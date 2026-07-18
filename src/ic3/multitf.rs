//! Multi-timeframe optimization for IC3.
//!
//! This module implements an optimization that unrolls the transition system
//! multiple timeframes to block proof obligations more efficiently.
//!
//! Key idea: Instead of checking blocking one step at a time, unroll k steps
//! and check if the cube can be blocked across all k timeframes simultaneously.

use super::{
    IC3,
    mic::{DropVarParameter, MicType},
    proofoblig::ProofObligation,
};
use crate::{
    gipsat::TransysSolver,
    transys::{TransysIf, unroll::TransysUnroll},
};
use giputils::{grc::Grc, hash::GHashSet};
use log::{debug, error};
use logicrs::{LitOrdVec, LitVec, Var, satif::Satif};
use std::{
    cmp::min,
    time::{Duration, Instant},
};

// ===========================================================================
// Multi-timeframe parameters.
//
// Every parameter can be overridden through the RIC3_MT_* environment
// variable named on its field. Parsing happens once at first use; the
// resolved values are printed once, and an unset or out-of-range value
// silently falls back to its default.
// ===========================================================================

/// Runtime multi-timeframe parameters, each overridable via the RIC3_MT_*
/// environment variable named on its field.
struct MtParams {
    /// RIC3_MT_MIN_LEVEL (default 4): mt intervenes only once the proof has
    /// reached this level. Triggering at shallow levels only confiscates the
    /// obligation queue without buying depth.
    min_level: usize,
    /// RIC3_MT_ABS_THRESHOLD_MS (default 10_000): absolute "stuck" threshold —
    /// a single blocking query running longer than this (scaled by the
    /// abs_expand_factor per escalation) may trigger a restart + escalation.
    abs_threshold: Duration,
    /// RIC3_MT_MEDIAN_FACTOR (default 2): second stuck condition — the query
    /// must also exceed the median blocking time times this factor. Protects
    /// cases whose median is tens of seconds from being misjudged as stuck.
    median_factor: u32,
    /// RIC3_MT_ABS_EXPAND_FACTOR (default 2.0): each escalation also
    /// multiplies the absolute threshold (10s -> 20s -> 40s); queries over
    /// larger expansions legitimately take longer. Reset per blocking phase.
    abs_expand_factor: f64,
    /// RIC3_MT_EXP_RATIO (default 0.25, range [0,1]): ceiling ramp start —
    /// at t=0 the expansion ceiling is ratio * level. 0.0 is legal and
    /// meaningful (ceiling 1 = pure-PDR opening); do not "validate" it away.
    ratio_start: f64,
    /// RIC3_MT_RATIO_MAX (default 0.75, range [start,1]): ceiling ramp end.
    /// Values < 1.0 rule out the exp == level regime where the mt query
    /// degenerates into BMC.
    ratio_max: f64,
    /// RIC3_MT_RATIO_RAMP_SEC (default 2400): the ceiling relaxes linearly
    /// from start to max over this many seconds, then holds.
    ratio_ramp_sec: f64,
    /// RIC3_MT_EXP_OVERSHOOT (default 2): earned depth — an obligation
    /// repeatedly pressing against the ceiling may double it, at most this
    /// many times. The allowance is scoped to the level (same-level
    /// obligations share it; reset when the level advances).
    overshoot_max: usize,
    /// RIC3_MT_EXP_CAP (default off): absolute expansion bound over the ramp
    /// ceiling and earned overshoot alike. Insurance against memory blow-up:
    /// deep-level monster expansions burn the whole time budget in a single
    /// solve.
    exp_cap: Option<usize>,
    /// RIC3_MT_LOG (default off, enable with any nonzero integer): print one
    /// line per SelectDepth event (breakthrough, restart) in the format
    /// `TimeStamp = <seconds since run start, 2 decimals> : <event>`.
    log: bool,
}

fn mt_env<T: std::str::FromStr>(name: &str) -> Option<T> {
    std::env::var(name).ok().and_then(|v| v.parse().ok())
}

fn mt_params() -> &'static MtParams {
    static PARAMS: std::sync::OnceLock<MtParams> = std::sync::OnceLock::new();
    PARAMS.get_or_init(|| {
        let ratio_start = mt_env::<f64>("RIC3_MT_EXP_RATIO")
            .filter(|r| (0.0..=1.0).contains(r))
            .unwrap_or(0.25);
        let p = MtParams {
            min_level: mt_env("RIC3_MT_MIN_LEVEL").unwrap_or(4),
            abs_threshold: Duration::from_millis(
                mt_env("RIC3_MT_ABS_THRESHOLD_MS").unwrap_or(10_000),
            ),
            median_factor: mt_env("RIC3_MT_MEDIAN_FACTOR").unwrap_or(2),
            abs_expand_factor: mt_env::<f64>("RIC3_MT_ABS_EXPAND_FACTOR")
                .filter(|f| *f > 0.0)
                .unwrap_or(2.0),
            ratio_start,
            // the end may not undercut the start; with only EXP_RATIO set the
            // default end still keeps the ramp monotone
            ratio_max: mt_env::<f64>("RIC3_MT_RATIO_MAX")
                .filter(|m| (ratio_start..=1.0).contains(m))
                .unwrap_or_else(|| ratio_start.max(0.75)),
            ratio_ramp_sec: mt_env::<f64>("RIC3_MT_RATIO_RAMP_SEC")
                .filter(|t| *t > 0.0)
                .unwrap_or(2400.0),
            overshoot_max: mt_env("RIC3_MT_EXP_OVERSHOOT").unwrap_or(2),
            exp_cap: mt_env("RIC3_MT_EXP_CAP"),
            log: mt_env::<i64>("RIC3_MT_LOG").map(|v| v != 0).unwrap_or(false),
        };
        // Print the resolved parameters once, in the shared cross-tool
        // format (env names without the tool prefix).
        println!(
            "MT params: MT_MIN_LEVEL={} MT_ABS_THRESHOLD_MS={} MT_MEDIAN_FACTOR={} MT_ABS_EXPAND_FACTOR={} MT_EXP_RATIO={} MT_RATIO_MAX={} MT_RATIO_RAMP_SEC={} MT_EXP_OVERSHOOT={} MT_EXP_CAP={} MT_LOG={}",
            p.min_level,
            p.abs_threshold.as_millis(),
            p.median_factor,
            p.abs_expand_factor,
            p.ratio_start,
            p.ratio_max,
            p.ratio_ramp_sec,
            p.overshoot_max,
            p.exp_cap.map_or_else(|| "off".to_string(), |c| c.to_string()),
            if p.log { "on" } else { "off" }
        );
        p
    })
}

/// Outcome of a multi-timeframe blocking attempt.
pub(super) enum MtBlockResult {
    /// Obligation handled (lemma added or deeper obligation queued).
    Handled,
    /// Fixpoint reached while adding the lemma.
    Proved,
    /// The multi-timeframe path cannot soundly justify a lemma for this
    /// obligation; the caller must process it with the standard 1-step path.
    Fallback,
}

impl IC3 {
    /// Hard(f): the immovable expansion bound — the level and optionally
    /// RIC3_MT_EXP_CAP. Neither the ramp nor an earned overshoot can pass
    /// it; when the ceiling sits on it, `is_time_to_restart` commits instead
    /// of spending overshoot (a doubling would buy nothing).
    #[inline]
    fn mt_hard_cap(&self) -> usize {
        let mut hard = self.level();
        if let Some(cap) = mt_params().exp_cap {
            hard = min(hard, cap);
        }
        hard.max(1)
    }

    /// Ceil(f): the deterministic time ramp (ratio_start -> ratio_max times
    /// the current level over ratio_ramp_sec), doubled per earned overshoot
    /// step (granted in `is_time_to_restart` when a PO keeps pressing
    /// against the ceiling), clamped by `mt_hard_cap`.
    #[inline]
    fn max_timeframe_expansion(&self) -> usize {
        let p = mt_params();
        let t = self.mt_solver_start.elapsed().as_secs_f64();
        let ratio =
            p.ratio_start + (p.ratio_max - p.ratio_start) * (t / p.ratio_ramp_sec).min(1.0);
        let base = ((ratio * self.level() as f64).ceil() as usize).max(1);
        min(self.mt_hard_cap(), base << self.mt_overshoot_used)
    }

    /// Phase-start bookkeeping for the overshoot counter: the allowance is
    /// scoped to the level (subsequent POs at the same level inherit the
    /// raised *ceiling*, never the expansion — each PO still starts at 1 and
    /// only escalates if itself difficult), so retry-heavy levels (elevator:
    /// dozens of expensive POs) pay the earning wait once instead of per PO.
    /// Reset when the level advances.
    pub(crate) fn mt_overshoot_phase_reset(&mut self) {
        if self.mt_overshoot_level == self.level() {
            return; // keep earned allowance for this level
        }
        self.mt_overshoot_used = 0;
        self.mt_overshoot_level = usize::MAX;
    }

    /// Deepen (Algorithm 3): double the timeframe expansion (capped at the
    /// ceiling, recomputed with any overshoot just granted) and scale the
    /// abs threshold along with it (`abs_effective = abs_threshold *
    /// abs_expand_factor^(escalations at this proof-obligation)`).
    pub(crate) fn update_timeframe_expansion(&mut self) {
        self.timeframe_expansion =
            min(self.timeframe_expansion * 2, self.max_timeframe_expansion());
        self.mt_abs_mult *= mt_params().abs_expand_factor;
        if mt_params().log {
            println!(
                "TimeStamp = {:.2} : restarting with expansion = {}",
                self.mt_solver_start.elapsed().as_secs_f64(),
                self.timeframe_expansion
            );
        }
    }

    /// Check if it's time to restart with a larger timeframe expansion
    /// (Algorithm 3, SelectDepth). Returns true when the caller must clear
    /// the queue and continue at the escalated expansion; the deepen itself
    /// (`min(2l, ceiling)`, plus the abs-budget doubling) happens in
    /// `update_timeframe_expansion`.
    ///
    /// Condition order mirrors the pseudocode:
    /// 1. Gates: dynamic mode, multi-timeframe enabled, level >= min_level.
    /// 2. Easy — no expansion needed: elapsed time must exceed the absolute
    ///    threshold (abs_threshold, scaled by abs_expand_factor per
    ///    escalation) AND median_factor x the median blocking time (an empty
    ///    median counts as exceeded).
    /// 3. At the ceiling: a pressing obligation may earn up to overshoot_max
    ///    ceiling doublings, but only while a doubling actually buys room
    ///    (ceiling < hard cap); otherwise commit, keeping the capped
    ///    expansion. Hence a restart always strictly deepens, and the
    ///    deepened expansion is always >= 2 — for every config.
    pub(crate) fn is_time_to_restart(&mut self, start: &Instant) -> bool {
        // Fixed expansion mode: expansion is set once per blocking phase, never restart
        if self.cfg.ic3.multi_fixed.is_some() {
            return false;
        }
        if !self.cfg.ic3.multi_timeframe {
            return false;
        }
        let p = mt_params();
        if self.level() < p.min_level {
            return false;
        }

        // Easy: no expansion needed. Relatively difficult: current
        // duration exceeds median_factor x the median; no samples yet counts
        // as difficult, so early phases are gated by the absolute threshold
        // alone.
        let current_duration = start.elapsed();
        let abs_threshold = p.abs_threshold.mul_f64(self.mt_abs_mult);
        let median = self.blocking_time_median.median();
        let relatively_difficult =
            median.is_none_or(|median| current_duration > median * p.median_factor);
        let absolutely_difficult = current_duration > abs_threshold;

        self.statistic.mt.restart_checks += 1;
        match (absolutely_difficult, relatively_difficult) {
            (true, false) => self.statistic.mt.abs_only += 1,
            (false, true) => self.statistic.mt.rel_only += 1,
            _ => (),
        }

        if !(absolutely_difficult && relatively_difficult) {
            return false;
        }

        // At the ceiling: breakthrough or commit. Invariant: expansion <=
        // ceiling — the expansion is only ever assigned min(.., ceiling),
        // and the ceiling is non-decreasing while the expansion persists
        // (ramp up, overshoot up, level fixed) — hence the equality test.
        let ceiling = self.max_timeframe_expansion();
        debug_assert!(self.timeframe_expansion <= ceiling);
        if self.timeframe_expansion == ceiling {
            if self.mt_overshoot_used >= p.overshoot_max || ceiling == self.mt_hard_cap() {
                // Out of breakthroughs, or the wall is immovable (hard cap:
                // a doubling would buy nothing): commit — keep blocking
                // multi-frame at the capped expansion.
                return false;
            }
            // Breakthrough: ceiling < hard cap, so the earned doubling
            // strictly raises it and the caller's deepen strictly deepens.
            self.mt_overshoot_used += 1;
            self.mt_overshoot_level = self.level();
            if p.log {
                println!(
                    "TimeStamp = {:.2} : update b from {} to {}",
                    self.mt_solver_start.elapsed().as_secs_f64(),
                    self.mt_overshoot_used - 1,
                    self.mt_overshoot_used
                );
            }
        }

        // Deepen and restart the attempt (in the caller, which emits the
        // restart log once the new expansion is known).
        self.statistic.mt.num_restart += 1;
        true
    }

    /// Initialize the multi-timeframe solver with the given timeframe expansion.
    ///
    /// This creates a new unrolled transition system and solver for the given
    /// number of timeframes.
    pub(super) fn mt_init_solver(&mut self, frame: usize, timeframe_expansion: usize) {
        assert!(timeframe_expansion >= 1);
        assert!(timeframe_expansion <= frame);
        let init_start = Instant::now();

        // Create new unrolled transition system
        self.mt_unroll = TransysUnroll::new(&self.mt_origin_ts);
        if timeframe_expansion > 1 {
            self.mt_unroll.unroll_to(timeframe_expansion - 1);
        }
        self.mt_tsctx = Grc::new(self.mt_unroll.compile().ctx());
        self.mt_solver = TransysSolver::new(&self.mt_tsctx, true);
        self.mt_lift = TransysSolver::new(&self.mt_tsctx, false);
        self.timeframe_expansion = timeframe_expansion;

        // Add constraints from existing frames to the multi-timeframe solver
        let start_frame = frame.saturating_sub(timeframe_expansion);
        for i in start_frame..self.frame.len() {
            for frame_lemma in self.frame[i].iter() {
                for f in start_frame..frame {
                    if f <= i {
                        let lift_num = f - start_frame;
                        let lifted_cube = self.mt_get_lemma_at_frame(frame_lemma.cube(), lift_num);
                        let clause: LitVec = lifted_cube.iter().map(|l| !*l).collect();
                        self.mt_solver.add_clause(&clause);
                    } else {
                        break;
                    }
                }
            }
        }

        // Add initial state constraint if start_frame is 0
        if start_frame == 0 {
            debug!("adding initial state constraint for multi-timeframe solver");
            for init_clause in self.tsctx.init.clone() {
                self.mt_solver.add_clause(&init_clause);
            }
        }
        self.statistic.mt.mt_init_time += init_start.elapsed();
    }

    /// Lift a lemma (cube) to a specific timeframe.
    fn mt_get_lemma_at_frame(&self, cube: &[logicrs::Lit], lift_num: usize) -> LitVec {
        assert!(lift_num <= self.mt_unroll.num_unroll);
        self.mt_unroll.lits_next(&LitVec::from(cube), lift_num)
    }

    /// Check if a cube is blocked in the multi-timeframe context.
    fn mt_blocked_with_ordered(&mut self, cube: &LitVec, strengthen: bool) -> bool {
        let mut ordered_cube = cube.clone();
        self.activity.sort_by_activity(&mut ordered_cube, false);
        self.mt_solver.inductive(&ordered_cube, strengthen)
    }

    /// Check if a cube is blocked with additional constraints.
    fn mt_blocked_with_ordered_constrain(
        &mut self,
        cube: &LitVec,
        strengthen: bool,
        constraint: Vec<LitVec>,
    ) -> bool {
        let mut ordered_cube = cube.clone();
        self.activity.sort_by_activity(&mut ordered_cube, false);
        self.mt_solver
            .inductive_with_constrain(&ordered_cube, strengthen, constraint)
    }

    /// Get predecessor state across multiple timeframes.
    ///
    /// Returns (latch_values, inputs_per_timeframe, intermediate_states),
    /// where intermediate_states[j-1] is the state at timeframe j
    /// (1 <= j <= timeframe_expansion - 1) in frame-0 variable space, used to
    /// reconstruct the counterexample as a chain of 1-step links.
    pub(super) fn mt_get_pred(&mut self, strengthen: bool) -> (LitVec, Vec<LitVec>, Vec<LitVec>) {
        let mut cls: LitVec = self.mt_solver.get_assump().clone();
        cls.extend_from_slice(&self.mt_tsctx.constraint);
        if cls.is_empty() {
            return (LitVec::new(), vec![], vec![]);
        }

        let in_cls: GHashSet<Var> = GHashSet::from_iter(cls.iter().map(|l| l.var()));
        let cls = !cls;

        // States at intermediate timeframes, extracted while the model is
        // untouched (before any flip_to_none / lift minimization).
        let mut mid_states = Vec::with_capacity(self.timeframe_expansion.saturating_sub(1));
        for j in 1..self.timeframe_expansion {
            let mut st = LitVec::new();
            for latch in self.tsctx.latch.iter() {
                let lit_j = self.mt_unroll.lit_next(latch.lit(), j);
                if let Some(v) = self.mt_solver.sat_value(lit_j) {
                    st.push(latch.lit().not_if(!v));
                }
            }
            mid_states.push(st);
        }

        // Collect inputs for each timeframe
        let mut inputs = vec![LitVec::default(); self.timeframe_expansion];
        let mut inputs_flat = LitVec::new();
        let num_input = self.tsctx.input.len();

        for (index, input) in self.mt_tsctx.input.iter().enumerate() {
            let lit = input.lit();
            if let Some(v) = self.mt_solver.sat_value(lit) {
                let timeframe = index / num_input;
                let index_in_timeframe = index % num_input;
                if timeframe < self.timeframe_expansion && index_in_timeframe < num_input {
                    let lit_in_frame_0 = self.tsctx.input[index_in_timeframe].lit();
                    inputs[timeframe].push(lit_in_frame_0.not_if(!v));
                }
                inputs_flat.push(lit.not_if(!v));
            }
        }

        // Get latch values with lifting
        self.mt_lift.set_domain(cls.iter().cloned());
        let mut latchs = LitVec::new();
        for latch in self.mt_tsctx.latch.iter() {
            let lit = latch.lit();
            if self.mt_lift.domain_has(lit.var()) {
                if let Some(v) = self.mt_solver.sat_value(lit) {
                    if in_cls.contains(latch) || !self.mt_solver.flip_to_none(*latch) {
                        latchs.push(lit.not_if(!v));
                    }
                }
            }
        }

        // Minimize predecessor using lift solver
        for _ in 0.. {
            if latchs.is_empty() {
                break;
            }
            latchs.shuffle(&mut self.rng);
            let olen = latchs.len();
            if let Some(n) = self.mt_lift.dcs.minimal_premise(&inputs_flat, &latchs, &cls) {
                latchs = n;
            } else {
                // The returned cube must guarantee the k-step path to the
                // target; silently keeping an unlifted cube here would drop
                // that guarantee and produce spurious obligations.
                error!("mt lift minimal_premise failed, please report this bug");
                panic!();
            }
            if latchs.len() == olen || !strengthen {
                break;
            }
        }
        self.mt_lift.unset_domain();

        (latchs, inputs, mid_states)
    }

    /// Main multi-timeframe blocking logic.
    pub(super) fn mt_block(
        &mut self,
        po: ProofObligation,
        frame: usize,
        cube: &LitVec,
        timeframe_expansion: usize,
    ) -> MtBlockResult {
        assert!(timeframe_expansion <= frame);

        let mt_start = Instant::now();
        *self
            .statistic
            .mt
            .mt_block_by_expansion
            .entry(timeframe_expansion)
            .or_default() += 1;

        self.mt_init_solver(frame, timeframe_expansion);

        let blocked = self.mt_blocked_with_ordered(cube, true);

        let result = if blocked {
            debug!("UNSAT in multi-timeframe block at frame {frame}");
            let mic_type = self.get_mic_type(&po);
            self.mt_generalize(po, mic_type, timeframe_expansion)
        } else {
            debug!("SAT in multi-timeframe block at frame {frame}");
            let (model, mut inputs, mid_states) = self.mt_get_pred(true);
            inputs.resize(timeframe_expansion, LitVec::default());
            // Link the deep predecessor to `po` through one obligation per
            // timeframe so the counterexample stays a chain of 1-step links
            // (each link's input drives the transition from its state to the
            // next link's state). Only the deep predecessor enters the queue;
            // the intermediate links exist for witness reconstruction.
            let mut next = po.clone();
            for j in (1..timeframe_expansion).rev() {
                next = ProofObligation::new(
                    po.frame - timeframe_expansion + j,
                    LitOrdVec::new(mid_states.get(j - 1).cloned().unwrap_or_default()),
                    inputs[j].clone(),
                    po.depth + (timeframe_expansion - j),
                    Some(next),
                );
            }
            self.add_obligation(ProofObligation::new(
                po.frame - timeframe_expansion,
                LitOrdVec::new(model),
                inputs[0].clone(),
                po.depth + timeframe_expansion,
                Some(next),
            ));
            self.add_obligation(po);
            MtBlockResult::Handled
        };
        self.statistic.mt.mt_block_time += mt_start.elapsed();
        result
    }

    /// Get the MIC type based on proof obligation activity.
    fn get_mic_type(&self, po: &ProofObligation) -> MicType {
        if self.cfg.ic3.dynamic {
            if let Some(mut n) = po.next.as_ref() {
                let mut act = n.act;
                for _ in 0..2 {
                    if let Some(nn) = n.next.as_ref() {
                        n = nn;
                        act = act.max(n.act);
                    } else {
                        break;
                    }
                }
                const CTG_THRESHOLD: f64 = 10.0;
                const EXCTG_THRESHOLD: f64 = 40.0;
                let (limit, max, level) = match act {
                    EXCTG_THRESHOLD.. => {
                        let limit =
                            ((act - EXCTG_THRESHOLD).powf(0.45) * 2.0 + 5.0).round() as usize;
                        (limit, 5, 1)
                    }
                    CTG_THRESHOLD..EXCTG_THRESHOLD => {
                        let max = (act - CTG_THRESHOLD) as usize / 10 + 2;
                        (1, max, 1)
                    }
                    ..CTG_THRESHOLD => (0, 0, 0),
                    _ => panic!(),
                };
                let p = DropVarParameter::new(limit, max, level);
                MicType::DropVar(p)
            } else {
                MicType::DropVar(Default::default())
            }
        } else {
            MicType::from_config(&self.cfg)
        }
    }

    /// Generalize a lemma in multi-timeframe context.
    ///
    /// The k-step (exact `timeframe_expansion`-step) UNSAT result alone cannot
    /// justify a lemma: it neither covers states reachable in fewer than k
    /// steps, nor establishes the 1-step relative induction that rIC3's
    /// propagation/fixpoint argument relies on. Soundness here comes from two
    /// extra obligations (mirroring abc_PDR-multi's `ManRecRefine` + union):
    /// short horizons are covered by `mt_rec_refine`, and the final cube must
    /// pass a standard 1-step relative-induction gate before entering frame f.
    /// If either fails, the obligation falls back to the standard path.
    fn mt_generalize(
        &mut self,
        mut po: ProofObligation,
        mic_type: MicType,
        timeframe_expansion: usize,
    ) -> MtBlockResult {
        // Get inductive core from multi-timeframe solver
        let Some(mut mic) = self.mt_solver.inductive_core() else {
            self.statistic.mt.fb_no_core += 1;
            return MtBlockResult::Fallback;
        };

        // Apply MIC minimization on the unrolled solver
        mic = self.mt_mic(mic, &[], mic_type);

        // Short-horizon refinement (ABC: ManRecRefine). None means the
        // obligation state could not be blocked within the short horizon,
        // i.e. it may be genuinely reachable there.
        let drop_var_param = self.get_drop_var_parameter(&po);
        let Some(unsat_core_tf1) =
            self.mt_rec_refine(timeframe_expansion - 1, &po.lemma, drop_var_param)
        else {
            self.statistic.mt.fb_rec_refine += 1;
            return MtBlockResult::Fallback;
        };

        // Combine MIC and recursive refinement result
        let blocking_cube = self.mt_get_blocking_cube(&mic, &unsat_core_tf1);

        // Soundness gate: 1-step relative induction against F_{f-1}.
        let blocking_lemma = LitOrdVec::new(blocking_cube);
        if !self.blocked_with_ordered(po.frame, &blocking_lemma, true) {
            debug!(
                "multi-timeframe lemma rejected by 1-step gate at frame {}",
                po.frame
            );
            self.statistic.mt.fb_gate_reject += 1;
            return MtBlockResult::Fallback;
        }
        let core = self.solvers[po.frame - 1]
            .inductive_core()
            .unwrap_or_else(|| blocking_lemma.cube().clone());
        let (frame, core) = self.push_lemma(po.frame, core);

        po.push_to(frame);
        self.add_obligation(po.clone());
        self.statistic.mt.mt_lemma_added += 1;
        if self.mt_add_lemma(frame - 1, core, true, Some(po)) {
            MtBlockResult::Proved
        } else {
            MtBlockResult::Handled
        }
    }

    /// Get drop var parameter based on proof obligation.
    fn get_drop_var_parameter(&self, po: &ProofObligation) -> DropVarParameter {
        if self.cfg.ic3.dynamic {
            if let Some(mut n) = po.next.as_ref() {
                let mut act = n.act;
                for _ in 0..2 {
                    if let Some(nn) = n.next.as_ref() {
                        n = nn;
                        act = act.max(n.act);
                    } else {
                        break;
                    }
                }
                const CTG_THRESHOLD: f64 = 10.0;
                const EXCTG_THRESHOLD: f64 = 40.0;
                let (limit, max, level) = match act {
                    EXCTG_THRESHOLD.. => {
                        let limit =
                            ((act - EXCTG_THRESHOLD).powf(0.3) * 2.0 + 5.0).round() as usize;
                        (limit, 5, 1)
                    }
                    CTG_THRESHOLD..EXCTG_THRESHOLD => {
                        let max = (act - CTG_THRESHOLD) as usize / 10 + 2;
                        (1, max, 1)
                    }
                    ..CTG_THRESHOLD => (0, 0, 0),
                    _ => panic!(),
                };
                DropVarParameter::new(limit, max, level)
            } else {
                DropVarParameter::default()
            }
        } else {
            DropVarParameter::default()
        }
    }

    /// Recursive refinement for multi-timeframe (ABC: `ManRecRefine`).
    ///
    /// Blocks `lemma` at the short horizon `frame` (= timeframe_expansion - 1)
    /// with standard 1-step recursive blocking, so that states reachable in
    /// fewer than `timeframe_expansion` steps — invisible to the exact-k
    /// query — are covered by the returned cube.
    ///
    /// Returns `None` when the lemma cannot be refuted within the horizon
    /// (its predecessor chain reaches the initial states). The caller must
    /// then abort multi-timeframe blocking: adding the k-step lemma alone
    /// would be unsound (this mirrors ABC returning NULL and reporting a
    /// counterexample instead of blocking).
    fn mt_rec_refine(
        &mut self,
        frame: usize,
        lemma: &LitOrdVec,
        parameter: DropVarParameter,
    ) -> Option<LitVec> {
        if frame == 0 {
            return None;
        }
        if self.tsctx.cube_subsume_init(lemma) {
            return None;
        }

        loop {
            if self.blocked_with_ordered(frame, lemma, false) {
                let mut mic = self.solvers[frame - 1]
                    .inductive_core()
                    .unwrap_or_else(|| lemma.cube().clone());
                mic = self.mic(frame, mic, &[], MicType::DropVar(parameter));
                let (push_frame, mic) = self.push_lemma(frame, mic);
                self.add_lemma(push_frame - 1, mic.clone(), false, None);
                return Some(mic);
            } else {
                let model = LitOrdVec::new(self.get_pred(frame, false).0);
                if self.tsctx.cube_subsume_init(&model) {
                    return None;
                }
                self.mt_rec_refine(frame - 1, &model, parameter)?;
            }
        }
    }

    /// Combine MIC and recursive refinement results into a blocking cube.
    fn mt_get_blocking_cube(&self, mic: &LitVec, unsat_core_tf1: &LitVec) -> LitVec {
        let mut result = LitVec::new();
        let mut lit_set = std::collections::BTreeSet::new();

        // Add all literals from mic
        for &lit in mic.iter() {
            lit_set.insert(lit);
            result.push(lit);
        }

        // Add literals from unsat_core_tf1 that don't conflict
        for &lit in unsat_core_tf1.iter() {
            debug_assert!(
                !lit_set.contains(&!lit),
                "Conflicting literals found: {:?} and {:?}",
                !lit,
                lit
            );
            if lit_set.insert(lit) {
                result.push(lit);
            }
        }
        result
    }

    /// Add a lemma considering multi-timeframe context.
    ///
    /// Returns true if fixpoint (invariant) is found.
    fn mt_add_lemma(
        &mut self,
        frame: usize,
        lemma: LitVec,
        contained_check: bool,
        po: Option<ProofObligation>,
    ) -> bool {
        // Delegate to the standard add_lemma
        self.add_lemma(frame, lemma, contained_check, po)
    }

    /// Multi-timeframe MIC (Minimal Inductive Core).
    ///
    /// Cube-shrinking only, no CTG: a lemma derived inside the k-step
    /// generalization would enter the frames without the 1-step consecution
    /// that frame clauses require (the mt candidate justifying it may never
    /// be added), so no clause may be added from here.
    fn mt_mic(&mut self, cube: LitVec, constraint: &[LitVec], mic_type: MicType) -> LitVec {
        match mic_type {
            MicType::NoMic => cube,
            MicType::DropVar(_) => self.mt_mic_by_drop_var(cube, constraint),
        }
    }

    /// Multi-timeframe MIC by drop variable method.
    fn mt_mic_by_drop_var(&mut self, mut cube: LitVec, constraint: &[LitVec]) -> LitVec {
        self.statistic.avg_mic_cube_len += cube.len();
        self.statistic.num_mic += 1;

        self.mt_solver.set_domain(
            self.mt_tsctx
                .lits_next(&cube)
                .iter()
                .copied()
                .chain(cube.iter().copied()),
        );

        let mut keep = GHashSet::new();
        let mut i = 0;
        self.activity.sort_by_activity(&mut cube, true);

        while i < cube.len() {
            if keep.contains(&cube[i]) {
                i += 1;
                continue;
            }

            let mut removed_cube = cube.clone();
            removed_cube.remove(i);

            if let Some(new_cube) = self.mt_down(&removed_cube, &keep, constraint) {
                self.statistic.mic_drop.success();
                cube = new_cube;
                // Re-sort after modification
                self.activity.sort_by_activity(&mut cube, true);
                i = 0;
                self.mt_solver.unset_domain();
                self.mt_solver.set_domain(
                    self.mt_tsctx
                        .lits_next(&cube)
                        .iter()
                        .copied()
                        .chain(cube.iter().copied()),
                );
            } else {
                self.statistic.mic_drop.fail();
                keep.insert(cube[i]);
                i += 1;
            }
        }

        self.mt_solver.unset_domain();

        self.activity.bump_cube_activity(&cube);
        cube
    }

    /// Downward refinement for multi-timeframe MIC.
    fn mt_down(
        &mut self,
        cube: &LitVec,
        keep: &GHashSet<logicrs::Lit>,
        constraint: &[LitVec],
    ) -> Option<LitVec> {
        let mut cube = cube.clone();
        self.statistic.num_down += 1;

        loop {
            if self.tsctx.cube_subsume_init(&cube) {
                return None;
            }
            self.statistic.num_down_sat += 1;

            if self.mt_blocked_with_ordered_constrain(&cube, true, constraint.to_vec()) {
                return self.mt_solver.inductive_core();
            }

            // Get values from solver and filter
            let mut cube_new = LitVec::new();
            for lit in cube {
                if keep.contains(&lit) {
                    if self.mt_solver.sat_value(lit).is_some_and(|v| v) {
                        cube_new.push(lit);
                    } else {
                        return None;
                    }
                } else if self.mt_solver.sat_value(lit).is_some_and(|v| v)
                    && !self.mt_solver.flip_to_none(lit.var())
                {
                    cube_new.push(lit);
                }
            }
            cube = cube_new;
        }
    }

}

// Extension trait for LitVec to add shuffle
trait ShuffleLitVec {
    fn shuffle(&mut self, rng: &mut rand::rngs::StdRng);
}

impl ShuffleLitVec for LitVec {
    fn shuffle(&mut self, rng: &mut rand::rngs::StdRng) {
        use rand::seq::SliceRandom;
        self.as_mut_slice().shuffle(rng);
    }
}

