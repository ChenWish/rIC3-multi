use crate::ic3::{
    IC3,
    mic::{DropVarParameter, MicType},
    multitf::MtBlockResult,
    proofoblig::ProofObligation,
};
use log::{debug, info, trace};
use logicrs::{LitOrdVec, LitVec, satif::Satif};
use std::time::Instant;

pub enum BlockResult {
    Success,
    Failure,
    Proved,
    LimitExceeded,
}

impl IC3 {
    pub(crate) fn push_lemma(&mut self, frame: usize, mut cube: LitVec) -> (usize, LitVec) {
        let start = Instant::now();
        for i in frame + 1..=self.level() {
            if self.solvers[i - 1].inductive(&cube, true) {
                cube = self.solvers[i - 1].inductive_core().unwrap_or(cube);
            } else {
                return (i, cube);
            }
        }
        self.statistic.block.push_time += start.elapsed();
        (self.level() + 1, cube)
    }

    fn generalize(&mut self, mut po: ProofObligation, mic_type: MicType) -> bool {
        let Some(mut mic) = self.solvers[po.frame - 1].inductive_core() else {
            po.frame += 1;
            self.add_obligation(po.clone());
            return self.add_lemma(po.frame - 1, po.lemma.cube().clone(), false, Some(po));
        };
        mic = self.mic(po.frame, mic, &[], mic_type);
        let (frame, mic) = self.push_lemma(po.frame, mic);
        self.statistic.avg_po_cube_len += po.lemma.len();
        po.push_to(frame);
        self.add_obligation(po.clone());
        if self.add_lemma(frame - 1, mic.clone(), false, Some(po)) {
            return true;
        }
        false
    }

    #[allow(unused)]
    fn block_with_restart(&mut self) -> BlockResult {
        let mut restart = 0;
        loop {
            let rest_base = luby(2.0, restart);
            match self.block(Some(rest_base * 100.0)) {
                BlockResult::LimitExceeded => {
                    let bt = if let Some(a) = self.obligations.peak() {
                        (a.frame + 2).min(self.level() - 1)
                    } else {
                        self.level() - 1
                    };
                    self.obligations.clear_to(bt);
                    restart += 1;
                    if restart % 10 == 0 {
                        info!("rIC3 restarted {restart} times");
                    }
                }
                r => return r,
            }
        }
    }

    pub fn block(&mut self, limit: Option<f64>) -> BlockResult {
        let mut noc = 0;
        let mut popped_any = false;
        let mut blocking_start = Instant::now();

        // Fixed expansion mode: expansion = min(level, fixed), active immediately
        if let Some(fixed) = self.cfg.ic3.multi_fixed {
            self.timeframe_expansion = fixed.min(self.level()).max(1);
        } else if self.mt_restart_pending {
            // Continuing a blocking phase interrupted by a dynamic-mode
            // restart: keep the escalated expansion for this call.
            self.mt_restart_pending = false;
        } else {
            self.timeframe_expansion = 1;
            self.mt_abs_mult = 1.0;
            self.mt_overshoot_phase_reset();
        }

        while let Some(mut po) = self.obligations.pop(self.level()) {
            popped_any = true;
            if po.removed {
                continue;
            }
            if let Some(limit) = limit
                && noc as f64 > limit
            {
                return BlockResult::LimitExceeded;
            }
            trace!(
                "blocking {} in frame {} with depth {}",
                po.lemma, po.frame, po.depth
            );
            if self.tsctx.cube_subsume_init(&po.lemma) {
                if self.cfg.ic3.abs_cst || self.cfg.ic3.abs_trans {
                    self.add_obligation(po.clone());
                    if self.check_witness_by_bmc(po.depth) {
                        return BlockResult::Failure;
                    } else {
                        self.obligations.clear();
                        for f in self.frame.iter_mut() {
                            for l in f.iter_mut() {
                                l.po = None;
                            }
                        }
                        continue;
                    }
                } else if po.frame > 0 {
                    // An init-intersecting obligation above frame 0 would be
                    // blocked ungated below (generalize's no-core branch),
                    // producing a lemma that excludes an initial state.
                    let lemma = po.lemma.cube();
                    assert!(!self.solvers[0].solve(lemma));
                } else {
                    self.add_obligation(po.clone());
                    return BlockResult::Failure;
                }
            }

            // Multi-timeframe restart check. Clearing the queue ends this
            // `block()` call; `check()` re-seeds the unblocked bad state via
            // `get_bad` and the next `block()` call continues with the
            // escalated expansion (`mt_restart_pending`).
            if self.is_time_to_restart(&blocking_start) {
                self.update_timeframe_expansion();
                self.obligations.clear();
                self.mt_restart_pending = true;
                blocking_start = Instant::now();
                continue;
            }

            if let Some((bf, _)) = self.frame.trivial_contained(Some(po.frame), &po.lemma) {
                if let Some(bf) = bf {
                    po.push_to(bf + 1);
                    self.add_obligation(po);
                }
                continue;
            }
            debug!("{}", self.frame.statistic(false));
            po.bump_act();
            if self.cfg.ic3.drop_po && po.act > 20.0 {
                continue;
            }

            // Check if we should use multi-timeframe blocking
            if self.cfg.ic3.multi_enabled()
                && po.frame == self.level()
                && self.timeframe_expansion > 1
            {
                let cube = po.lemma.cube().clone();
                let tf_exp = self.timeframe_expansion;
                let frame = po.frame;
                match self.mt_block(po.clone(), frame, &cube, tf_exp) {
                    MtBlockResult::Proved => {
                        debug!("fixpoint reached in multi-timeframe block");
                        return BlockResult::Proved;
                    }
                    MtBlockResult::Handled => continue,
                    // The mt path cannot soundly justify a lemma for this
                    // obligation; process it with the standard path below.
                    MtBlockResult::Fallback => {
                        debug!("multi-timeframe block fallback at frame {frame}");
                    }
                }
            }

            let blocked_start = Instant::now();
            let blocked = self.blocked_with_ordered(po.frame, &po.lemma, false);
            self.statistic.block.blocked_time += blocked_start.elapsed();
            if blocked {
                noc += 1;
                let mic_type = if self.cfg.ic3.dynamic {
                    if let Some(mut n) = po.next.as_mut() {
                        let mut act = n.act;
                        for _ in 0..2 {
                            if let Some(nn) = n.next.as_mut() {
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
                                let limit = ((act - EXCTG_THRESHOLD).powf(0.45) * 2.0 + 5.0).round()
                                    as usize;
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
                };
                if self.generalize(po, mic_type) {
                    return BlockResult::Proved;
                }
            } else {
                let (model, inputs) = self.get_pred(po.frame, true);
                self.add_obligation(ProofObligation::new(
                    po.frame - 1,
                    LitOrdVec::new(model),
                    inputs,
                    po.depth + 1,
                    Some(po.clone()),
                ));
                self.add_obligation(po);
            }
        }

        // Reset timeframe expansion after a completed blocking phase; keep it
        // when a dynamic-mode restart interrupted the phase (the continuation
        // happens in the next `block()` call).
        //
        // The median must only see real blocking episodes (abc_PDR-multi
        // parity): restart-interrupted exits and calls that popped no
        // obligation would otherwise record near-zero samples and drag the
        // median towards 0, degenerating the relative restart condition.
        if !self.mt_restart_pending {
            self.timeframe_expansion = 1;
            if popped_any {
                self.blocking_time_median.add(blocking_start.elapsed());
                self.statistic.mt.final_median = self.blocking_time_median.median();
                self.statistic.mt.median_samples = self.blocking_time_median.count();
            }
        }
        BlockResult::Success
    }

    #[allow(unused)]
    fn trivial_block_rec(
        &mut self,
        frame: usize,
        lemma: LitOrdVec,
        constraint: &[LitVec],
        limit: &mut usize,
        parameter: DropVarParameter,
    ) -> bool {
        if frame == 0 {
            return false;
        }
        if self.tsctx.cube_subsume_init(&lemma) {
            return false;
        }
        if *limit == 0 {
            return false;
        }
        *limit -= 1;
        loop {
            if self.blocked_with_ordered_with_constrain(
                frame,
                &lemma,
                false,
                true,
                constraint.to_vec(),
            ) {
                let mut mic = self.solvers[frame - 1].inductive_core().unwrap();
                mic = self.mic(frame, mic, constraint, MicType::DropVar(parameter));
                let (frame, mic) = self.push_lemma(frame, mic);
                self.add_lemma(frame - 1, mic, false, None);
                return true;
            } else {
                if *limit == 0 {
                    return false;
                }
                let model = LitOrdVec::new(self.get_pred(frame, false).0);
                if !self.trivial_block_rec(frame - 1, model, constraint, limit, parameter) {
                    return false;
                }
            }
        }
    }

    pub fn trivial_block(
        &mut self,
        frame: usize,
        lemma: LitOrdVec,
        constraint: &[LitVec],
        parameter: DropVarParameter,
    ) -> bool {
        let mut limit = parameter.limit;
        self.trivial_block_rec(frame, lemma, constraint, &mut limit, parameter)
    }
}

fn luby(y: f64, mut x: usize) -> f64 {
    let mut size = 1;
    let mut seq = 0;
    while size < x + 1 {
        seq += 1;
        size = 2 * size + 1
    }
    while size - 1 != x {
        size = (size - 1) >> 1;
        seq -= 1;
        x %= size;
    }
    y.powi(seq)
}
