use crate::{
    Engine, Proof, Witness,
    config::Config,
    gipsat::{SolverStatistic, TransysSolver},
    ic3::{block::BlockResult, localabs::LocalAbs},
    transys::{Transys, TransysCtx, TransysIf, certify::Restore, unroll::TransysUnroll},
};
use activity::Activity;
use frame::{Frame, Frames};
use giputils::{grc::Grc, logger::IntervalLogger};
use log::{Level, debug, info, trace};
use logicrs::{Lit, LitOrdVec, LitVec, LitVvec, Var, satif::Satif};
use proofoblig::{ProofObligation, ProofObligationQueue};
use rand::{Rng, SeedableRng, rngs::StdRng};
use statistic::Statistic;
use std::time::Instant;

mod activity;
mod aux;
mod block;
mod frame;
mod localabs;
mod mic;
mod multitf;
mod percentile;
mod proofoblig;
mod propagate;
mod solver;
mod statistic;
mod verify;

use percentile::BoundedMedianCalculator;

pub struct IC3 {
    cfg: Config,
    ts: Transys,
    tsctx: Grc<TransysCtx>,
    solvers: Vec<TransysSolver>,
    inf_solver: TransysSolver,
    lift: TransysSolver,
    frame: Frames,
    obligations: ProofObligationQueue,
    /// Solver construction time; drives the ceiling ramp (RIC3_MT_RATIO_RAMP_SEC).
    mt_solver_start: Instant,
    activity: Activity,
    statistic: Statistic,
    localabs: LocalAbs,
    ots: Transys,
    rst: Restore,
    auxiliary_var: Vec<Var>,
    rng: StdRng,

    filog: IntervalLogger,

    // Multi-timeframe optimization fields
    /// Original transition system with !bad as constraint (for multi-timeframe unrolling)
    mt_origin_ts: Transys,
    /// Unrolled transition system for multi-timeframe
    mt_unroll: TransysUnroll<Transys>,
    /// Context for multi-timeframe solver
    mt_tsctx: Grc<TransysCtx>,
    /// Solver for multi-timeframe blocking queries
    mt_solver: TransysSolver,
    /// Lift solver for multi-timeframe predecessor extraction
    mt_lift: TransysSolver,
    /// Current timeframe expansion factor (starts at 1, doubles on restart)
    timeframe_expansion: usize,
    /// abs-threshold multiplier scaled with expansion within a blocking phase
    /// (RIC3_MT_ABS_EXPAND_FACTOR): reset to 1.0 when `timeframe_expansion` resets
    /// to 1, multiplied by the factor on each escalation. Gives larger
    /// expansions proportionally more time before the next restart fires.
    mt_abs_mult: f64,
    /// Earned ceiling doublings (up to RIC3_MT_EXP_OVERSHOOT): incremented when
    /// the trigger keeps firing at the ceiling, reset alongside
    /// `timeframe_expansion`/`mt_abs_mult`.
    mt_overshoot_used: usize,
    /// Level at which the current overshoot allowance was earned (usize::MAX
    /// when none). The allowance survives phase resets while the level is
    /// unchanged.
    mt_overshoot_level: usize,
    /// A dynamic-mode restart cleared the obligation queue; the next `block()`
    /// call continues the same blocking phase and must keep the escalated
    /// `timeframe_expansion` (mirrors ABC re-seeding the original cube with
    /// the doubled expansion inside the same BlockCube call).
    mt_restart_pending: bool,
    /// Median calculator for blocking time (tracks execution time of blocking queries)
    blocking_time_median: BoundedMedianCalculator,
}

impl IC3 {
    #[inline]
    pub fn level(&self) -> usize {
        self.solvers.len() - 1
    }

    fn extend(&mut self) {
        let nl = self.solvers.len();
        debug!("extending IC3 to level {nl}");
        let solver = self.inf_solver.clone();
        self.solvers.push(solver);
        self.frame.push(Frame::new());
        if self.level() == 0 {
            for init in self.tsctx.init.clone() {
                self.add_lemma(0, !init, true, None);
            }
            let mut init = LitVec::new();
            for l in self.tsctx.latch.iter() {
                if self.tsctx.init_map[*l].is_none()
                    && let Some(v) = self.solvers[0].sat_value(l.lit())
                {
                    let l = l.lit().not_if(!v);
                    init.push(l);
                }
            }
            for i in init {
                self.ts.add_init(i.var(), Lit::constant(i.polarity()));
                self.tsctx.add_init(i.var(), Lit::constant(i.polarity()));
            }
        }

    }

    fn base(&mut self) -> bool {
        self.extend();
        assert!(self.level() == 0);
        true
    }
}

impl IC3 {
    pub fn new(cfg: Config, ts: Transys) -> Self {
        let ots = ts.clone();
        let rst = Restore::new(&ts);
        let mut rng = StdRng::seed_from_u64(cfg.rseed);
        let statistic = Statistic::default();
        let (mut ts, mut rst) = ts.preproc(&cfg.preproc, rst);
        let mut uts = TransysUnroll::new(&ts);
        uts.unroll();
        if cfg.ic3.inn {
            ts = uts.interal_signals();
        }
        ts.remove_gate_init(&mut rst);
        let tsctx = Grc::new(ts.ctx());
        let activity = Activity::new(&tsctx);
        let frame = Frames::new(&tsctx);
        let mut inf_solver = TransysSolver::new(&tsctx, true);
        inf_solver.dcs.set_rseed(rng.random());
        let lift = TransysSolver::new(&tsctx, false);
        let localabs = LocalAbs::new(&ts, &cfg);

        // Initialize multi-timeframe fields
        // Create a copy of the transition system with !bad as constraint
        let mut mt_origin_ts = ts.clone();
        mt_origin_ts.constraint.extend(ts.bad.iter().map(|l| !*l));
        // Initial unroll (no extra unrolling yet, timeframe_expansion starts at 1)
        let mt_unroll = TransysUnroll::new(&mt_origin_ts);
        let mt_tsctx = Grc::new(mt_unroll.compile().ctx());
        let mt_solver = TransysSolver::new(&mt_tsctx, true);
        let mt_lift = TransysSolver::new(&mt_tsctx, false);

        Self {
            cfg,
            ts,
            tsctx,
            activity,
            solvers: Vec::new(),
            inf_solver,
            lift,
            statistic,
            obligations: ProofObligationQueue::new(),
            mt_solver_start: Instant::now(),
            frame,
            localabs,
            auxiliary_var: Vec::new(),
            ots,
            rst,
            rng,
            filog: Default::default(),
            // Multi-timeframe fields
            mt_origin_ts,
            mt_unroll,
            mt_tsctx,
            mt_solver,
            mt_lift,
            timeframe_expansion: 1,
            mt_abs_mult: 1.0,
            mt_overshoot_used: 0,
            mt_overshoot_level: usize::MAX,
            mt_restart_pending: false,
            // max_size=1000, removal_ratio=0.2 (abc_PDR-multi uses the same
            // window after raising it from 100)
            blocking_time_median: BoundedMedianCalculator::new(1000, 0.2),
        }
    }

    pub fn invariant(&self) -> Vec<LitVec> {
        self.frame
            .invariant()
            .iter()
            .map(|l| l.map_var(|l| self.rst.restore_var(l)))
            .collect()
    }
}

impl Engine for IC3 {
    fn check(&mut self) -> Option<bool> {
        if !self.base() {
            return Some(false);
        }
        loop {
            let start = Instant::now();
            debug!("blocking phase begin");
            loop {
                match self.block(None) {
                    BlockResult::Failure => {
                        self.statistic.block.overall_time += start.elapsed();
                        return Some(false);
                    }
                    BlockResult::Proved => {
                        self.statistic.block.overall_time += start.elapsed();
                        self.verify();
                        return Some(true);
                    }
                    _ => (),
                }
                if let Some((bad, inputs)) = self.get_bad() {
                    debug!("bad state found in frame {}", self.level());
                    trace!("bad = {bad}");
                    let bad = LitOrdVec::new(bad);
                    self.add_obligation(ProofObligation::new(self.level(), bad, inputs, 0, None))
                } else {
                    break;
                }
            }
            debug!("blocking phase end");
            self.statistic.block.overall_time += start.elapsed();
            self.filog.log(Level::Info, self.frame.statistic(true));
            self.extend();
            let start = Instant::now();
            let propagate = self.propagate(None);
            self.statistic.overall_propagate_time += start.elapsed();
            if propagate {
                self.verify();
                return Some(true);
            }
            self.propagete_to_inf();
        }
    }

    fn proof(&mut self) -> Proof {
        let mut proof = self.ots.clone();
        if let Some(iv) = self.rst.init_var() {
            let piv = proof.add_init_var();
            self.rst.add_restore(iv, piv);
        }
        let mut invariants = self.frame.invariant();
        for c in self.ts.constraint.clone() {
            proof.rel.migrate(&self.ts.rel, c.var(), &mut self.rst.vmap);
            invariants.push(LitVec::from(!c));
        }
        let mut invariants: LitVvec = invariants
            .iter()
            .map(|l| LitVec::from_iter(l.iter().map(|l| self.rst.restore(*l))))
            .collect();
        invariants.extend(self.rst.eq_invariant());
        let mut certifaiger_dnf = vec![];
        for cube in invariants {
            certifaiger_dnf.push(proof.rel.new_and(cube));
        }
        let invariants = proof.rel.new_or(certifaiger_dnf);
        let bad = proof.rel.new_or(proof.bad);
        proof.bad = LitVec::from(proof.rel.new_or([invariants, bad]));
        Proof { proof }
    }

    fn witness(&mut self) -> Witness {
        if let Some(res) = self.localabs.witness(&self.rst) {
            return res;
        }
        let mut res = Witness::default();
        let b = self.obligations.peak().unwrap();
        assert!(b.frame == 0);
        let mut b = Some(b);
        let iv = self.rst.init_var();
        while let Some(bad) = b {
            res.state.push(
                bad.lemma
                    .iter()
                    .filter(|l| iv.is_none_or(|v| l.var() != v))
                    .map(|l| self.rst.restore(*l))
                    .collect(),
            );
            res.input.push(
                bad.input
                    .iter()
                    .filter(|l| iv.is_none_or(|v| l.var() != v))
                    .map(|l| self.rst.restore(*l))
                    .collect(),
            );
            b = bad.next.clone();
        }
        res.exact_init_state(&self.ots);
        for s in res.state.iter_mut() {
            *s = self.rst.restore_eq_state(s);
        }
        res
    }

    fn statistic(&mut self) {
        self.statistic.num_auxiliary_var = self.auxiliary_var.len();
        info!("obligations: {}", self.obligations.statistic());
        info!("{}", self.frame.statistic(false));
        let mut statistic = SolverStatistic::default();
        for s in self.solvers.iter() {
            statistic += *s.statistic();
        }
        info!("{statistic:#?}");
        info!("{:#?}", self.statistic);
    }
}
