use crate::{
    Engine, Proof, Witness,
    config::Config,
    gipsat::{SolverStatistic, TransysSolver},
    transys::{Transys, TransysCtx, TransysIf, unroll::TransysUnroll},
};
use activity::Activity;
use frame::{Frame, Frames};
use giputils::{grc::Grc, hash::GHashMap, logger::IntervalLogger};
use log::{Level, debug, info};
use logic_form::{LitOrdVec, LitVec, Var, VarVMap};
use mic::{DropVarParameter, MicType};
use proofoblig::{ProofObligation, ProofObligationQueue};
use rand::{SeedableRng, rngs::StdRng};
use satif::Satif;
use statistic::Statistic;
use std::{time::{Instant, Duration}, cmp::{min, max}};

// Global debug flag
pub static DEBUG: bool = false;
pub static DEBUG_PRINT_CUBE: bool = false;

mod activity;
mod frame;
mod mic;
mod proofoblig;
mod solver;
mod statistic;
mod verify;
mod unsize_percentile_calculator;
pub use unsize_percentile_calculator::UnsizePercentileCalculator;

pub struct IC3 {
    cfg: Config,
    origin_ts: Transys,
    ts: Grc<TransysCtx>,
    solvers: Vec<TransysSolver>,
    lift: TransysSolver,
    bad_ts: Grc<TransysCtx>,
    bad_solver: cadical::Solver,
    bad_lift: TransysSolver,
    bad_input: GHashMap<Var, Var>,
    frame: Frames,
    obligations: ProofObligationQueue,
    activity: Activity,
    statistic: Statistic,
    pre_lemmas: Vec<LitVec>,
    abs_cst: LitVec,
    bmc_solver: Option<(Box<dyn satif::Satif>, TransysUnroll<Transys>)>,
    ots: Transys,
    rst: VarVMap,
    auxiliary_var: Vec<Var>,
    rng: StdRng,

    filog: IntervalLogger,

    multi_timeframe_origin_ts_with_not_bad: Transys,
    multi_timeframe_ts_unroll: TransysUnroll<Transys>,
    multi_timeframe_ts: Grc<TransysCtx>,
    multi_timeframe_solver_id: usize,
    multi_timeframe_solver: TransysSolver,
    multi_timeframe_lift: TransysSolver,
    timeframe_expansion: usize,
    blocking_nodes_per_level: GHashMap<usize, usize>,
    cube_count_percentile_calculator: UnsizePercentileCalculator,
    cube_count_threshold_to_use_multi_timeframe: Option<usize>,
}

impl IC3 {
    #[inline]
    pub fn level(&self) -> usize {
        self.solvers.len() - 1
    }

    fn extend(&mut self) {
        if !self.cfg.ic3.no_pred_prop {
            self.bad_solver = cadical::Solver::new();
            self.bad_ts.load_trans(&mut self.bad_solver, true);
        }
        let mut solver = TransysSolver::new(Some(self.frame.len()), &self.ts, self.cfg.rseed);
        for v in self.auxiliary_var.iter() {
            solver.add_domain(*v, true);
        }
        self.solvers.push(solver);
        self.frame.push(Frame::new());
        if self.level() == 0 {
            for init in self.ts.init.clone() {
                self.add_lemma(0, LitVec::from([!init]), true, None);
            }
            let mut init = LitVec::new();
            for l in self.ts.latchs.iter() {
                if self.ts.init_map[*l].is_none()
                    && let Some(v) = self.solvers[0].sat_value(l.lit())
                {
                    let l = l.lit().not_if(!v);
                    init.push(l);
                }
            }
            for i in init {
// println!("&&& add init: {}", i);
                self.ts.add_init(i.var(), Some(i.polarity()));
            }
        } else if self.level() == 1 {
            for cls in self.pre_lemmas.clone().iter() {
                self.add_lemma(1, !cls.clone(), true, None);
            }
        }

        if let Some(threshold) = self.cube_count_percentile_calculator.percentile(0.5) {
            self.cube_count_threshold_to_use_multi_timeframe = Some(threshold * 2);
        }
        else {
            self.cube_count_threshold_to_use_multi_timeframe = None;
        }
        self.cube_count_percentile_calculator.reset();
    }

    fn push_lemma(&mut self, frame: usize, mut cube: LitVec) -> (usize, LitVec) {
        let start = Instant::now();
        for i in frame + 1..=self.level() {
            if self.solvers[i - 1].inductive(&cube, true) {
                cube = self.solvers[i - 1].inductive_core();
            } else {
                return (i, cube);
            }
        }
        self.statistic.block_push_time += start.elapsed();
        (self.level() + 1, cube)
    }

    fn generalize(&mut self, mut po: ProofObligation, mic_type: MicType) -> bool {
        if self.cfg.ic3.inn && self.ts.cube_subsume_init(&po.lemma) {
            po.frame += 1;
            self.add_obligation(po.clone());
            return self.add_lemma(po.frame - 1, po.lemma.cube().clone(), false, Some(po));
        }
        let mut mic = self.solvers[po.frame - 1].inductive_core();
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

    fn block(&mut self, dirty_obligation: Option<ProofObligation>) -> Option<bool> {

        if let Some(root_po) = dirty_obligation.clone() {
            self.add_obligation(root_po);
        }

// println!("=== block ===");

        let mut cube_count = 0;
        let mut start = Instant::now();

        while let Some(mut po) = self.obligations.pop(self.level()) {

if unsafe { DEBUG_PRINT_CUBE } {
println!("--------------------------------");
println!("po.frame: {}", po.frame);
print!("po.lemma: ");
self.debug_print_sorted_cube(&po.lemma);
println!();
println!("--------------------------------");
}

            if po.removed {
                continue;
            }
            if self.ts.cube_subsume_init(&po.lemma) {
                if self.cfg.ic3.abs_cst {
                    self.add_obligation(po.clone());
                    if let Some(c) = self.check_witness_by_bmc(po.clone()) {
                        for c in c {
                            assert!(!self.abs_cst.contains(&c));
                            self.abs_cst.push(c);
                        }
                        info!("abs cst len: {}", self.abs_cst.len(),);
                        self.obligations.clear();
                        for f in self.frame.iter_mut() {
                            for l in f.iter_mut() {
                                l.po = None;
                            }
                        }
                        continue;
                    } else {
                        return Some(false);
                    }
                } else if self.cfg.ic3.inn && po.frame > 0 {
                    assert!(!self.solvers[0].solve(&po.lemma));
                } else {
                    self.add_obligation(po.clone());
                    assert!(po.frame == 0);
println!("===== find CEX =====");
println!("reach initial state: {}", &po.lemma);
let witness = self.multi_timeframe_witness();
println!("witness: {:?}", witness);
                    return Some(false);
                }
            }
            if let Some((bf, _)) = self.frame.trivial_contained(po.frame, &po.lemma) {
                po.push_to(bf + 1);
                self.add_obligation(po);
                continue;
            } else if self.is_time_to_restart(&cube_count, &start) {
                self.update_timeframe_expansion();
                // TODO: check which is better
                self.obligations.clear();
                // while let Some(_) = self.obligations.pop(self.level()) {}
                cube_count = 0;
                start = Instant::now();
                if let Some(root_po) = dirty_obligation.clone() {
                    self.add_obligation(root_po);
                }
                else {
                    // assert!(false);
                }
println!("restart at level: {} with timeframe_expansion: {}", self.level(), self.timeframe_expansion);
                continue;
            }
            debug!("{}", self.frame.statistic(false));
            po.bump_act();
            let blocked_start = Instant::now();

            unsafe { if DEBUG { dbg!("frame: {}", po.frame); } }
            unsafe { if DEBUG { println!("{}", &po.lemma); } }
            
// println!("=== solving po ===");
            // Increment the counter for this level
            cube_count += 1;
// *self.blocking_nodes_per_level.entry(po.frame).or_insert(0) += 1;
// println!("blocking_nodes_per_level: {:?}", self.blocking_nodes_per_level);

//*
            if self.cfg.ic3.multi_timeframe && po.frame == self.level() && self.timeframe_expansion > 1 {
                let continue_solving= self.multi_timeframe_block(po.clone(), po.frame, &po.lemma, self.timeframe_expansion.clone());
                if !continue_solving {
                    // reach fix point, UNSAT
                    dbg!("reach fix point, UNSAT");
                    return None;
                }
                else {
                    continue;
                }
            }
// */


            let blocked = self.blocked_with_ordered(po.frame, &po.lemma, false, false);
            self.statistic.block_blocked_time += blocked_start.elapsed();
            if blocked {
unsafe { if DEBUG { dbg!("UNSAT"); } }
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
                                let limit = ((act - EXCTG_THRESHOLD).powf(0.3) * 2.0 + 5.0).round()
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
dbg!("generalized in block");
                    return None;
                }
            } else {
                let (model, inputs) = self.get_pred(po.frame, true);

unsafe { if DEBUG { dbg!("SAT"); } }
if unsafe { DEBUG_PRINT_CUBE } {
print!("pred: ");
self.debug_print_sorted_cube(&model);
println!();
}

                self.add_obligation(ProofObligation::new(
                    po.frame - 1,
                    LitOrdVec::new(model),
                    vec![inputs],
                    po.depth + 1,
                    Some(po.clone()),
                ));
                self.add_obligation(po);
            }
        }

// println!("&&& cube_count(level: {}): {} &&&", self.level(), cube_count);
self.cube_count_percentile_calculator.add(cube_count);
self.timeframe_expansion = 1;
        Some(true)
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
        if self.ts.cube_subsume_init(&lemma) {
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
                let mut mic = self.solvers[frame - 1].inductive_core();
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

    fn trivial_block(
        &mut self,
        frame: usize,
        lemma: LitOrdVec,
        constraint: &[LitVec],
        parameter: DropVarParameter,
    ) -> bool {
        let mut limit = parameter.limit;
        self.trivial_block_rec(frame, lemma, constraint, &mut limit, parameter)
    }

    fn propagate(&mut self, from: Option<usize>) -> bool {
        let from = from.unwrap_or(self.frame.early).max(1);
        for frame_idx in from..self.level() {
            self.frame[frame_idx].sort_by_key(|x| x.len());
            let frame = self.frame[frame_idx].clone();
            for mut lemma in frame {
                if self.frame[frame_idx].iter().all(|l| l.ne(&lemma)) {
                    continue;
                }
                for ctp in 0..3 {
                    if self.blocked_with_ordered(frame_idx + 1, &lemma, false, false) {
                        let core = if self.cfg.ic3.inn && self.ts.cube_subsume_init(&lemma) {
                            lemma.cube().clone()
                        } else {
                            self.solvers[frame_idx].inductive_core()
                        };
                        if let Some(po) = &mut lemma.po
                            && po.frame < frame_idx + 2
                            && self.obligations.remove(po)
                        {
                            po.push_to(frame_idx + 2);
                            self.obligations.add(po.clone());
                        }
                        self.add_lemma(frame_idx + 1, core, true, lemma.po);
                        self.statistic.ctp.statistic(ctp > 0);
                        break;
                    }
                    if !self.cfg.ic3.ctp {
                        break;
                    }
                    let (ctp, _) = self.get_pred(frame_idx + 1, false);
                    if !self.ts.cube_subsume_init(&ctp)
                        && self.solvers[frame_idx - 1].inductive(&ctp, true)
                    {
                        let core = self.solvers[frame_idx - 1].inductive_core();
                        let mic =
                            self.mic(frame_idx, core, &[], MicType::DropVar(Default::default()));
                        if self.add_lemma(frame_idx, mic, false, None) {
                            return true;
                        }
                    } else {
                        break;
                    }
                }
            }
            if self.frame[frame_idx].is_empty() {
                return true;
            }
        }
        self.frame.early = self.level();
        false
    }

    fn base(&mut self) -> bool {
        self.extend();
        assert!(self.level() == 0);
        if !self.cfg.ic3.no_pred_prop {
            let bad = self.ts.bad;
            if self.solvers[0].solve(&self.ts.bad.cube()) {
                let (bad, inputs) = self.get_pred(self.solvers.len(), true);
                self.add_obligation(ProofObligation::new(
                    0,
                    LitOrdVec::new(bad),
                    vec![inputs],
                    0,
                    None,
                ));
                return false;
            }
            self.ts.constraints.push(!bad);
            self.lift = TransysSolver::new(None, &self.ts, self.cfg.rseed);
        }
        true
    }
}

impl IC3 {
    pub fn new(mut cfg: Config, mut ts: Transys, pre_lemmas: Vec<LitVec>) -> Self {
        let ots = ts.clone();
        let mut rst = VarVMap::new_self_map(ts.max_var());
        ts = ts.check_liveness_and_l2s(&mut rst);
        if !cfg.preproc.no_preproc {
            ts.simplify(&mut rst);
            ts.frts(&cfg, &mut rst);
        }
        let mut uts = TransysUnroll::new(&ts);
        uts.unroll();
        if cfg.ic3.inn {
            cfg.ic3.no_pred_prop = true;
            ts = uts.interal_signals();
        }
        let mut bad_input = GHashMap::new();
        for &l in ts.input.iter() {
            bad_input.insert(uts.var_next(l, 1), l);
        }
        let mut bad_ts = uts.compile();
        bad_ts.constraint.extend(ts.bad.iter().map(|&l| !l));
        let origin_ts = ts.clone();
        let ts = Grc::new(ts.ctx());
        let bad_ts = Grc::new(bad_ts.ctx());
        let statistic = Statistic::new(cfg.model.to_str().unwrap());
        let activity = Activity::new(&ts);
        let frame = Frames::new(&ts);
        let lift = TransysSolver::new(None, &ts, cfg.rseed);
        let bad_lift = TransysSolver::new(None, &bad_ts, cfg.rseed);
        let abs_cst = if cfg.ic3.abs_cst {
            LitVec::new()
        } else {
            ts.constraints.clone()
        };
        let rng = StdRng::seed_from_u64(cfg.rseed);
        // let multi_timeframe_ts = Grc::new(multi_timeframe_ts_unroll.compile().ctx());
        // let multi_timeframe_solver = Solver::new(options.clone(), Some(4), &multi_timeframe_ts);
        // let multi_timeframe_lift = Solver::new(options.clone(), None, &multi_timeframe_ts);


        let mut multi_timeframe_origin_ts_with_not_bad = origin_ts.clone();
        multi_timeframe_origin_ts_with_not_bad.constraint.push(!ts.bad);
        let multi_timeframe_ts_unroll = TransysUnroll::new(&multi_timeframe_origin_ts_with_not_bad);
        let multi_timeframe_ts = Grc::new(multi_timeframe_ts_unroll.compile().ctx());
        let multi_timeframe_solver_id = 0;
        let multi_timeframe_solver = TransysSolver::new(Some(4), &multi_timeframe_ts, cfg.rseed);
        let multi_timeframe_lift = TransysSolver::new(None, &multi_timeframe_ts, cfg.rseed);
        Self {
            cfg,
            origin_ts,
            ts,
            activity,
            solvers: Vec::new(),
            bad_ts,
            bad_solver: cadical::Solver::new(),
            bad_lift,
            bad_input,
            lift,
            statistic,
            obligations: ProofObligationQueue::new(),
            frame,
            abs_cst,
            pre_lemmas,
            auxiliary_var: Vec::new(),
            ots,
            rst,
            bmc_solver: None,
            rng,
            filog: Default::default(),
            multi_timeframe_origin_ts_with_not_bad,
            multi_timeframe_ts_unroll,
            multi_timeframe_ts,
            multi_timeframe_solver_id,
            multi_timeframe_solver,
            multi_timeframe_lift,
            timeframe_expansion: 1,
            blocking_nodes_per_level: GHashMap::new(),
            cube_count_percentile_calculator: UnsizePercentileCalculator::new(),
            cube_count_threshold_to_use_multi_timeframe: None,
        }
    }

    pub fn invariant(&self) -> Vec<LitVec> {
        self.frame
            .invariant()
            .iter()
            .map(|l| l.map_var(|l| self.rst[&l]))
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
            let mut dirty_obligation: Option<ProofObligation> = None;
            loop {
                match self.block(dirty_obligation) {
                    Some(false) => {
                        self.statistic.overall_block_time += start.elapsed();
                        return Some(false);
                    }
                    None => {
                        self.statistic.overall_block_time += start.elapsed();
                        self.verify();
                        return Some(true);
                    }
                    _ => (),
                }
                if let Some((bad, inputs, depth)) = self.get_bad() {
                    let bad = LitOrdVec::new(bad);
                    dirty_obligation = Some(ProofObligation::new(
                        self.level(),
                        bad,
                        inputs,
                        depth,
                        None,
                    ));
                } else {
                    break;
                }
            }
            let blocked_time = start.elapsed();
            self.filog.log(Level::Info, self.frame.statistic(true));
            self.statistic.overall_block_time += blocked_time;
            self.extend();
            let start = Instant::now();
            let propagate = self.propagate(None);
            self.statistic.overall_propagate_time += start.elapsed();
            if propagate {
dbg!("fix point at propagate");
                self.verify();
                return Some(true);
            }
        }
    }

    fn proof(&mut self) -> Proof {
        let invariants = self.frame.invariant();
        let invariants = invariants
            .iter()
            .map(|l| LitVec::from_iter(l.iter().filter_map(|l| self.rst.lit_map(*l))));
        let mut proof = self.ots.clone();
        let mut certifaiger_dnf = vec![];
        for cube in invariants {
            certifaiger_dnf.push(proof.rel.new_and(cube));
        }
        let invariants = proof.rel.new_or(certifaiger_dnf);
        let constrains: Vec<_> = proof
            .constraint
            .iter()
            .map(|e| !*e)
            .chain(proof.bad.iter().copied())
            .collect();
        let constrains = proof.rel.new_or(constrains);
        proof.bad = LitVec::from(proof.rel.new_or([invariants, constrains]));
        Proof { proof }
    }

    fn witness(&mut self) -> Witness {
println!("*** witness ***");
        let mut res = Witness::default();
        if let Some((bmc_solver, uts)) = self.bmc_solver.as_mut() {
            for k in 0..=uts.num_unroll {
                let mut w = LitVec::new();
                for l in uts.ts.input() {
                    let l = l.lit();
                    let kl = uts.lit_next(l, k);
                    if let Some(v) = bmc_solver.sat_value(kl)
                        && let Some(r) = self.rst.lit_map(l.not_if(!v))
                    {
                        w.push(r);
                    }
                }
                res.input.push(w);
                let mut w = LitVec::new();
                for l in uts.ts.latch() {
                    let l = l.lit();
                    let kl = uts.lit_next(l, k);
                    if let Some(v) = bmc_solver.sat_value(kl)
                        && let Some(r) = self.rst.lit_map(l.not_if(!v))
                    {
                        w.push(r);
                    }
                }
                res.state.push(w);
            }
            return res;
        }
        let b = self.obligations.peak().unwrap();
        assert!(b.frame == 0);
print!("init: ");
        let mut init_state = LitVec::new();
        for &l in b.lemma.iter() {
            if let Some(r) = self.rst.lit_map(l) {
                init_state.push(r);
print!("{} ", r);
            }
        }
        res.state.push(init_state);
println!();
        let mut b = Some(b);
        while let Some(bad) = b {
            res.state.push(
                bad.lemma
                    .iter()
                    .filter_map(|l| self.rst.lit_map(*l))
                    .collect(),
            );

            if let Some(next_bad) = &bad.next {  // Use reference to check without moving
                let timeframe = bad.depth - next_bad.depth;
                println!("--------------------------------");
                println!("timeframe: {}", timeframe);
                if timeframe > 1 {
                    println!("multi_timeframe_witness");
                    println!("depth: {}", bad.depth);
                    println!("next depth: {}", next_bad.depth);
                }
                println!("--------------------------------");
            }
            else {
                println!("this is bad proof-obligation");
            }
            
            for i in bad.input.iter() {
                res.input
                    .push(i.iter().filter_map(|l| self.rst.lit_map(*l)).collect());
println!("{}", res.input.last().unwrap());
            }
            b = bad.next.clone();
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

//* 
impl IC3 {
    fn multi_timeframe_blocked_with_ordered(
        &mut self,
        cube: &LitVec,
        ascending: bool,
        strengthen: bool,
    ) -> bool {
        self.multi_timeframe_blocked_with_ordered_with_constrain(cube, ascending, strengthen, vec![])
    }

    fn multi_timeframe_blocked_with_ordered_with_constrain(
        &mut self,
        cube: &LitVec,
        ascending: bool,
        strengthen: bool,
        constraint: Vec<LitVec>,
    ) -> bool {
        let mut ordered_cube = cube.clone();
        self.activity.sort_by_activity(&mut ordered_cube, ascending);
        self.multi_timeframe_solver.inductive_with_constrain(&ordered_cube, strengthen, constraint)
    }

    fn multi_timeframe_get_lemma_at_frame(&self, lemma: &LitOrdVec, lift_num: usize) -> LitOrdVec {
        assert!(lift_num <= self.multi_timeframe_ts_unroll.num_unroll);
        let new_lemma = LitOrdVec::new(self.multi_timeframe_ts_unroll.lits_next(lemma, lift_num));
        new_lemma
    }

    fn multi_timeframe_init_solver(&mut self, frame: usize, timeframe_expansion: usize) {
        assert!(timeframe_expansion >= 1);
        assert!(timeframe_expansion <= frame);

        // if self.multi_timeframe_solver_id == frame && self.timeframe_expansion == timeframe_expansion {
        //     return;
        // }
// println!("*** init solver ***");
        self.multi_timeframe_ts_unroll = TransysUnroll::new(&self.multi_timeframe_origin_ts_with_not_bad);
        self.multi_timeframe_ts_unroll.unroll_to(timeframe_expansion-1);
        self.multi_timeframe_ts = Grc::new(self.multi_timeframe_ts_unroll.compile().ctx());
        self.multi_timeframe_solver = TransysSolver::new(Some(4), &self.multi_timeframe_ts, self.cfg.rseed);
        self.multi_timeframe_lift = TransysSolver::new(None, &self.multi_timeframe_ts, self.cfg.rseed);

        self.multi_timeframe_solver_id = frame;
        self.timeframe_expansion = timeframe_expansion;

        // add constraint from frames
        let start_frame = frame - timeframe_expansion;
        for i in start_frame..self.frame.len() {
            for frame_lemma in self.frame[i].iter() {
                for f in start_frame..frame {
                    if f <= i {
                        let lift_num = f - start_frame;
                        let lemma = self.multi_timeframe_get_lemma_at_frame(&frame_lemma, lift_num);
                        let clause = !lemma.cube();
                        self.multi_timeframe_solver.add_clause(&clause);
                        // self.multi_timeframe_lift.add_lemma(&clause);
                    }
                    else {
                        break;
                    }
                }
            }
        }

        if start_frame == 0 {
println!("add initial state constraint for multi_timeframe_solver");
            for init in self.ts.init.clone() {
                let clause = [init];
                self.multi_timeframe_solver.add_clause(&clause);
                // self.multi_timeframe_lift.add_lemma(&clause);
            }
        }

    }

    fn max_timeframe_expansion(&self) -> usize {
        // 2
        // self.level() - 2
        self.level()
    }

    fn update_timeframe_expansion(&mut self) {
        self.timeframe_expansion = min(self.timeframe_expansion * 2, self.max_timeframe_expansion());
    }

    fn is_time_to_restart(&self, cube_count: &usize, start: &Instant) -> bool {
        if !self.cfg.ic3.multi_timeframe {
            return false;
        }
        let min_level_to_use_multi_timeframe = 4;
        let min_cube_count_threshold = 100;
        let restart_time_threshold = Duration::from_secs(5);
        if self.level() < min_level_to_use_multi_timeframe {
            return false;
        }
        if self.timeframe_expansion == self.max_timeframe_expansion() {
            return false;
        }

        let cube_count_condition = 
            if let Some(mut threshold) = self.cube_count_threshold_to_use_multi_timeframe {
                threshold = max(threshold, min_cube_count_threshold);
// println!("level: {}, cube_count: {}, threshold: {}, time: {:?}", self.level(), cube_count, threshold, start.elapsed());
                *cube_count > threshold
            }
            else {
// println!("level: {}, cube_count: {}, threshold: None, time: {:?}", self.level(), cube_count, start.elapsed());
                false
            };

        let time_condition = start.elapsed() > restart_time_threshold;

        cube_count_condition && time_condition
    }

    // return continue solving or not
    // return true: continue solving
    // return false: reach fix point, UNSAT
    fn multi_timeframe_block(
        &mut self,
        mut po: ProofObligation,
        frame: usize,
        cube: &LitVec,
        timeframe_expansion: usize
    ) -> bool {
        unsafe { if DEBUG { dbg!(frame); } }
        assert!(timeframe_expansion <= frame);


        self.multi_timeframe_init_solver(frame, timeframe_expansion);

        let ascending = false;
        let strengthen = true;
        let blocked = self.multi_timeframe_blocked_with_ordered(cube, ascending, strengthen);

        if blocked {
            unsafe { if DEBUG { dbg!("UNSAT in multi_timeframe_block"); } }
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
                            let limit = ((act - EXCTG_THRESHOLD).powf(0.3) * 2.0 + 5.0).round()
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
            if self.multi_timeframe_generalize(po, mic_type, timeframe_expansion) {
                // reach fix point, UNSAT
                // return None;
dbg!("generalized in multi_timeframe_block");
                return false;
            }
        }
        else {
            unsafe { if DEBUG { dbg!("SAT in multi_timeframe_block"); } }
            // let (model, inputs) = self.get_pred(po.frame, true);
            // self.add_obligation(ProofObligation::new(
            //     po.frame - 1,
            //     Lemma::new(model),
            //     vec![inputs],
            //     po.depth + 1,
            //     Some(po.clone()),
            // ));
            // self.add_obligation(po);
            let (model, inputs) = self.multi_timeframe_get_pred(true);

if unsafe { DEBUG_PRINT_CUBE } {
println!("SAT in multi_timeframe_block");
println!("frame: {}", frame);
println!("timeframe_expansion: {}", timeframe_expansion);
print!("pred: ");
self.debug_print_sorted_cube(&model);
println!();
}

            self.add_obligation(ProofObligation::new(
                po.frame - timeframe_expansion,
                LitOrdVec::new(model),
                inputs,
                po.depth + timeframe_expansion,
                Some(po.clone()),
            ));
            self.add_obligation(po);
        }
        return true;
    }

    fn multi_timeframe_get_drop_var_parameter(&mut self, po: &mut ProofObligation) -> DropVarParameter {
        if self.cfg.ic3.dynamic {
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
                        let limit = ((act - EXCTG_THRESHOLD).powf(0.3) * 2.0 + 5.0).round()
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
                DropVarParameter::new(limit, max, level)
            } else {
                DropVarParameter::default()
            }
        } else {
            DropVarParameter::default()
        }
    }

    fn multi_timeframe_generalize(
        &mut self,
        mut po: ProofObligation,
        mic_type: MicType,
        timeframe_expansion: usize,
    ) -> bool {
        if self.cfg.ic3.inn && self.ts.cube_subsume_init(&po.lemma) {
            assert!(false); // TODO: fix this
            po.frame += 1;
            self.add_obligation(po.clone());
            return self.add_lemma(po.frame - 1, po.lemma.cube().clone(), false, Some(po));
        }
        let mut mic = self.multi_timeframe_solver.inductive_core();
        mic = self.multi_timeframe_mic(po.frame, mic, &[], mic_type, timeframe_expansion);
        let drop_var_parameter = self.multi_timeframe_get_drop_var_parameter(&mut po);
        let unsat_core_timeframe_expansion_1 = self.multi_timeframe_rec_refine(timeframe_expansion - 1, &po.lemma, drop_var_parameter);
        let blocking_cube = self.multi_timeframe_get_blocking_cube(&mic, &unsat_core_timeframe_expansion_1);
        // let (frame, mic) = self.push_lemma(po.frame, mic);
        self.statistic.avg_po_cube_len += po.lemma.len();
        // po.push_to(frame);
        // self.add_obligation(po.clone());
        // if self.add_lemma(frame - 1, mic.clone(), false, Some(po)) {
        //     return true;
        // }
        // TODO: check frame -1 or not
        // for i in 1..=po.frame {
        //     // DEBUG: inductive fail
        //     // if self.multi_timeframe_add_lemma(i, blocking_cube.clone(), true, Some(po.clone())) {
        //     if self.multi_timeframe_add_lemma(i, blocking_cube.clone(), false, Some(po.clone())) {
        //         dbg!("add lemma at frame {}, target frame {}", i, po.frame);
        //         return true;
        //     }
        // }
        self.multi_timeframe_add_lemma(po.frame, blocking_cube.clone(), true, Some(po.clone()));
        false
    }

    fn multi_timeframe_rec_refine(
        &mut self,
        frame: usize,
        lemma: &LitOrdVec,
        parameter: DropVarParameter,
    ) -> LitVec {
        assert!(frame > 0);
        assert!(!self.ts.cube_subsume_init(lemma));

        loop {
            if self.blocked_with_ordered(
                frame,
                lemma,
                false,
                true,
            ) {
                let mut mic = self.solvers[frame - 1].inductive_core();
                mic = self.mic(frame, mic, &[], MicType::DropVar(parameter));
                // DEBUG: inductive fail
                let (frame, mic) = self.push_lemma(frame, mic);
                self.add_lemma(frame - 1, mic.clone(), false, None);
                // self.add_lemma(frame, mic.clone(), false, None);
                return mic;
            } else {
                let model = LitOrdVec::new(self.get_pred(frame, false).0);
                self.multi_timeframe_rec_refine(frame - 1, &model, parameter);
                continue;
            }
        }
    }

    fn multi_timeframe_get_blocking_cube(
        &mut self, 
        mic: &LitVec,
        unsat_core_timeframe_expansion_1: &LitVec,
    ) -> LitVec {
        let mut result = LitVec::new();
        let mut lit_set = std::collections::BTreeSet::new();

        // First add all literals from mic
        for &lit in mic.iter() {
            lit_set.insert(lit);
            result.push(lit);
        }

        // Then add literals from unsat_core_timeframe_expansion_1
        for &lit in unsat_core_timeframe_expansion_1.iter() {
            assert!(!lit_set.contains(&!lit), "Conflicting literals found: {:?} and {:?}", !lit, lit);
            if lit_set.insert(lit) {
                result.push(lit);
            }
        }
        result
    }

    pub fn debug_print_sorted_cube(&self, cube: &LitVec) {
        let mut sorted_cube = cube.clone();
        sorted_cube.sort();
        print!("{}", sorted_cube);
    }

    fn multi_timeframe_witness(&mut self) -> Witness {
println!("*** multi_timeframe_witness ***");
        let mut res = Witness::default();
        let b = self.obligations.peak().unwrap();
        assert!(b.frame == 0);
println!("init: ");
        for &l in b.lemma.iter() {
            if let Some(r) = self.rst.lit_map(l) {
                res.state.push(LitVec::from([r]));
print!("{} ", r);
            }
        }
println!();

        let mut b = Some(b);
        while let Some(bad) = b {
println!("================");
            let mut timeframe = 1;
            if let Some(next_bad) = &bad.next {  // Use reference to check without moving
                timeframe = bad.depth - next_bad.depth;
                println!("timeframe: {}", timeframe);
                if timeframe > 1 {
                    println!("multi_timeframe_witness");
                    println!("depth: {}", bad.depth);
                    println!("next depth: {}", next_bad.depth);
                }
            }
            else {
                println!("this is bad proof-obligation");
            }
            let _ts = if timeframe == 1 { &self.ts } else { &self.multi_timeframe_ts };
            for i in bad.input.iter() {
                res.input
                .push(i.iter().filter_map(|l| self.rst.lit_map(*l)).collect());            
    self.debug_print_sorted_cube(&res.input.last().unwrap());
    println!();
            }
println!("================");
            b = bad.next.clone();
        }
println!("*** multi_timeframe_witness end ***");
        res
    }
}
//*/