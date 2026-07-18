use giputils::statistic::{Average, CountedDuration, RunningTime, SuccessRate};
use std::{collections::BTreeMap, fmt::Debug, time::Duration};

/// Multi-timeframe statistics (observability only, no behavior).
#[derive(Debug, Default)]
pub struct Mt {
    /// Restart-condition evaluations that reached the two difficult checks.
    pub restart_checks: usize,
    /// Only the absolute threshold held (relative blocked the restart).
    pub abs_only: usize,
    /// Only the relative condition held (absolute blocked the restart).
    pub rel_only: usize,
    /// Restarts triggered.
    pub num_restart: usize,
    /// Time spent in mt_block (multi-timeframe blocking attempts).
    pub mt_block_time: CountedDuration,
    /// mt_block entries keyed by timeframe expansion.
    pub mt_block_by_expansion: BTreeMap<usize, usize>,
    /// Time spent rebuilding the multi-timeframe solver (mt_init_solver).
    pub mt_init_time: CountedDuration,
    /// Fallback: unrolled solver produced no inductive core.
    pub fb_no_core: usize,
    /// Fallback: short-horizon refinement (mt_rec_refine) failed.
    pub fb_rec_refine: usize,
    /// Fallback: 1-step relative-induction gate rejected the lemma.
    pub fb_gate_reject: usize,
    /// Lemmas successfully added through the mt path.
    pub mt_lemma_added: usize,
    /// Blocking-time median at the end of the run.
    pub final_median: Option<Duration>,
    /// Number of samples in the median window at the end of the run.
    pub median_samples: usize,
}

#[derive(Debug, Clone, Default)]
pub struct Block {
    pub overall_time: Duration,
    pub get_bad_time: CountedDuration,
    pub blocked_time: CountedDuration,
    pub get_pred_time: Duration,
    pub mic_time: Duration,
    pub push_time: Duration,
}

#[allow(unused)]
#[derive(Debug, Default)]
pub struct Statistic {
    time: RunningTime,

    pub num_mic: usize,
    pub avg_mic_cube_len: Average,
    pub avg_po_cube_len: Average,
    pub mic_drop: SuccessRate,
    pub num_down: usize,
    pub num_down_sat: usize,

    pub ctp: SuccessRate,

    pub block: Block,

    pub overall_propagate_time: Duration,

    pub xor_gen: SuccessRate,
    pub num_auxiliary_var: usize,

    pub test: SuccessRate,

    pub mt: Mt,
}
