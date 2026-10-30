//! The plan of an encode: where its layers split between the gathered passes and the deep pass.

use primitives::log2_strict_usize;

use super::stage::LOG_BATCH;

/// How an encode of `2^log_d` rows splits its layers `start..log_d`.
///
/// - The far layers `start..deep_start` run as gathered passes of at most `max_g` layers each.
/// - The near layers `deep_start..log_d` run as one deep pass over L2-sized sub-blocks.
/// - It holds numbers only and is `Copy`, so an encode can keep it to read rows back.
/// - [`AdditiveNttF64::rows`](super::AdditiveNttF64::rows) rebuilds a row from it, so it must come from the same pool size as the encode.
#[derive(Clone, Copy, Debug)]
pub struct Plan {
    pub(super) log_d: usize,
    pub(super) num_ntts: usize,
    /// The first layer of the encode, where the cosets split.
    pub(super) start: usize,
    pub(super) deep_start: usize,
    /// Most layers one gathered pass runs: what the L2 budget holds.
    pub(super) max_g: usize,
}

impl Plan {
    /// The plan of an encode from layer `start`.
    pub(super) fn new(log_d: usize, num_ntts: usize, start: usize) -> Self {
        let deep_start = deep_start(log_d, num_ntts, start);
        Self {
            log_d,
            num_ntts,
            start,
            deep_start,
            max_g: fit(L2_WORDS, num_ntts),
        }
    }

    /// Whether the first gathered pass can read a lane-major message itself: it has a layer to run, whole cache
    /// lines in a row, and enough residues to batch.
    pub(super) fn reads_lanes(&self) -> bool {
        let g = (self.deep_start - self.start).min(self.max_g);
        self.start < self.deep_start && self.num_ntts.is_multiple_of(8) && self.log_d - self.start - g >= LOG_BATCH
    }

    /// Whether an opening can rebuild a row from a lane-major message alone: one gathered pass reads it and
    /// covers every layer before the deep pass.
    pub(super) fn rebuilds_from_lanes(&self) -> bool {
        self.reads_lanes() && self.single_gathered_pass()
    }

    /// The gathered passes as `(layer, g)`: each runs layers `layer..layer + g`.
    pub(super) fn gathered(&self) -> impl Iterator<Item = (usize, usize)> + use<> {
        let (deep_start, max_g) = (self.deep_start, self.max_g);
        let mut layer = self.start;
        std::iter::from_fn(move || {
            (layer < deep_start).then(|| {
                let g = (deep_start - layer).min(max_g);
                layer += g;
                (layer - g, g)
            })
        })
    }

    /// Whether one gathered pass covers every layer before the deep pass.
    pub(super) fn single_gathered_pass(&self) -> bool {
        self.start < self.deep_start && self.deep_start - self.start <= self.max_g
    }

    /// Whether a deep pass has layers to run.
    pub(super) fn has_deep(&self) -> bool {
        self.deep_start < self.log_d
    }

    /// Whether the deep pass hands rows over itself: it starts past layer 0 and has layers to run.
    ///
    /// A deep pass from layer 0 is one sub-block on one thread, so its rows go over in parallel afterwards.
    pub(super) fn fuses_rows(&self) -> bool {
        0 < self.deep_start && self.deep_start < self.log_d
    }

    /// The log of the rows of one deep sub-block: a block of layer `deep_start`.
    pub(super) fn log_sub(&self) -> usize {
        self.log_d - self.deep_start
    }

    /// Words of one deep sub-block.
    pub(super) fn sub_len(&self) -> usize {
        self.num_ntts << self.log_sub()
    }

    /// The log of the rows of one deep task: a run of sub-blocks of at least an L2 budget of rows, so a high
    /// rate's tiny sub-blocks still reach the hasher in whole batches.
    pub(super) fn log_task(&self) -> usize {
        self.log_sub().max(self.max_g.min(self.log_d - par_log(self.log_d)))
    }

    /// The log of the rows of a block handed over in parallel after the last pass: four blocks per worker.
    pub(super) fn log_handover_rows(&self) -> usize {
        let log_tasks = (4 * parallel::num_threads()).next_power_of_two().ilog2() as usize;
        self.log_d - log_tasks.min(self.log_d)
    }

    /// Words of the buffer the encode left.
    pub fn words(&self) -> usize {
        self.num_ntts << self.log_d
    }
}

/// How many rows, as a log, a cache budget of `words` holds.
///
/// At 51 lanes: 2^17 / 51 -> 2^11 rows in L2,  2^18 / 51 -> 2^12 rows in L3.
pub(super) fn fit(words: usize, num_ntts: usize) -> usize {
    (words / num_ntts).max(1).ilog2() as usize
}

/// From 2^12 rows on, a deep pass cuts at least 2^LOG_SUBS_PER_WORKER sub-blocks per worker: this log of them.
fn par_log(log_d: usize) -> usize {
    /// Below this domain the transform is too small to split across the pool.
    const PARALLEL_FLOOR_LOG_D: usize = 12;
    /// Fewest rows a deep sub-block takes when splitting for parallelism.
    const MIN_SUB_LOG: usize = 8;
    if log_d >= PARALLEL_FLOOR_LOG_D {
        (log2_strict_usize(parallel::num_threads().next_power_of_two()) + LOG_SUBS_PER_WORKER).min(log_d - MIN_SUB_LOG)
    } else {
        0
    }
}

/// Where the deep pass of a `2^log_d`-row transform from layer `start` starts.
///
/// - If every layer fits one L3 sub-block, the deep pass is the whole transform: one sweep.
/// - Otherwise the deep pass keeps one L2 sub-block of layers.
fn deep_start(log_d: usize, num_ntts: usize, start: usize) -> usize {
    let deep = if log_d - start <= fit(L3_WORDS, num_ntts) {
        fit(L3_WORDS, num_ntts)
    } else {
        fit(L2_WORDS, num_ntts)
    };
    log_d.saturating_sub(deep).max(par_log(log_d)).max(start)
}

/// Words one L2-resident unit of work may span: a gathered row group or a deep sub-block.
///
/// # Why this value
///
/// - 2^17 words is 1 MiB, a whole Zen 5 L2.
/// - At 51 lanes it plans one gathered pass plus the deep pass, where 2^16 words planned two plus one.
///
/// # On Apple silicon
///
/// - A deep layer costs about the same whether its sub-block fits a cache or not: the transform is compute bound.
/// - A gathered layer costs more than a deep one, its rows scattered over more streams than the prefetcher follows.
/// - So the budget is sized to push layers into the deep pass, not to fit a cache.
/// - It exceeds [`L3_WORDS`], which then changes no plan.
#[cfg(not(all(target_arch = "aarch64", target_os = "macos")))]
pub(super) const L2_WORDS: usize = 1 << 17;
#[cfg(all(target_arch = "aarch64", target_os = "macos"))]
pub(super) const L2_WORDS: usize = 1 << 21;

/// Deep sub-blocks cut per worker, as a log.
///
/// - Apple silicon mixes performance and efficiency cores.
/// - With one sub-block each, the performance cores would wait on the efficiency cores' sub-blocks.
/// - Elsewhere every core is alike, and one each suffices.
#[cfg(not(all(target_arch = "aarch64", target_os = "macos")))]
const LOG_SUBS_PER_WORKER: usize = 0;
#[cfg(all(target_arch = "aarch64", target_os = "macos"))]
const LOG_SUBS_PER_WORKER: usize = 2;

/// Words a deep sub-block may span when it alone covers every layer.
///
/// # Why this value
///
/// - 2^18 words is 2 MiB, one thread's share of L3.
/// - Such a sub-block spills from L2 into L3.
/// - That costs extra L3 traffic, but saves a whole sweep of DRAM.
const L3_WORDS: usize = 1 << 18;
