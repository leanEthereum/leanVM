//! The encodes: each composes the plan, the gathered passes and the deep pass into one transform.

use primitives::field::F64;
use primitives::log2_strict_usize;

use super::deep::DeepPass;
use super::gathered::GatheredPass;
use super::plan::Plan;
use super::source::{Lanes, Source};
use super::twiddles::AdditiveNttF64;
use super::window::Window;

/// Receives a finished block of codeword rows, as `(first_row, rows)`.
///
/// - It is called from pool tasks.
/// - Each row is handed over exactly once.
/// - Blocks are aligned, and all of one power-of-two size.
/// - A block is handed over while its rows are still in cache.
pub type RowSink<'a> = dyn Fn(usize, &[F64]) + Sync + 'a;

/// What [`AdditiveNttF64::encode_lane_major`](super::AdditiveNttF64::encode_lane_major) is asked to keep of its codeword.
#[derive(Clone, Copy, PartialEq, Eq)]
pub enum Keep {
    /// All of it: the deep pass is written back.
    Whole,
    /// The buffer as the gathered passes leave it.
    /// [`AdditiveNttF64::rows`] runs the deep pass again on a row read.
    BeforeDeep,
    /// None of it, if the plan allows: [`AdditiveNttF64::rows`] recomputes a row from the message.
    Nothing,
}

/// What an encode kept of its codeword, for [`AdditiveNttF64::rows`] to read rows from.
///
/// Each carries the encode's [`Plan`].
pub enum Codeword {
    /// All of it.
    Whole(Vec<F64>, Plan),
    /// The buffer as the gathered passes left it: the deep layers run again on each row read.
    BeforeDeep(Vec<F64>, Plan),
    /// No buffer: each row is recomputed from the message of this many lane-major lanes.
    Nothing(Plan, usize),
}

impl Codeword {
    /// The plan of the encode.
    pub fn plan(&self) -> &Plan {
        match self {
            Self::Whole(_, plan) | Self::BeforeDeep(_, plan) | Self::Nothing(plan, _) => plan,
        }
    }
}

/// The encodes: `transform` is the spine, a [`Plan`], gathered passes, a deep pass and a
/// hand-over, and the three public encodes differ in their source and in what they keep of the codeword.
impl AdditiveNttF64 {
    /// RS-encode a message already stored in the codeword's first replica.
    ///
    /// # Overview
    ///
    /// - The message fills the first `1 / 2^r` of the buffer, `r` the log inverse rate.
    /// - It is row-major: word `row * n + lane` for `n` interleaved lanes.
    /// - The buffer ends as `2^r` copies of it, each transformed from layer `r` on.
    ///
    /// The replication is free: the first pass reads its rows from the message itself, see `transform`.
    pub fn encode_interleaved_in_place(&self, data: &mut [F64], num_ntts: usize, log_inv_rate: usize) {
        self.transform(
            &mut Window::new(data, num_ntts, 0),
            log_inv_rate,
            Source::InPlace,
            None,
            false,
        );
    }

    /// Encode a lane-major message, handing `on_rows` every finished block, and keep what `keep` asks for.
    ///
    /// - The result equals `transpose_lane_major` into block 0 followed by the in-place encode.
    /// - With a gathered first pass, that pass reads the message itself and writes every block.
    /// - So no transposed copy of the message is written and read back.
    /// - With [`Keep::Nothing`], if a single such pass covers the layers before the deep pass,
    ///   the codeword is never whole.
    /// - The encode then runs once per half of the cosets, in one half-size buffer.
    ///   The deep pass goes to `on_rows` only.
    /// - Otherwise the codeword is kept whole, before its deep layers unless `keep` is [`Keep::Whole`].
    #[allow(clippy::too_many_arguments)]
    pub fn encode_lane_major(
        &self,
        msg: &[F64],
        n_lanes: usize,
        num_ntts: usize,
        log_inv_rate: usize,
        keep: Keep,
        on_rows: &RowSink<'_>,
    ) -> Codeword {
        assert!(0 < n_lanes && n_lanes <= num_ntts, "a row holds its lanes");
        assert!(log_inv_rate >= 1, "a codeword has at least two cosets");
        let msg_rows = msg.len() / n_lanes;
        assert_eq!(msg.len(), n_lanes * msg_rows, "the message is n_lanes lane blocks");
        let log_d = log2_strict_usize(msg_rows) + log_inv_rate;
        let by_halves = keep == Keep::Nothing && Plan::new(log_d, num_ntts, log_inv_rate).rebuilds_from_lanes();
        let defer_deep = keep != Keep::Whole;
        // The cosets one pass holds: half of them when the opening rebuilds the rows.
        let held = (1usize << log_inv_rate) >> usize::from(by_halves);
        let mut done = None;
        // SAFETY: the fill writes every element before it reads any.
        let data = unsafe {
            primitives::filled_vec((held * msg_rows) * num_ntts, |data| {
                for first in (0..1usize << log_inv_rate).step_by(held).rev() {
                    let src = Source::Lanes(Lanes { words: msg, n_lanes });
                    let mut win = Window::new(data, num_ntts, first * msg_rows);
                    done = Some(self.transform(&mut win, log_inv_rate, src, Some(on_rows), defer_deep));
                }
            })
        };
        match done.expect("the encode runs") {
            (plan, true) if by_halves => Codeword::Nothing(plan, n_lanes),
            (plan, true) => Codeword::BeforeDeep(data, plan),
            (plan, false) => Codeword::Whole(data, plan),
        }
    }

    /// RS-encode a row-major message held apart, handing `on_rows` every finished block of rows.
    ///
    /// - The codeword equals the in-place encode's, and every word is written before it is read.
    /// - With `defer_deep`, the deep pass is not written back: each deep sub-block is finished in scratch
    ///   and handed to `on_rows` from there, and the codeword is kept [`Codeword::BeforeDeep`].
    pub fn encode_interleaved_with(
        &self,
        msg: &[F64],
        num_ntts: usize,
        log_inv_rate: usize,
        defer_deep: bool,
        on_rows: &RowSink<'_>,
    ) -> Codeword {
        let mut done = None;
        // SAFETY: the fill writes every element before it reads any.
        let data = unsafe {
            primitives::filled_vec(msg.len() << log_inv_rate, |data| {
                let mut win = Window::new(data, num_ntts, 0);
                done = Some(self.transform(&mut win, log_inv_rate, Source::Rows(msg), Some(on_rows), defer_deep));
            })
        };
        match done.expect("the encode runs") {
            (plan, true) => Codeword::BeforeDeep(data, plan),
            (plan, false) => Codeword::Whole(data, plan),
        }
    }

    /// Run layers `start..log_d` of a `2^log_d`-row transform in as few sweeps of the buffer as possible.
    ///
    /// A large transform is bound by memory bandwidth, so its cost is its number of sweeps.
    ///
    /// # Plan
    ///
    /// ```text
    ///     layers:  start ............ deep_start ............ log_d
    ///              |---- gathered passes ----|---- deep pass ----|
    ///
    ///     gathered pass:  one task per row group of 2^g rows, 2^(log_d - layer - g) apart
    ///                     gathered into L2 scratch, all g layers run there, written back
    ///     deep pass:      one task per run of contiguous sub-blocks, at least an L2 budget of rows,
    ///                     its layers run in place (or in scratch, when a separate message has to be copied in)
    /// ```
    ///
    /// - When every layer fits one L3-sized sub-block, the deep pass is the whole transform: one sweep.
    /// - Otherwise gathered passes run until the rest fits one L2-sized sub-block.
    /// - With `n` words a row, a block of up to `(L2 words / n)^2` rows then costs two sweeps.
    ///
    /// # With a message
    ///
    /// - The layer-`start` blocks are not in the buffer yet: each is a copy of the message, see [`Source`].
    /// - The first pass reads its rows from the message instead.
    /// - A lane-major message is read by that pass directly.
    ///   A plan with no such pass transposes it into block 0 of the buffer and encodes in place.
    /// - Its `first_row` and the buffer's size give the layer-`start` blocks the buffer holds.
    /// - Twiddles and rows handed to `on_rows` stay global.
    ///
    /// # Why block 0 goes last
    ///
    /// - The message may be the buffer's own block 0.
    /// - So a gathered task visits blocks in descending order, and overwrites block 0 last.
    /// - Tasks own disjoint row residues, so no task reads rows another task writes.
    ///
    /// # Finished rows
    ///
    /// - Each deep sub-block is final, and hands its rows to `on_rows` while they are in L2.
    /// - Without a split deep pass, the rows go over in parallel blocks at the end.
    /// - With `defer_deep`, the deep pass's results go only to `on_rows`, not back into the buffer.
    pub(super) fn transform(
        &self,
        win: &mut Window,
        start: usize,
        mut src: Source<'_>,
        on_rows: Option<&RowSink<'_>>,
        defer_deep: bool,
    ) -> (Plan, bool) {
        // The buffer is 2^log_d rows of `num_ntts` words, or the layer-`start` blocks of a lane-major message.
        let (num_ntts, log_d) = (win.num_ntts(), src.log_d(win, start));
        assert!(log_d <= self.log_domain_size());
        assert!(start <= log_d);

        // The plan reads the original message, before a lane-major one is transposed.
        let plan = Plan::new(log_d, num_ntts, start);

        // Phase 1: gathered passes, each at most one L2 group of layers.
        //
        // Only the first one reads the message.
        // A lane-major message is read by the first gathered pass, a batch of residues at a time.
        // Without such a pass, or with too few residues to batch, it is transposed into block 0 first.
        if matches!(src, Source::Lanes(_)) && !plan.reads_lanes() {
            assert_eq!(
                win.len() / num_ntts,
                1 << log_d,
                "a partial buffer needs the gathered pass"
            );
            src = src.transpose_into(win, log_d - start);
        }
        for (layer, g) in plan.gathered() {
            GatheredPass::new(&plan, win, layer, g, src.take()).run(self, win);
        }

        // Phase 2: replicas a deep-only plan cannot build inside its tasks.
        src = src.replicate(win, start, plan.has_deep());

        // A lone sub-block runs on this thread, so its rows go over in parallel afterwards.
        let deep_rows = on_rows.filter(|_| plan.fuses_rows());

        // The deep pass defers only over replicas in place, whose rows it can hand from scratch.
        let defer = defer_deep && deep_rows.is_some() && matches!(src, Source::Replicas);

        // Phase 3: the deep pass, one task per run of contiguous sub-blocks.
        if plan.has_deep() {
            DeepPass::new(&plan, deep_rows, defer).run(self, win, src);
        }

        if let Some(sink) = on_rows.filter(|_| !plan.fuses_rows()) {
            Self::hand_over(win, &plan, sink);
        }
        (plan, defer)
    }

    /// Hand every row of the buffer to the sink, in parallel blocks of four a worker.
    fn hand_over(win: &mut Window, plan: &Plan, sink: &RowSink<'_>) {
        let (log_rows, first) = (plan.log_handover_rows(), win.first_row());
        parallel::chunks_mut(win.words_mut(), plan.num_ntts << log_rows, |i, rows| {
            sink(first + (i << log_rows), rows)
        });
    }
}
