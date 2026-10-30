//! The gathered pass: a few layers in one sweep of the buffer, one row group at a time.

use primitives::field::F64;
use primitives::stream::Stream;

use super::drain::Drain;
use super::layers::Layers;
use super::plan::Plan;
use super::scratch::with_scratch;
use super::source::Source;
use super::stage::{BATCH, Stage};
use super::window::Window;

/// One gathered pass: layers `layer..layer + g` in one sweep of the buffer, one row group at a time.
///
/// - It owns the geometry of the pass: the group, block and task sizes, and how a finished group drains.
/// - It owns its [`Source`] and, for a lane-major message, its [`Stage`].
/// - [`GatheredPass::new`] computes the geometry, and [`GatheredPass::run`] sweeps the buffer once.
///
/// # Row groups
///
/// - A group takes rows `r + i * step`, for `i < 2^g`, of one layer-`layer` block.
/// - Here `step = 2^(d - layer - g)` and the residue `r < step`.
/// - Those are exactly the rows the next `g` layers pair with each other.
///
/// ```text
///     g = 2, a 16-row block, step = 4, residue r = 1:
///
///     rows:     0  1  2  3 |  4  5  6  7 |  8  9 10 11 | 12 13 14 15
///                  ^              ^              ^              ^
///     scratch:  [ row 1, row 5, row 9, row 13 ]   ->  a 4-row transform of its own
/// ```
///
/// # Why the twiddles still match
///
/// - At layer `L`, a row's block index is `row >> (d - L)`.
/// - The residue is below `step`, so that shift drops it.
/// - The scratch transform therefore takes the same twiddles as the full one.
///
/// # Tasks
///
/// - A task is one residue over every block the buffer holds, from `first_block` on, block 0 last.
/// - With a message, it gathers the message's rows once, and every block transforms a copy of them.
/// - The message may be the buffer's block 0, so block 0 goes last.
/// - Tasks own disjoint residues, so no task reads rows another task writes.
///
/// # With a lane-major message
///
/// - Word `w` of message row `j` is word `j` of lane block `num_ntts - 1 - w`, and zero below the padding.
/// - A lane block's cache line holds [`BATCH`] consecutive rows, so a task takes that many residues.
/// - It goes one octet of lanes at a time, and the octet of the residues is 64 lanes of one transform.
/// - It transposes those lanes into a stage of `2^g` rows of 64 words, one line per residue.
/// - Each block transforms a copy of the stage and scatters it line by line.
///
/// A block's rows are its own, and the message is read before block 0 is written.
pub(super) struct GatheredPass<'a> {
    src: Source<'a>,
    /// The transpose of a lane-major message, if the source is one.
    staging: Option<Stage>,
    layer: usize,
    g: usize,
    num_ntts: usize,
    /// The first block the buffer holds, and the blocks it holds from there.
    first_block: usize,
    blocks: std::ops::Range<usize>,
    /// Rows of a layer-`layer` block, and the rows between the rows of a group.
    block_rows: usize,
    step: usize,
    /// Rows of a group, its words a row, and its words in all.
    rows: usize,
    width: usize,
    group_len: usize,
    /// Residues one task step takes, and the words of its stage.
    batch: usize,
    stage_len: usize,
    /// How a finished group drains: in pieces of `piece` words, `piece_stride` apart.
    piece: usize,
    piece_stride: usize,
    stream: bool,
}

impl<'a> GatheredPass<'a> {
    /// The geometry of the pass over layers `layer..layer + g` of `plan`, reading `src` and writing `win`.
    pub(super) fn new(plan: &Plan, win: &Window, layer: usize, g: usize, src: Source<'a>) -> Self {
        let (log_d, num_ntts) = (plan.log_d, win.num_ntts());
        // A group is 2^g rows, `step` rows apart, of a block of `block_rows` rows.
        let log_step = log_d - layer - g;
        let (rows, step, block_rows) = (1usize << g, 1usize << log_step, 1usize << (log_d - layer));
        // The blocks the buffer holds.
        let first_block = win.first_coset();
        let blocks = first_block..first_block + (win.len() / num_ntts) / block_rows;
        // A lane-major group is 64 lanes of a batch of residues, transposed into a stage: one line per residue in each row.
        let staged = matches!(src, Source::Lanes(_));
        let batch = if staged { BATCH } else { 1 };
        let width = if staged { BATCH * 8 } else { num_ntts };
        // A message that is not lane-major gathers into a stage of one group; replicas gather per block.
        let gathers = matches!(src, Source::Rows(_) | Source::InPlace);
        let group_len = rows * width;
        let stage_len = if staged || gathers { group_len } else { 0 };
        let staging = match src {
            Source::Lanes(lanes) => Some(Stage::new(&lanes, log_step, block_rows, num_ntts)),
            _ => None,
        };
        // Whole aligned cache lines in every row stream out a line at a time; other rows are stored whole.
        let stream = win.streams_lines();
        let piece = if staged || stream { 8 } else { num_ntts };
        let piece_stride = if staged { num_ntts } else { piece };
        Self {
            src,
            staging,
            layer,
            g,
            num_ntts,
            first_block,
            blocks,
            block_rows,
            step,
            rows,
            width,
            group_len,
            batch,
            stage_len,
            piece,
            piece_stride,
            stream,
        }
    }

    /// Sweep the buffer once, one task per range of residues.
    pub(super) fn run(&self, layers: Layers, win: &mut Window) {
        let base = win.base();
        let win = &*win;
        parallel::for_each_chunk(self.step / self.batch, |lo, hi| {
            with_scratch(self.stage_len + self.group_len, |all| {
                let (stage, scratch) = all.split_at_mut(self.stage_len);
                // One fence at the end of the task covers all its streaming stores.
                let stream = self.stream.then(Stream::new);
                let stream = stream.as_ref();
                for t in lo..hi {
                    match (self.src, &self.staging) {
                        (Source::Lanes(lanes), Some(staging)) => {
                            for octet in 0..self.num_ntts / 8 {
                                staging.fill(stage, lanes.words, t * self.batch, octet);
                                for block in self.blocks.clone().rev() {
                                    let r = t * self.batch;
                                    let dst = win.row(self.block_rows, block, r) + 8 * octet;
                                    self.group(layers, scratch, stream, win, base, block, r, Some(&*stage), dst);
                                }
                            }
                        }
                        _ => {
                            let msg = self.message_rows(base, win, t);
                            if let Some(msg) = msg {
                                self.gather(stage, msg);
                            }
                            for block in self.blocks.clone().rev() {
                                let dst = win.row(self.block_rows, block, t);
                                let from = msg.map(|_| &*stage);
                                self.group(layers, scratch, stream, win, base, block, t, from, dst);
                            }
                        }
                    }
                }
            });
        });
    }

    /// The first word of residue `r`'s rows in the message, or `None` if the blocks hold their own rows.
    fn message_rows(&self, base: parallel::SendPtr<F64>, win: &Window, r: usize) -> Option<*const F64> {
        let first = win.row(self.block_rows, self.first_block, r);
        match self.src {
            Source::Rows(msg) => Some(msg.as_ptr().wrapping_add(first)),
            Source::InPlace => Some(base.0.cast_const().wrapping_add(first)),
            Source::Replicas | Source::Lanes(_) => None,
        }
    }

    /// Copy the group's rows, `step` rows apart from `src` on, into `dst`.
    #[inline(always)]
    fn gather(&self, dst: &mut [F64], src: *const F64) {
        let (num_ntts, step) = (self.num_ntts, self.step);
        for (i, dst) in dst.chunks_exact_mut(num_ntts).enumerate() {
            // SAFETY:
            // - The message and the buffer both cover every row addressed here.
            // - Tasks own disjoint residues, so no other task writes these rows.
            // - Block 0 is written last, after every read of the message in it.
            dst.copy_from_slice(unsafe { std::slice::from_raw_parts(src.add(i * step * num_ntts), num_ntts) });
        }
    }

    /// Transform residue `r`'s group as layer-`layer` block `block`, and send it back to word `dst` on.
    ///
    /// The rows are `from` the stage, or gathered from the block's own rows of the buffer.
    #[allow(clippy::too_many_arguments)]
    #[inline(always)]
    fn group(
        &self,
        layers: Layers,
        scratch: &mut [F64],
        stream: Option<&Stream>,
        win: &Window,
        base: parallel::SendPtr<F64>,
        block: usize,
        r: usize,
        from: Option<&[F64]>,
        dst: usize,
    ) {
        let (layer, g, num_ntts, step) = (self.layer, self.g, self.num_ntts, self.step);
        if from.is_none() {
            // Replicas: each block transforms its own rows of the buffer.
            self.gather(
                scratch,
                base.0.cast_const().wrapping_add(win.row(self.block_rows, block, r)),
            );
        }
        layers.run(
            scratch,
            from,
            layer + g,
            self.width,
            layer,
            layer + g,
            layer,
            block,
            None,
        );
        Drain {
            // SAFETY: the group's first row lies inside the buffer.
            dst: unsafe { base.add(dst) },
            row_len: self.width,
            dst_stride: step * num_ntts,
            piece: self.piece,
            piece_stride: self.piece_stride,
            rows: self.rows,
        }
        .run(scratch, stream);
    }
}
