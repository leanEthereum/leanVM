//! A range of layers run over one sub-block of the domain.

use primitives::field::F64;

use super::kernels::{
    butterfly_interleaved_block, butterfly_interleaved_fused_2layer, butterfly_interleaved_fused_3layer,
};
use super::twiddles::Twiddles;

/// The layer sweeps, over the twiddles of the domain.
///
/// - It is a `Copy` handle on the [`Twiddles`], so every pass takes it by value, as one pointer.
/// - [`Layers::run`] runs a range of layers on one buffer, which is one sub-block of the domain.
/// - It knows no plan, message or cache budget: its callers decide what to run, and where.
#[derive(Clone, Copy)]
pub(super) struct Layers<'t>(&'t Twiddles);

impl<'t> Layers<'t> {
    pub(super) fn new(twiddles: &'t Twiddles) -> Self {
        Self(twiddles)
    }

    /// Log of the number of points of the domain.
    pub(super) fn log_domain_size(self) -> usize {
        self.0.log_domain_size()
    }
}

impl Layers<'_> {
    /// Run a range of layers over one sub-block of the domain.
    ///
    /// - The domain has `2^d` rows and splits into `2^o` equal sub-blocks.
    /// - The buffer is one of them; its index fixes the global block index, and so the twiddle, of each block.
    /// - Layers fuse into radix-8 sweeps, with radix-4 sweeps where a lone radix-2 would be left over.
    ///
    /// With `live` (sorted), blocks that hold none of those buffer rows are left alone.
    ///
    /// - Only those rows come out right: a block feeds only the rows inside it, in every later layer.
    /// - A fused sweep skips whole blocks of its first layer, so a sparse `live` prunes coarsely.
    ///
    /// With a `src` as long as `buf`, the layers run over a copy of it, which the first sweep makes.
    /// That sweep loads from `src` and stores to `buf`, and the blocks it skips are not copied.
    /// Later sweeps work inside the blocks of the first, so they never read a word that was not copied.
    #[allow(clippy::too_many_arguments)]
    pub(super) fn run(
        self,
        buf: &mut [F64],
        mut src: Option<&[F64]>,
        log_d: usize,
        num_ntts: usize,
        first_layer: usize,
        end_layer: usize,
        outer_log: usize,
        sub_idx: usize,
        live: Option<&[usize]>,
    ) {
        if let Some(src) = src.filter(|_| first_layer >= end_layer) {
            buf.copy_from_slice(src);
        }
        let mut layer = first_layer;
        while layer < end_layer {
            // This layer's blocks inside the buffer: how many, and their size in rows and words.
            let num_blocks_in_buf = 1usize << (layer - outer_log);
            let block_size = 1usize << (log_d - layer);
            let block_elems = block_size * num_ntts;
            // A block's index in the whole domain, which picks its twiddle.
            let global = |block_in_buf: usize| sub_idx * num_blocks_in_buf + block_in_buf;

            let radix = radix_layers(end_layer - layer);
            if radix == 3 {
                // One radix-8 sweep.
                let eighth = block_size >> 3;
                for_each_block(num_blocks_in_buf, log_d - layer, live, |block_in_buf| {
                    let t = self.0.radix8(layer, global(block_in_buf));
                    let start = block_in_buf * block_elems;
                    butterfly_interleaved_fused_3layer(
                        &mut buf[start..start + block_elems],
                        src.map(|s| &s[start..start + block_elems]),
                        &t,
                        eighth,
                        num_ntts,
                    );
                });
                layer += 3;
            } else if radix == 2 {
                // One radix-4 sweep.
                let quarter = block_size >> 2;
                for_each_block(num_blocks_in_buf, log_d - layer, live, |block_in_buf| {
                    let global_block = global(block_in_buf);
                    let t = [
                        self.0.twiddle(layer, global_block),
                        self.0.twiddle(layer + 1, 2 * global_block),
                        self.0.twiddle(layer + 1, 2 * global_block + 1),
                    ];
                    let start = block_in_buf * block_elems;
                    butterfly_interleaved_fused_2layer(
                        &mut buf[start..start + block_elems],
                        src.map(|s| &s[start..start + block_elems]),
                        &t,
                        quarter,
                        num_ntts,
                    );
                });
                layer += 2;
            } else {
                // One layer: a plain butterfly sweep.
                let block_size_half = block_size >> 1;
                for_each_block(num_blocks_in_buf, log_d - layer, live, |block_in_buf| {
                    let twiddle = self.0.twiddle(layer, global(block_in_buf));
                    let start = block_in_buf * block_elems;
                    // A lone layer is rare: its block is copied before it runs, not fused with it.
                    if let Some(src) = src {
                        buf[start..start + block_elems].copy_from_slice(&src[start..start + block_elems]);
                    }
                    butterfly_interleaved_block(
                        &mut buf[start..start + block_elems],
                        twiddle,
                        block_size_half,
                        num_ntts,
                    );
                });
                layer += 1;
            }
            src = None;
        }
    }
}

/// Call `f` with each block of `1 << log_rows` rows that holds a row of `live` (sorted).
/// With no `live`, call it with every block of `num_blocks`.
fn for_each_block(num_blocks: usize, log_rows: usize, live: Option<&[usize]>, mut f: impl FnMut(usize)) {
    match live {
        None => (0..num_blocks).for_each(f),
        Some(rows) => rows
            .chunk_by(|a, b| a >> log_rows == b >> log_rows)
            .for_each(|run| f(run[0] >> log_rows)),
    }
}

/// How many layers the next sweep fuses, with `left` layers still to run.
///
/// - Radix 8 while three or more remain, but never leave one layer for a lone radix-2 sweep.
/// - A radix-2 sweep costs more per layer than a radix-4 one, and a radix-4 sweep more than a radix-8 one.
/// - So when one layer would be left over, a radix-4 sweep goes first and another ends the run.
/// - A block of the next sweep's first layer has `2^left` rows or more, so it always fits the radix.
pub(super) fn radix_layers(left: usize) -> usize {
    if left >= 4 && left % 3 == 1 { 2 } else { left.min(3) }
}
