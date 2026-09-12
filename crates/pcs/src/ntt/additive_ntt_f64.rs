//! Additive NTT over GF(2^64) using the LCH novel polynomial basis: the
//! encoding layer of the 64-bit transition (commitments over K = F_{2^64}).
//!
//! The transform uses the same subspace-polynomial construction,
//! neighbors-last layer ordering, and SoA interleaved layout as the
//! extension-field transform. Its inner butterflies use architecture-specific
//! SIMD kernels where available; large transforms are memory-bandwidth bound.

use primitives::field::F64;
use primitives::log2_strict_usize;

/// Normalized subspace-polynomial evaluation table (see the extension-field twin).
fn generate_evals_from_subspace(basis: &[F64]) -> Vec<Vec<F64>> {
    let l = basis.len();
    let mut evals: Vec<Vec<F64>> = Vec::with_capacity(l);
    evals.push(basis.to_vec());
    for i in 1..l {
        let mut row = Vec::with_capacity(l - i);
        for k in 1..evals[i - 1].len() {
            let val = evals[i - 1][k] * (evals[i - 1][k] + evals[i - 1][0]);
            row.push(val);
        }
        evals.push(row);
    }
    for row in evals.iter_mut() {
        let inv = row[0].inv();
        for v in row.iter_mut() {
            *v *= inv;
        }
    }
    evals
}

/// `Σ_j bit_j(idx) · basis[j]`.
#[inline]
fn span_get(basis: &[F64], idx: usize) -> F64 {
    let mut acc = F64::ZERO;
    for (j, &b) in basis.iter().enumerate() {
        if (idx >> j) & 1 == 1 {
            acc += b;
        }
    }
    acc
}

/// Additive NTT over F_{2^64} with the standard polynomial-basis subspace
/// `{1, x, x², …}`: the F_2-subspace is `{0, 1, …, 2^ℓ−1}` under the natural
/// integer encoding, exactly as in the extension-field version (whose domain already
/// lived inside this very subfield).
#[derive(Clone, Debug)]
pub struct AdditiveNttF64 {
    evals: Vec<Vec<F64>>,
}

impl AdditiveNttF64 {
    fn new(basis: &[F64]) -> Self {
        Self {
            evals: generate_evals_from_subspace(basis),
        }
    }

    /// Standard NTT with basis `{1, x, …, x^(dim-1)}`. Requires `dim ≤ 63` so
    /// the evaluation domain (and the twiddles) stay inside F_{2^64} without
    /// wrap; far beyond any codeword size in use.
    pub fn standard(dim: usize) -> Self {
        assert!(dim <= 63, "standard NTT requires dim ≤ 63");
        let basis: Vec<F64> = (0..dim).map(|i| F64(1u64 << i)).collect();
        Self::new(&basis)
    }

    pub fn log_domain_size(&self) -> usize {
        self.evals.len()
    }

    /// Twiddle at `(layer, block)`; see the extension-field twin for the convention.
    pub fn twiddle(&self, layer: usize, block: usize) -> F64 {
        let v = &self.evals[self.log_domain_size() - layer - 1];
        span_get(&v[1..], block)
    }

    /// The seven twiddles a radix-8 group needs, breadth-first: layer `layer`,
    /// then `layer + 1` (one per half), then `layer + 2` (one per quarter).
    ///
    /// `span_get` is F_2-linear in the block index, so the six deeper twiddles are
    /// the block's own contribution plus a fixed correction per sub-block index:
    /// one scan of the three basis rows replaces seven.
    pub(crate) fn twiddles_radix8(&self, layer: usize, block: usize) -> [F64; 7] {
        let l = self.log_domain_size();
        let (v0, v1, v2) = (
            &self.evals[l - layer - 1],
            &self.evals[l - layer - 2],
            &self.evals[l - layer - 3],
        );
        let (mut t0, mut a, mut c) = (F64::ZERO, F64::ZERO, F64::ZERO);
        for j in 0..layer {
            if (block >> j) & 1 == 1 {
                t0 += v0[1 + j];
                a += v1[2 + j];
                c += v2[3 + j];
            }
        }
        let (d, e0, e1) = (v1[1], v2[1], v2[2]);
        [t0, a, a + d, c, c + e0, c + e1, c + e0 + e1]
    }

    /// The `2^j - 1` twiddles a radix-`2^j` group needs, breadth-first: sub-layer
    /// `d` contributes its `2^d` at `out[2^d - 1 ..]`. Generalizes
    /// [`twiddles_radix8`](Self::twiddles_radix8) to any width.
    ///
    /// `span_get` is F_2-linear in the block index, so a sub-layer's twiddles are
    /// the block's own contribution plus a subset sum of the `d` basis elements
    /// the sub-index selects: one scan of each basis row, then XOR-doubling.
    fn twiddles_radix(&self, layer: usize, block: usize, j: usize, out: &mut [F64]) {
        let l = self.log_domain_size();
        for d in 0..j {
            let v = &self.evals[l - layer - d - 1];
            let mut base = F64::ZERO;
            for k in 0..layer {
                if (block >> k) & 1 == 1 {
                    base += v[1 + d + k];
                }
            }
            let dst = &mut out[(1 << d) - 1..][..1 << d];
            dst[0] = base;
            for k in 0..d {
                let (done, rest) = dst.split_at_mut(1 << k);
                for (slot, &seen) in rest.iter_mut().zip(done.iter()) {
                    *slot = seen + v[1 + k];
                }
            }
        }
    }

    /// Forward additive NTT in place (scalar; used directly for tests and as
    /// the small-input path).
    pub fn forward_transform_scalar(&self, data: &mut [F64]) {
        let log_d = log2_strict_usize(data.len());
        assert!(log_d <= self.log_domain_size());
        for layer in 0..log_d {
            let num_blocks = 1usize << layer;
            let block_size_half = 1usize << (log_d - layer - 1);
            for block in 0..num_blocks {
                let twiddle = self.twiddle(layer, block);
                let block_start = block << (log_d - layer);
                for idx0 in block_start..(block_start + block_size_half) {
                    let idx1 = idx0 | block_size_half;
                    let v = data[idx1];
                    let new_u = data[idx0] + v * twiddle;
                    data[idx0] = new_u;
                    data[idx1] = v + new_u;
                }
            }
        }
    }

    /// How many leading layers sweep the whole buffer before the rest run as cache-resident sub-NTTs.
    ///
    /// Round the position size up because padding-free commitments need not have a power-of-two lane count.
    pub(crate) fn cache_split(log_d: usize, num_ntts: usize) -> usize {
        const TARGET_SUBGROUP_LOG_BYTES: usize = 21;
        let log_bytes_per_position = 3 + num_ntts.next_power_of_two().ilog2() as usize;
        let target_log_positions = TARGET_SUBGROUP_LOG_BYTES.saturating_sub(log_bytes_per_position);
        let cache_n_top = log_d.saturating_sub(target_log_positions);

        const PARALLEL_FLOOR_LOG_D: usize = 12;
        const MIN_SUB_LOG: usize = 8;
        if log_d >= PARALLEL_FLOOR_LOG_D {
            let want_subs_log = log2_strict_usize(parallel::num_threads().next_power_of_two());
            let max_n_top = log_d.saturating_sub(MIN_SUB_LOG);
            cache_n_top.max(want_subs_log.min(max_n_top))
        } else {
            cache_n_top
        }
    }

    /// RS-encode the message already sitting in the codeword's own first replica,
    /// `data[..data.len() >> log_inv_rate]`: `data` becomes `2^log_inv_rate`
    /// replicas of it, transformed from layer `log_inv_rate`.
    ///
    /// The message is read ROW-major (`data[row * num_ntts + lane]`), which is what
    /// [`transpose_lane_major`] writes there for a lane-major caller. That transpose
    /// stays a pass of its own because it wants one long contiguous run per lane
    /// while a radix-8 group wants eight row windows at once, so fusing the two would
    /// put `8 * num_ntts` message streams in flight. Separating them costs one extra
    /// read and write of the message rather than of the whole codeword.
    ///
    /// The replication is fused into the first pass. Each block at layer
    /// `log_inv_rate` IS one replica, so a block's participating rows are
    /// message rows, and the pass can gather them itself instead of reading back a
    /// codeword someone else just filled. Each transformed window is published
    /// once. Replica 0 IS the message,
    /// so the blocks run in descending order and it is transformed in place last,
    /// once every other replica has read it.
    ///
    /// On x86 the first pass gathers up to 128 rows, tiling columns to keep its
    /// scratch in L1, and publishes each output window once with streaming stores.
    /// Falls back to replicating and transforming for tiny transforms or a rate
    /// deep enough to leave fewer than three whole-buffer layers.
    pub fn encode_interleaved_in_place(&self, data: &mut [F64], num_ntts: usize, log_inv_rate: usize) {
        self.encode_interleaved_with_output(data, num_ntts, log_inv_rate, |_, _| {});
    }

    /// Publish each complete row interval once, with its starting row index.
    /// Callbacks can run on pool workers and must not dispatch nested work.
    pub(crate) fn encode_interleaved_with_output(
        &self,
        data: &mut [F64],
        num_ntts: usize,
        log_inv_rate: usize,
        output: impl Fn(usize, &[F64]) + Sync,
    ) {
        assert!(num_ntts > 0);
        assert_eq!(data.len() % num_ntts, 0);
        let log_d = log2_strict_usize(data.len() / num_ntts);
        let n_top = Self::cache_split(log_d, num_ntts);
        let block_rows = 1usize << (log_d - log_inv_rate);
        let msg_len = data.len() >> log_inv_rate;

        if n_top == 0 || log_d < 8 || log_inv_rate + 2 >= n_top || block_rows < 8 {
            replicate_in_place(data, msg_len);
            self.forward_interleaved_with_output(data, num_ntts, log_inv_rate, output);
            return;
        }

        #[cfg(target_arch = "x86_64")]
        {
            let log_radix = (n_top - log_inv_rate).min(7);
            self.encode_first_pass(data, num_ntts, log_inv_rate, log_radix);
            self.forward_interleaved_with_output(data, num_ntts, log_inv_rate + log_radix, output);
        }
        #[cfg(not(target_arch = "x86_64"))]
        {
            let dst = parallel::SendPtr(data.as_mut_ptr());
            let eighth = block_rows >> 3;
            let tw: Vec<[F64; 7]> = (0..1usize << log_inv_rate)
                .map(|block| self.twiddles_radix8(log_inv_rate, block))
                .collect();
            parallel::for_each(eighth, |r| {
                for (block, t) in tw.iter().enumerate().rev() {
                    let base = (block * block_rows + r) * num_ntts;
                    // SAFETY: row group `r` of block `block` owns the eight windows
                    // `base + i * eighth * num_ntts`, disjoint across `r` and across
                    // blocks, and `data` outlives the dispatch.
                    let mut rows: [&mut [F64]; 8] =
                        std::array::from_fn(|i| unsafe { dst.slice(base + i * eighth * num_ntts, num_ntts) });
                    if block > 0 {
                        // Replica 0 still holds the message: read it, and note that this
                        // loop reaches block 0 last, so no replica reads it transformed.
                        for (i, row) in rows.iter_mut().enumerate() {
                            // SAFETY: the message region is `data[..msg_len]`, read-only
                            // until block 0 transforms it in place below.
                            let src = unsafe { dst.slice((i * eighth + r) * num_ntts, num_ntts) };
                            row.copy_from_slice(src);
                        }
                    }
                    radix8_butterflies(&mut rows, t);
                }
            });
            self.forward_interleaved_with_output(data, num_ntts, log_inv_rate + 3, output);
        }
    }

    #[cfg(target_arch = "x86_64")]
    fn encode_first_pass(&self, data: &mut [F64], num_ntts: usize, log_inv_rate: usize, log_radix: usize) {
        assert!((3..=7).contains(&log_radix));
        let block_rows = (data.len() / num_ntts) >> log_inv_rate;
        let dst = parallel::SendPtr(data.as_mut_ptr());
        const STAGE_WORDS: usize = 4096;
        let rows = 1usize << log_radix;
        assert!(block_rows >= rows);
        let step = block_rows >> log_radix;
        let stage_lanes = STAGE_WORDS / rows;
        let tw: Vec<Vec<F64>> = (0..1usize << log_inv_rate)
            .map(|block| {
                let mut tw = vec![F64::ZERO; rows - 1];
                self.twiddles_radix(log_inv_rate, block, log_radix, &mut tw);
                tw
            })
            .collect();
        parallel::for_each_chunk(step, |lo, hi| {
            let mut stage = [F64::ZERO; STAGE_WORDS];
            let stream = primitives::stream::Stream::new();
            for r in lo..hi {
                for lane in (0..num_ntts).step_by(stage_lanes) {
                    let len = (num_ntts - lane).min(stage_lanes);
                    for (block, tw) in tw.iter().enumerate().rev() {
                        for i in 0..rows {
                            // SAFETY: replica zero remains the source until this
                            // group's last iteration, and groups own distinct rows.
                            let src = unsafe { dst.slice((i * step + r) * num_ntts + lane, len) };
                            stage[i * len..][..len].copy_from_slice(src);
                        }
                        radix_butterflies(&mut stage[..rows * len], len, log_radix, tw);
                        for i in 0..rows {
                            let base = (block * block_rows + i * step + r) * num_ntts + lane;
                            // SAFETY: this group owns each output window, which is
                            // read again after the dispatch's streaming stores finish.
                            stream.copy(unsafe { dst.slice(base, len) }, &stage[i * len..][..len]);
                        }
                    }
                }
            }
        });
    }

    /// Scalar reference for the interleaved forward NTT (test oracle).
    pub fn forward_transform_interleaved_scalar_from_layer(
        &self,
        data: &mut [F64],
        num_ntts: usize,
        start_layer: usize,
    ) {
        let n_total = data.len();
        let log_d = log2_strict_usize(n_total / num_ntts);

        for layer in start_layer..log_d {
            let num_blocks = 1usize << layer;
            let block_size = 1usize << (log_d - layer);
            let block_size_half = block_size >> 1;
            let block_elems = block_size * num_ntts;
            for block in 0..num_blocks {
                let twiddle = self.twiddle(layer, block);
                let block_start = block * block_elems;
                for row in 0..block_size_half {
                    let off_top = block_start + row * num_ntts;
                    let off_bot = off_top + block_size_half * num_ntts;
                    for lane in 0..num_ntts {
                        let v = data[off_bot + lane];
                        let new_u = data[off_top + lane] + v * twiddle;
                        data[off_top + lane] = new_u;
                        data[off_bot + lane] = v + new_u;
                    }
                }
            }
        }
    }

    /// Parallel interleaved (SoA) forward NTT of `num_ntts` independent lanes sharing
    /// the twiddle structure (`data[pos * num_ntts + lane]`, so one Merkle leaf is one
    /// position, a contiguous slice of `num_ntts` F_{2^64} elements), starting at
    /// `start_layer`: the RS-encoding caller replicates the message into all `2^rate`
    /// sub-blocks, which IS the exact post-layer-`rate` state, and skips those layers
    /// here.
    ///
    /// Cache-blocked like the extension-field twin: top layers sweep the full buffer
    /// row-parallel, deep layers run as cache-resident sub-NTTs one per worker. Both
    /// phases fuse up to three layers per pass, so the pass count, which is what a
    /// memory-bound transform pays, is a third of the layer count. Constants are
    /// re-derived for 8-byte elements.
    pub fn forward_transform_interleaved_parallel_from_layer(
        &self,
        data: &mut [F64],
        num_ntts: usize,
        start_layer: usize,
    ) {
        self.forward_interleaved_with_output(data, num_ntts, start_layer, |_, _| {});
    }

    fn forward_interleaved_with_output(
        &self,
        data: &mut [F64],
        num_ntts: usize,
        start_layer: usize,
        output: impl Fn(usize, &[F64]) + Sync,
    ) {
        // `num_ntts` is a plain interleaving stride here: a padding-free L0
        // commitment interleaves only the lanes that carry data, so it is not a
        // power of two, while `n_total / num_ntts` (the transform's domain) still is.
        assert!(num_ntts > 0);
        let n_total = data.len();
        assert_eq!(n_total % num_ntts, 0);
        let log_d = log2_strict_usize(n_total / num_ntts);
        assert!(log_d <= self.log_domain_size());
        assert!(start_layer <= log_d);

        let n_top = Self::cache_split(log_d, num_ntts);
        if n_top == 0 || log_d < 8 {
            self.forward_transform_interleaved_scalar_from_layer(data, num_ntts, start_layer);
            output(0, data);
            return;
        }

        // Top layers: whole-buffer sweeps, and the pass count is what sets the cost
        // up here, so they go as wide as one scratch group allows.
        self.run_top_layers(data, log_d, num_ntts, start_layer.min(n_top), n_top);

        // Deep layers: one sub-NTT per worker, each over a cache-resident
        // sub-block. Layers fuse here for the same reason they do above, only the
        // pass being saved is over L2/L3 rather than DRAM: a sub is a couple of
        // megabytes, so twelve single-layer sweeps re-read it twelve times. The
        // row loop inside a fused kernel stays serial, since the parallelism is
        // already spent on the subs and a nested dispatch would deadlock.
        let sub_elems = (1usize << (log_d - n_top)) * num_ntts;
        parallel::chunks_mut(data, sub_elems, |sub_idx, sub_data| {
            self.run_layers(
                sub_data,
                log_d,
                num_ntts,
                n_top.max(start_layer),
                log_d,
                n_top,
                sub_idx,
                false,
            );
            output(sub_idx * (sub_elems / num_ntts), sub_data);
        });
    }

    /// Run layers `first_layer..end_layer` over `buf`, which holds the blocks of
    /// Run the whole-buffer layers through gathered groups, avoiding cache-set aliasing between widely spaced rows.
    fn run_top_layers(&self, buf: &mut [F64], log_d: usize, num_ntts: usize, first_layer: usize, end_layer: usize) {
        /// Words of scratch per row group, so a group stays inside L1.
        const GROUP_WORDS: usize = 4096;
        /// Widest gathered radix, and so the size of a group's twiddle set.
        const MAX_LOG_RADIX: usize = 6;
        /// Below this width the gather costs more than the pass it saves, and
        /// [`run_layers`]'s in-place kernels are the better shape.
        const MIN_LOG_RADIX: usize = 4;

        let mut layer = first_layer;
        while layer < end_layer {
            let j = (end_layer - layer)
                .min(MAX_LOG_RADIX)
                .min((GROUP_WORDS / num_ntts).ilog2() as usize)
                .min(log_d - layer);
            if j < MIN_LOG_RADIX {
                self.run_layers(buf, log_d, num_ntts, layer, end_layer, 0, 0, true);
                return;
            }
            let log_step = log_d - layer - j;
            let (rows, step) = (1usize << j, 1usize << log_step);
            let base = parallel::SendPtr(buf.as_mut_ptr());
            parallel::for_each_chunk(1usize << (log_d - j), |lo, hi| {
                let mut scratch = [F64::ZERO; GROUP_WORDS];
                let mut tw = [F64::ZERO; (1 << MAX_LOG_RADIX) - 1];
                let mut built = usize::MAX;
                for g in lo..hi {
                    let (block, r) = (g >> log_step, g & (step - 1));
                    if built != block {
                        self.twiddles_radix(layer, block, j, &mut tw);
                        built = block;
                    }
                    // The group's rows, `block_size` apart in blocks and `step`
                    // apart within one.
                    let row = |i: usize| ((block << (log_d - layer)) + r + i * step) * num_ntts;
                    // SAFETY: distinct `g` name disjoint row sets (distinct `r`
                    // within a block, distinct blocks across), every one in
                    // bounds, and `buf` stays borrowed for the whole dispatch.
                    for i in 0..rows {
                        scratch[i * num_ntts..][..num_ntts].copy_from_slice(unsafe { base.slice(row(i), num_ntts) });
                    }
                    radix_butterflies(&mut scratch[..rows * num_ntts], num_ntts, j, &tw);
                    for i in 0..rows {
                        unsafe { base.slice(row(i), num_ntts) }.copy_from_slice(&scratch[i * num_ntts..][..num_ntts]);
                    }
                }
            });
            layer += j;
        }
    }

    fn run_layers(
        &self,
        buf: &mut [F64],
        log_d: usize,
        num_ntts: usize,
        first_layer: usize,
        end_layer: usize,
        outer_log: usize,
        sub_idx: usize,
        par_rows: bool,
    ) {
        let mut layer = first_layer;
        while layer < end_layer {
            let num_blocks_in_buf = 1usize << (layer - outer_log);
            let block_size = 1usize << (log_d - layer);
            let block_elems = block_size * num_ntts;
            let global = |block_in_buf: usize| sub_idx * num_blocks_in_buf + block_in_buf;

            if layer + 2 < end_layer && block_size >= 8 {
                let eighth = block_size >> 3;
                for block_in_buf in 0..num_blocks_in_buf {
                    let t = self.twiddles_radix8(layer, global(block_in_buf));
                    let start = block_in_buf * block_elems;
                    butterfly_interleaved_fused_3layer(
                        &mut buf[start..start + block_elems],
                        &t,
                        eighth,
                        num_ntts,
                        par_rows,
                    );
                }
                layer += 3;
            } else if layer + 1 < end_layer && block_size >= 4 {
                let quarter = block_size >> 2;
                for block_in_buf in 0..num_blocks_in_buf {
                    let global_block = global(block_in_buf);
                    let t_outer = self.twiddle(layer, global_block);
                    let t_inner_a = self.twiddle(layer + 1, 2 * global_block);
                    let t_inner_b = self.twiddle(layer + 1, 2 * global_block + 1);
                    let start = block_in_buf * block_elems;
                    butterfly_interleaved_fused_2layer(
                        &mut buf[start..start + block_elems],
                        t_outer,
                        t_inner_a,
                        t_inner_b,
                        quarter,
                        num_ntts,
                        par_rows,
                    );
                }
                layer += 2;
            } else {
                let block_size_half = block_size >> 1;
                for block_in_buf in 0..num_blocks_in_buf {
                    let twiddle = self.twiddle(layer, global(block_in_buf));
                    let start = block_in_buf * block_elems;
                    let block = &mut buf[start..start + block_elems];
                    if par_rows {
                        butterfly_interleaved_block_par_rows(block, twiddle, block_size_half, num_ntts);
                    } else {
                        butterfly_interleaved_block(block, twiddle, block_size_half, num_ntts);
                    }
                }
                layer += 1;
            }
        }
    }

    /// Recover novel-basis coefficients from evaluations with a scalar inverse NTT.
    pub fn inverse_transform(&self, data: &mut [F64]) {
        let log_d = log2_strict_usize(data.len());
        assert!(log_d <= self.log_domain_size());
        for layer in (0..log_d).rev() {
            let num_blocks = 1usize << layer;
            let block_size_half = 1usize << (log_d - layer - 1);
            for block in 0..num_blocks {
                let twiddle = self.twiddle(layer, block);
                let block_start = block << (log_d - layer);
                for idx0 in block_start..(block_start + block_size_half) {
                    let idx1 = idx0 | block_size_half;
                    let u = data[idx0];
                    let new_v = data[idx1] + u;
                    data[idx1] = new_v;
                    data[idx0] = u + new_v * twiddle;
                }
            }
        }
    }
}

fn butterfly_interleaved_block_par_rows(block: &mut [F64], twiddle: F64, block_size_half: usize, num_ntts: usize) {
    const PARALLEL_ROW_THRESHOLD: usize = 1024;
    if block_size_half < PARALLEL_ROW_THRESHOLD {
        butterfly_interleaved_block(block, twiddle, block_size_half, num_ntts);
        return;
    }
    let half_offset = block_size_half * num_ntts;
    let (top, bot) = block.split_at_mut(half_offset);
    let bot_base = parallel::SendPtr(bot.as_mut_ptr());
    parallel::chunks_mut(top, num_ntts, |r, top_row| {
        // SAFETY: distinct `r` take disjoint `num_ntts`-windows of `bot`, the
        // same windows `chunks_mut` just proved disjoint in `top`; the two halves
        // are themselves disjoint by `split_at_mut`.
        let bot_row = unsafe { bot_base.slice(r * num_ntts, top_row.len()) };
        butterfly_lanes(top_row, bot_row, twiddle);
    });
}

/// Run `do_one` over every row group of a fused multi-layer block: `block` is
/// `N * stride_rows * num_ntts` elements, and group `r` owns the `N` windows
/// `block[i * stride + r * num_ntts .. + num_ntts]` for `i` in `0..N`.
/// Distinct `r` give disjoint windows within each slab, and the slabs are
/// disjoint by construction, so the groups are pairwise disjoint, which is what
/// makes one pointer plus an index sound where `N` nested `split_at_mut`s would
/// be needed to say the same thing.
fn fused_rows<const N: usize>(
    block: &mut [F64],
    stride_rows: usize,
    num_ntts: usize,
    par_rows: bool,
    do_one: impl Fn(&mut [&mut [F64]; N]) + Sync,
) {
    const PARALLEL_ROW_THRESHOLD: usize = 512;
    let stride = stride_rows * num_ntts;
    debug_assert_eq!(block.len(), N * stride);

    let base = parallel::SendPtr(block.as_mut_ptr());
    let group = |r: usize| {
        let off = r * num_ntts;
        // SAFETY: see the disjointness argument above; `off + num_ntts <= stride`
        // because `r < stride_rows`.
        let mut rows: [&mut [F64]; N] = std::array::from_fn(|i| unsafe { base.slice(i * stride + off, num_ntts) });
        do_one(&mut rows);
    };

    if !par_rows || stride_rows < PARALLEL_ROW_THRESHOLD {
        for r in 0..stride_rows {
            group(r);
        }
    } else {
        parallel::for_each(stride_rows, group);
    }
}

/// Fused three-layer (radix-8) butterfly over one layer-L block: applies
/// layers L, L+1 and L+2 in a single pass over the block's rows, instead of
/// the three full-buffer sweeps they would otherwise cost.
///
/// The eight participating rows stay L1-resident across all twelve
/// butterflies, exactly as the four rows do in the fused-2 kernel; each
/// butterfly is the same lane kernel, already 8-wide on NEON and AVX-512.
///
/// `block` is `8 * eighth * num_ntts` elements. For each `r ∈ 0..eighth` the
/// rows `r + i·eighth` for `i ∈ 0..8` participate. Layer L pairs them at
/// distance `4·eighth`, layer L+1 at `2·eighth`, layer L+2 at `eighth`.
/// `t` holds the seven twiddles breadth-first: `t[0]` is layer L, `t[1..3]`
/// layer L+1 (one per half), `t[3..7]` layer L+2 (one per quarter).
fn butterfly_interleaved_fused_3layer(block: &mut [F64], t: &[F64; 7], eighth: usize, num_ntts: usize, par_rows: bool) {
    fused_rows::<8>(block, eighth, num_ntts, par_rows, |rows| radix8_butterflies(rows, t));
}

/// The `2^j - 1` butterflies of a gathered radix-`2^j` group, whose `2^j` rows
/// are contiguous in `rows`. Sub-layer `d` pairs them at distance `2^(j-1-d)`
/// and takes its twiddle from the breadth-first set
/// [`twiddles_radix`](AdditiveNttF64::twiddles_radix) built; `j = 3` is exactly
/// [`radix8_butterflies`] with its rows gathered.
fn radix_butterflies(rows: &mut [F64], num_ntts: usize, j: usize, tw: &[F64]) {
    for d in 0..j {
        let dist = 1usize << (j - 1 - d);
        let base = (1usize << d) - 1;
        for i in (0..1usize << j).filter(|i| i & dist == 0) {
            let (top, bot) = rows.split_at_mut((i + dist) * num_ntts);
            let top = &mut top[i * num_ntts..(i + 1) * num_ntts];
            butterfly_lanes(top, &mut bot[..num_ntts], tw[base + (i >> (j - d))]);
        }
    }
}

/// The twelve butterflies of one radix-8 row group: layer L pairs the rows at
/// distance 4, L+1 at 2, L+2 at 1, with `t` holding the seven twiddles
/// breadth-first. Shared with [`AdditiveNttF64::encode_interleaved_in_place`], whose
/// first pass gathers its rows from the message rather than finding them in place.
#[inline(always)]
fn radix8_butterflies(rows: &mut [&mut [F64]; 8], t: &[F64; 7]) {
    let [r0, r1, r2, r3, r4, r5, r6, r7] = rows;
    // Layer L, distance 4·eighth.
    butterfly_lanes(r0, r4, t[0]);
    butterfly_lanes(r1, r5, t[0]);
    butterfly_lanes(r2, r6, t[0]);
    butterfly_lanes(r3, r7, t[0]);
    // Layer L+1, distance 2·eighth: t[1] on the new top half, t[2] on the new
    // bottom half.
    butterfly_lanes(r0, r2, t[1]);
    butterfly_lanes(r1, r3, t[1]);
    butterfly_lanes(r4, r6, t[2]);
    butterfly_lanes(r5, r7, t[2]);
    // Layer L+2, distance eighth: one twiddle per quarter.
    butterfly_lanes(r0, r1, t[3]);
    butterfly_lanes(r2, r3, t[4]);
    butterfly_lanes(r4, r5, t[5]);
    butterfly_lanes(r6, r7, t[6]);
}

/// Transpose a **lane-major message** into the interleaved order
/// [`AdditiveNttF64::encode_interleaved_in_place`] reads, writing it to the
/// codeword's own message region: lane `l`'s block is
/// `msg[l << log_rows ..][..1 << log_rows]`, and codeword lane `t` takes block
/// `n_lanes - 1 - t`. Pure data movement, independent of the transform's domain.
///
/// `n_lanes` is arbitrary, because the caller commits only the lanes that carry
/// data: the stacked witness's zero tail is whole lanes and is simply absent.
///
/// The DESCENDING direction is the PCS's leaf-image order: a leaf reads its lanes
/// from the top interleaving index downwards, so the absent lanes land at the FRONT
/// of the image, where their hash prefix is one chaining value every leaf shares
/// ([`crate::merkle::merkle_tree_padded_rows`]) and where they can be left out of
/// the proof. Which block feeds which lane is free here (each lane is an independent
/// codeword), so the convention costs nothing.
///
/// Blocked by row tile: each lane contributes a burst of contiguous words, and the
/// tile is written straight into its own contiguous run of `out`, which is
/// L1-resident while it fills. That is what keeps an `n_lanes`-way gather at
/// `2^log_rows` stride near bandwidth.
pub fn transpose_lane_major(out: &mut [F64], msg: &[F64], n_lanes: usize, log_rows: usize) {
    let rows = 1usize << log_rows;
    assert!(n_lanes > 0, "a commitment needs at least one lane");
    assert_eq!(msg.len(), n_lanes * rows, "message is n_lanes contiguous lane blocks");
    assert_eq!(out.len(), msg.len(), "the transpose is the same words, reordered");

    /// Words per cache-resident row tile.
    const TILE_WORDS: usize = 4096;
    assert!(n_lanes <= TILE_WORDS, "a codeword row must fit the transpose tile");
    // Largest power-of-two row count whose tile fits: both it and `rows` are then
    // powers of two, so the tiles cover every row. They have to: this is the sole
    // initializer of an uninitialized codeword's message region, and a truncating
    // tile count would leave the tail reading the previous phase's plausible bytes,
    // whose symptom is a proof that stops verifying rather than a crash.
    let tile_rows = (1usize << (TILE_WORDS / n_lanes).ilog2()).min(rows);
    assert_eq!(rows % tile_rows, 0, "row tiles must cover every row");

    parallel::chunks_mut(out, tile_rows * n_lanes, |t, tile| {
        let r0 = t * tile_rows;
        for lane in 0..n_lanes {
            let block = n_lanes - 1 - lane;
            let src = &msg[block * rows + r0..][..tile_rows];
            for (slot, &word) in tile[lane..].iter_mut().step_by(n_lanes).zip(src) {
                *slot = word;
            }
        }
    });
}

/// Fill the rest of `data` with copies of its first `msg_len` elements: the un-fused
/// form of [`AdditiveNttF64::encode_interleaved_in_place`]'s first pass.
fn replicate_in_place(data: &mut [F64], msg_len: usize) {
    let (msg, rest) = data.split_at_mut(msg_len);
    for replica in rest.chunks_mut(msg_len) {
        replica.copy_from_slice(msg);
    }
}

/// [`replicate_in_place`] from a message that lives elsewhere. Test oracle.
#[cfg(test)]
fn replicate_rows(data: &mut [F64], msg: &[F64]) {
    data[..msg.len()].copy_from_slice(msg);
    replicate_in_place(data, msg.len());
}

/// Fused 2-layer butterfly, row-parallel; see the extension-field twin for the shape.
fn butterfly_interleaved_fused_2layer(
    block: &mut [F64],
    t_outer: F64,
    t_inner_a: F64,
    t_inner_b: F64,
    quarter: usize,
    num_ntts: usize,
    par_rows: bool,
) {
    fused_rows::<4>(block, quarter, num_ntts, par_rows, |rows| {
        let [row_a, row_b, row_c, row_d] = rows;
        // Layer L butterflies (a,c) and (b,d), then layer L+1 (a,b) and
        // (c,d); each stage runs the NEON lane-pair kernel over the rows.
        butterfly_lanes(row_a, row_c, t_outer);
        butterfly_lanes(row_b, row_d, t_outer);
        butterfly_lanes(row_a, row_b, t_inner_a);
        butterfly_lanes(row_c, row_d, t_inner_b);
    });
}

#[inline]
fn butterfly_interleaved_block(block: &mut [F64], twiddle: F64, block_size_half: usize, num_ntts: usize) {
    let half_offset = block_size_half * num_ntts;
    let (top, bot) = block.split_at_mut(half_offset);
    for r in 0..block_size_half {
        let off = r * num_ntts;
        butterfly_lanes(&mut top[off..off + num_ntts], &mut bot[off..off + num_ntts], twiddle);
    }
}

/// Butterfly all `num_ntts` lanes of one (top row, bottom row) pair with a
/// shared twiddle: new_u = u + v*t; new_v = v + new_u.
///
/// On NEON this processes eight lanes per iteration. Four independent pair
/// reductions stay in the vector register file, exposing their PMULL chains
/// in parallel and amortizing the loop branch and constant setup. The pair
/// kernel handles a short even tail, and the scalar path handles an odd tail.
#[inline]
fn butterfly_lanes(top: &mut [F64], bot: &mut [F64], twiddle: F64) {
    debug_assert_eq!(top.len(), bot.len());
    #[cfg(all(target_arch = "x86_64", target_feature = "vpclmulqdq", target_feature = "avx512f"))]
    {
        let vectors = top.len() / 8;
        // SAFETY: the target features are enabled at compile time and each
        // iteration reads and writes exactly eight elements from both rows.
        unsafe {
            for i in 0..vectors {
                butterfly_lanes_avx512(top.as_mut_ptr().add(8 * i), bot.as_mut_ptr().add(8 * i), twiddle.0);
            }
        }
        for lane in 8 * vectors..top.len() {
            let v = bot[lane];
            let new_u = top[lane] + v * twiddle;
            top[lane] = new_u;
            bot[lane] = v + new_u;
        }
    }
    #[cfg(all(
        target_arch = "x86_64",
        target_feature = "vpclmulqdq",
        target_feature = "avx2",
        not(target_feature = "avx512f")
    ))]
    {
        let vectors = top.len() / 4;
        // SAFETY: the target features are enabled at compile time and each
        // iteration reads and writes exactly four elements from both rows.
        unsafe {
            for i in 0..vectors {
                butterfly_lanes_avx2(top.as_mut_ptr().add(4 * i), bot.as_mut_ptr().add(4 * i), twiddle.0);
            }
        }
        for lane in 4 * vectors..top.len() {
            let v = bot[lane];
            let new_u = top[lane] + v * twiddle;
            top[lane] = new_u;
            bot[lane] = v + new_u;
        }
    }
    #[cfg(all(target_arch = "aarch64", target_feature = "aes"))]
    {
        let vectors = top.len() / 8;
        // SAFETY: aes target feature is enabled at compile time; the kernel
        // reads/writes exactly lanes [8i, 8i+8) of each row.
        unsafe {
            for i in 0..vectors {
                butterfly_lanes_neon_8(top.as_mut_ptr().add(8 * i), bot.as_mut_ptr().add(8 * i), twiddle.0);
            }
            let mut lane = 8 * vectors;
            while lane + 2 <= top.len() {
                butterfly_lane_pair_neon(top.as_mut_ptr().add(lane), bot.as_mut_ptr().add(lane), twiddle.0);
                lane += 2;
            }
        }
        if top.len() % 2 == 1 {
            let last = top.len() - 1;
            let v = bot[last];
            let new_u = top[last] + v * twiddle;
            top[last] = new_u;
            bot[last] = v + new_u;
        }
    }
    #[cfg(not(any(
        all(target_arch = "aarch64", target_feature = "aes"),
        all(target_arch = "x86_64", target_feature = "vpclmulqdq", target_feature = "avx2")
    )))]
    {
        for lane in 0..top.len() {
            let v = bot[lane];
            let new_u = top[lane] + v * twiddle;
            top[lane] = new_u;
            bot[lane] = v + new_u;
        }
    }
}

/// [`butterfly_lanes_avx512`] at half the width, for a machine with VPCLMULQDQ
/// but no AVX-512. Without it the base encode's innermost loop is scalar there,
/// which costs it about half again as much.
///
/// # Safety
/// Requires VPCLMULQDQ + AVX2; `top` and `bot` must each address four readable
/// and writable F64 values.
#[cfg(all(
    target_arch = "x86_64",
    target_feature = "vpclmulqdq",
    target_feature = "avx2",
    not(target_feature = "avx512f")
))]
#[inline]
#[target_feature(enable = "vpclmulqdq", enable = "avx2")]
unsafe fn butterfly_lanes_avx2(top: *mut F64, bot: *mut F64, twiddle: u64) {
    use core::arch::x86_64::*;

    #[inline]
    #[target_feature(enable = "vpclmulqdq", enable = "avx2")]
    unsafe fn reduce(p: __m256i, r: __m256i) -> __m256i {
        let t = _mm256_clmulepi64_epi128::<0x01>(p, r);
        let u = _mm256_clmulepi64_epi128::<0x01>(t, r);
        _mm256_xor_si256(_mm256_xor_si256(p, t), u)
    }

    // SAFETY: the caller supplies valid four-element rows and the function's
    // target features cover every intrinsic below.
    unsafe {
        let u = _mm256_loadu_si256(top.cast());
        let v = _mm256_loadu_si256(bot.cast());
        let tw = _mm256_set1_epi64x(twiddle as i64);
        let r = _mm256_set1_epi64x(0x1b);

        let even = reduce(_mm256_clmulepi64_epi128::<0x00>(v, tw), r);
        let odd = reduce(_mm256_clmulepi64_epi128::<0x11>(v, tw), r);
        // The odd products land in each lane's low half; swap them up, then take
        // the odd qwords (32-bit elements 2, 3, 6, 7) from them.
        let odd = _mm256_shuffle_epi32::<0x4e>(odd);
        let product = _mm256_blend_epi32::<0b1100_1100>(even, odd);

        let new_u = _mm256_xor_si256(u, product);
        let new_v = _mm256_xor_si256(v, new_u);
        _mm256_storeu_si256(top.cast(), new_u);
        _mm256_storeu_si256(bot.cast(), new_v);
    }
}

/// Eight F64 butterflies as four independent NEON lane-pair reductions.
/// Loading all four bottom vectors before reducing them gives the out-of-order
/// core four independent PMULL chains to schedule, while one call amortizes
/// loop control and the duplicated twiddle/reduction constants over 8 lanes.
///
/// # Safety
/// Requires the `aes` target feature; `top`/`bot` must each point at eight
/// readable+writable F64 values.
#[cfg(all(target_arch = "aarch64", target_feature = "aes"))]
#[inline]
#[target_feature(enable = "aes")]
unsafe fn butterfly_lanes_neon_8(top: *mut F64, bot: *mut F64, twiddle: u64) {
    use core::arch::aarch64::*;
    use primitives::field::gf2_64::aarch64::reduce_pair_pmull4;

    // SAFETY: caller guarantees the two eight-element regions; F64 is
    // repr(transparent) over u64 and this function carries the aes feature.
    unsafe {
        let v0 = vld1q_u64(bot.cast());
        let v1 = vld1q_u64(bot.cast::<u64>().add(2));
        let v2 = vld1q_u64(bot.cast::<u64>().add(4));
        let v3 = vld1q_u64(bot.cast::<u64>().add(6));
        let tw = vdupq_n_u64(twiddle);

        let p00: uint64x2_t = core::mem::transmute(vmull_p64(vgetq_lane_u64::<0>(v0), twiddle));
        let p01: uint64x2_t = core::mem::transmute(vmull_high_p64(
            core::mem::transmute::<uint64x2_t, poly64x2_t>(v0),
            core::mem::transmute::<uint64x2_t, poly64x2_t>(tw),
        ));
        let p10: uint64x2_t = core::mem::transmute(vmull_p64(vgetq_lane_u64::<0>(v1), twiddle));
        let p11: uint64x2_t = core::mem::transmute(vmull_high_p64(
            core::mem::transmute::<uint64x2_t, poly64x2_t>(v1),
            core::mem::transmute::<uint64x2_t, poly64x2_t>(tw),
        ));
        let p20: uint64x2_t = core::mem::transmute(vmull_p64(vgetq_lane_u64::<0>(v2), twiddle));
        let p21: uint64x2_t = core::mem::transmute(vmull_high_p64(
            core::mem::transmute::<uint64x2_t, poly64x2_t>(v2),
            core::mem::transmute::<uint64x2_t, poly64x2_t>(tw),
        ));
        let p30: uint64x2_t = core::mem::transmute(vmull_p64(vgetq_lane_u64::<0>(v3), twiddle));
        let p31: uint64x2_t = core::mem::transmute(vmull_high_p64(
            core::mem::transmute::<uint64x2_t, poly64x2_t>(v3),
            core::mem::transmute::<uint64x2_t, poly64x2_t>(tw),
        ));

        let prod0 = reduce_pair_pmull4(p00, p01);
        let prod1 = reduce_pair_pmull4(p10, p11);
        let prod2 = reduce_pair_pmull4(p20, p21);
        let prod3 = reduce_pair_pmull4(p30, p31);

        let u0 = vld1q_u64(top.cast());
        let u1 = vld1q_u64(top.cast::<u64>().add(2));
        let u2 = vld1q_u64(top.cast::<u64>().add(4));
        let u3 = vld1q_u64(top.cast::<u64>().add(6));
        let new_u0 = veorq_u64(u0, prod0);
        let new_u1 = veorq_u64(u1, prod1);
        let new_u2 = veorq_u64(u2, prod2);
        let new_u3 = veorq_u64(u3, prod3);
        let new_v0 = veorq_u64(v0, new_u0);
        let new_v1 = veorq_u64(v1, new_u1);
        let new_v2 = veorq_u64(v2, new_u2);
        let new_v3 = veorq_u64(v3, new_u3);

        vst1q_u64(top.cast(), new_u0);
        vst1q_u64(top.cast::<u64>().add(2), new_u1);
        vst1q_u64(top.cast::<u64>().add(4), new_u2);
        vst1q_u64(top.cast::<u64>().add(6), new_u3);
        vst1q_u64(bot.cast(), new_v0);
        vst1q_u64(bot.cast::<u64>().add(2), new_v1);
        vst1q_u64(bot.cast::<u64>().add(4), new_v2);
        vst1q_u64(bot.cast::<u64>().add(6), new_v3);
    }
}

/// Eight F64 butterflies using the four independent 128-bit lanes of
/// VPCLMULQDQ. Even and odd u64 lanes are multiplied separately, reduced in
/// parallel, then packed back into their original order.
///
/// # Safety
/// Requires VPCLMULQDQ + AVX-512F; `top` and `bot` must each address eight
/// readable and writable F64 values.
#[cfg(all(target_arch = "x86_64", target_feature = "vpclmulqdq", target_feature = "avx512f"))]
#[inline]
#[target_feature(enable = "vpclmulqdq", enable = "avx512f", enable = "avx2")]
unsafe fn butterfly_lanes_avx512(top: *mut F64, bot: *mut F64, twiddle: u64) {
    use core::arch::x86_64::*;

    #[inline]
    #[target_feature(enable = "vpclmulqdq", enable = "avx512f")]
    unsafe fn reduce(p: __m512i, r: __m512i) -> __m512i {
        let t = _mm512_clmulepi64_epi128::<0x01>(p, r);
        let u = _mm512_clmulepi64_epi128::<0x01>(t, r);
        _mm512_xor_si512(_mm512_xor_si512(p, t), u)
    }

    // SAFETY: the caller supplies valid eight-element rows and the function's
    // target features cover every intrinsic below.
    unsafe {
        let u = _mm512_loadu_si512(top.cast());
        let v = _mm512_loadu_si512(bot.cast());
        let tw = _mm512_set1_epi64(twiddle as i64);
        let r = _mm512_set1_epi64(0x1b);

        let even = reduce(_mm512_clmulepi64_epi128::<0x00>(v, tw), r);
        let odd = reduce(_mm512_clmulepi64_epi128::<0x11>(v, tw), r);
        let odd = _mm512_shuffle_epi32::<0x4e>(odd);
        let product = _mm512_mask_blend_epi64(0xaa, even, odd);

        let new_u = _mm512_xor_si512(u, product);
        let new_v = _mm512_xor_si512(v, new_u);
        _mm512_storeu_si512(top.cast(), new_u);
        _mm512_storeu_si512(bot.cast(), new_v);
    }
}

/// Two F64 butterflies with a shared twiddle, NEON-resident end to end.
/// The two products issue as PMULL/PMULL2 on the loaded row (no lane
/// extraction) and reduce through the all-PMULL lane-pair fold
/// ([`primitives::field::gf2_64::aarch64::reduce_pair_pmull4`]), replacing the
/// old 10-op shift-XOR fold chain.
///
/// # Safety
/// Requires the `aes` target feature; `top`/`bot` must each point at two
/// readable+writable F64 values.
#[cfg(all(target_arch = "aarch64", target_feature = "aes"))]
#[inline]
#[target_feature(enable = "aes")]
unsafe fn butterfly_lane_pair_neon(top: *mut F64, bot: *mut F64, twiddle: u64) {
    use core::arch::aarch64::*;
    use primitives::field::gf2_64::aarch64::reduce_pair_pmull4;
    // SAFETY: caller guarantees the pointees; F64 is repr(transparent) u64.
    unsafe {
        let u = vld1q_u64(top as *const u64);
        let v = vld1q_u64(bot as *const u64);
        // Products v_lane * twiddle: PMULL on the low lanes, PMULL2 on the
        // highs (the dup is loop-invariant and hoisted after inlining).
        let tw = vdupq_n_u64(twiddle);
        let p0: uint64x2_t = core::mem::transmute(vmull_p64(vgetq_lane_u64::<0>(v), twiddle));
        let p1: uint64x2_t = core::mem::transmute(vmull_high_p64(
            core::mem::transmute::<uint64x2_t, poly64x2_t>(v),
            core::mem::transmute::<uint64x2_t, poly64x2_t>(tw),
        ));
        let prod = reduce_pair_pmull4(p0, p1);
        let new_u = veorq_u64(u, prod);
        let new_v = veorq_u64(v, new_u);
        vst1q_u64(top as *mut u64, new_u);
        vst1q_u64(bot as *mut u64, new_v);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use primitives::test_rng::Rng;

    /// Check forward∘inverse = id and scalar == interleaved == parallel, plus
    /// linearity.
    #[test]
    fn inverse_roundtrip_and_variants_agree() {
        let ntt = AdditiveNttF64::standard(12);
        let mut rng = Rng::new(1);
        for log_d in [1usize, 3, 6, 10] {
            let n = 1usize << log_d;
            let orig: Vec<F64> = (0..n).map(|_| F64(rng.next_u64())).collect();

            let mut a = orig.clone();
            ntt.forward_transform_scalar(&mut a);
            let mut b = orig.clone();
            ntt.forward_transform_interleaved_scalar_from_layer(&mut b, 1, 0);
            assert_eq!(a, b, "interleaved(1 lane) == scalar at log_d={log_d}");
            let mut c = orig.clone();
            ntt.forward_transform_interleaved_parallel_from_layer(&mut c, 1, 0);
            assert_eq!(a, c, "parallel == scalar at log_d={log_d}");

            ntt.inverse_transform(&mut a);
            assert_eq!(a, orig, "inverse roundtrip at log_d={log_d}");
        }
    }

    /// The parallel interleaved path must match the scalar reference at sizes
    /// that actually reach the fused multi-layer passes.
    ///
    /// `interleaved_lanes_are_independent_ntts` runs at `log_d = 7`, below the
    /// driver's `log_d < 8` bail-out, so it only ever exercises the scalar
    /// path. These shapes give `n_top >= 3`, which is what selects the
    /// radix-8 fused pass, and cover a non-zero `start_layer` because the
    /// commit path enters at `log_inv_rate`.
    #[test]
    fn interleaved_parallel_matches_scalar_at_fused_sizes() {
        let mut rng = Rng::new(0xC0FFEE);
        for log_d in [12usize, 14] {
            for lanes in [8usize, 64] {
                for start_layer in [0usize, 1] {
                    let ntt = AdditiveNttF64::standard(log_d);
                    let n = (1usize << log_d) * lanes;
                    let original: Vec<F64> = (0..n).map(|_| F64(rng.next_u64())).collect();

                    let mut want = original.clone();
                    ntt.forward_transform_interleaved_scalar_from_layer(&mut want, lanes, start_layer);
                    let mut got = original.clone();
                    ntt.forward_transform_interleaved_parallel_from_layer(&mut got, lanes, start_layer);

                    assert_eq!(
                        got, want,
                        "parallel != scalar at log_d={log_d}, lanes={lanes}, start_layer={start_layer}"
                    );
                }
            }
        }
    }

    /// `encode_interleaved_in_place` fuses the replication into its first pass, so it
    /// must land exactly where filling the codeword and transforming it does,
    /// including on the sizes that take its fallback.
    #[test]
    fn fused_encode_matches_replicate_then_transform() {
        let mut rng = Rng::new(0xE0C0DE);
        for log_d in [9usize, 12, 14] {
            for lanes in [8usize, 64, 65] {
                for log_inv_rate in [1usize, 2] {
                    let ntt = AdditiveNttF64::standard(log_d);
                    let msg_len = ((1usize << log_d) * lanes) >> log_inv_rate;
                    let msg: Vec<F64> = (0..msg_len).map(|_| F64(rng.next_u64())).collect();

                    let mut want = vec![F64::ZERO; msg_len << log_inv_rate];
                    replicate_rows(&mut want, &msg);
                    ntt.forward_transform_interleaved_parallel_from_layer(&mut want, lanes, log_inv_rate);

                    let mut got = vec![F64::ZERO; msg_len << log_inv_rate];
                    got[..msg_len].copy_from_slice(&msg);
                    ntt.encode_interleaved_in_place(&mut got, lanes, log_inv_rate);

                    assert_eq!(
                        got, want,
                        "fused != replicate+transform at log_d={log_d}, lanes={lanes}, rate={log_inv_rate}"
                    );
                }
            }
        }
    }

    #[cfg(target_arch = "x86_64")]
    #[test]
    fn gathered_encode_prefix_matches_scalar() {
        let mut rng = Rng::new(0x81CE_0443);
        for (log_radix, lanes, rate) in [(3, 3, 1), (4, 17, 2), (5, 65, 1), (6, 34, 2), (7, 34, 2), (7, 65, 1)] {
            let log_d = rate + log_radix + 2;
            let ntt = AdditiveNttF64::standard(log_d);
            let msg_len = lanes << (log_d - rate);
            let message: Vec<F64> = (0..msg_len).map(|_| F64(rng.next_u64())).collect();
            let mut expected = vec![F64::ZERO; lanes << log_d];
            replicate_rows(&mut expected, &message);
            ntt.forward_transform_interleaved_scalar_from_layer(&mut expected, lanes, rate);

            let mut actual = vec![F64::ZERO; expected.len()];
            actual[..msg_len].copy_from_slice(&message);
            ntt.encode_first_pass(&mut actual, lanes, rate, log_radix);
            ntt.forward_transform_interleaved_scalar_from_layer(&mut actual, lanes, rate + log_radix);
            assert_eq!(actual, expected, "radix={log_radix}, lanes={lanes}, rate={rate}");
        }
    }

    /// Every lane of the codeword must be exactly the single-lane RS codeword of
    /// that lane's contiguous message block, which is what makes a commitment over
    /// `n_lanes` lanes equal to the `2^log_batch_size`-lane one with a zero tail.
    /// The shapes cover the transposing fused first pass, its fallback, and lane
    /// counts that are not powers of two (the padding-free commit's whole point).
    #[test]
    fn lane_major_msg_encode_matches_per_lane_reference() {
        let mut rng = Rng::new(0x1A2E);
        for (log_rows, log_inv_rate, n_lanes) in [
            (2usize, 1usize, 3usize),
            (3, 1, 1),
            (5, 2, 7),
            (9, 1, 5),
            (12, 2, 37),
            (14, 1, 64),
        ] {
            let log_d = log_rows + log_inv_rate;
            let ntt = AdditiveNttF64::standard(log_d);
            let rows = 1usize << log_rows;
            let msg: Vec<F64> = (0..rows * n_lanes).map(|_| F64(rng.next_u64())).collect();

            let mut got = vec![F64::ZERO; msg.len() << log_inv_rate];
            transpose_lane_major(&mut got[..msg.len()], &msg, n_lanes, log_rows);
            ntt.encode_interleaved_in_place(&mut got, n_lanes, log_inv_rate);

            let block_len = 1usize << log_d;
            for lane in 0..n_lanes {
                // Lane `lane` encodes message block `n_lanes - 1 - lane`.
                let block = n_lanes - 1 - lane;
                let mut want = vec![F64::ZERO; block_len];
                replicate_rows(&mut want, &msg[block * rows..(block + 1) * rows]);
                ntt.forward_transform_interleaved_parallel_from_layer(&mut want, 1, log_inv_rate);
                for pos in 0..block_len {
                    assert_eq!(
                        got[pos * n_lanes + lane],
                        want[pos],
                        "lane {lane} pos {pos} at log_rows={log_rows}, rate={log_inv_rate}, n_lanes={n_lanes}"
                    );
                }
            }
        }
    }

    #[test]
    fn interleaved_lanes_are_independent_ntts() {
        let ntt = AdditiveNttF64::standard(10);
        let mut rng = Rng::new(2);
        let log_d = 7;
        let n = 1usize << log_d;
        for lanes in [1usize, 2, 4, 8, 64] {
            // SoA buffer + per-lane copies.
            let mut soa = vec![F64::ZERO; n * lanes];
            let mut per_lane: Vec<Vec<F64>> = vec![vec![F64::ZERO; n]; lanes];
            for pos in 0..n {
                for lane in 0..lanes {
                    let v = F64(rng.next_u64());
                    soa[pos * lanes + lane] = v;
                    per_lane[lane][pos] = v;
                }
            }
            ntt.forward_transform_interleaved_parallel_from_layer(&mut soa, lanes, 0);
            for (lane, lane_data) in per_lane.iter_mut().enumerate() {
                ntt.forward_transform_scalar(lane_data);
                for pos in 0..n {
                    assert_eq!(soa[pos * lanes + lane], lane_data[pos]);
                }
            }
        }
    }
}
