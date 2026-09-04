// CREDIT: https://github.com/succinctlabs/flock (flock-core), MIT OR Apache-2.0.
// Copyright (c) 2026 Bain Capital Crypto, LP and Ron Rothblum
// Modifications copyright 2026 Succinct Labs, Benedikt Bunz, William Wang
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! Interleaved forward additive NTT over `E = GF(2^192)` with K-twiddles,
//! split out of `whir` because it shares nothing with the rest of the
//! opener beyond the two log helpers.

use crate::ntt::AdditiveNttF64;
use primitives::field::{F64, F192};
use primitives::log2_ceil_usize;
use primitives::log2_strict_usize;

// ===================================================================
// Interleaved forward additive NTT over E with K-twiddles
// ===================================================================
//
// Deeper WHIR levels RS-encode an E-valued (folded) witness on the SAME
// K-domain: the twiddles are F64, and each butterfly multiply is the mixed
// product `v.mul_base(twiddle)` (3 PMULL). Structure copied from
// `ntt::additive_ntt_f64`'s interleaved transform, with constants re-derived
// for 24-byte elements.

pub(crate) fn forward_transform_interleaved_ext_from_layer(
    ntt: &AdditiveNttF64,
    data: &mut [F192],
    num_ntts: usize,
    start_layer: usize,
) {
    assert!(num_ntts.is_power_of_two() && num_ntts > 0);
    let n_total = data.len();
    assert_eq!(n_total % num_ntts, 0);
    let log_d = log2_strict_usize(n_total / num_ntts);
    assert!(log_d <= ntt.log_domain_size());
    assert!(start_layer <= log_d);

    // Keep the dedicated NEON and AVX-512 kernels; other x86 targets share the base NTT's larger groups.
    if log_d >= 12
        && cfg!(all(
            target_arch = "x86_64",
            not(all(target_feature = "vpclmulqdq", target_feature = "avx512f"))
        ))
    {
        forward_transform_interleaved_ext_via_base(ntt, data, num_ntts, start_layer);
    } else {
        forward_transform_interleaved_ext_parallel_from_layer(ntt, data, num_ntts, start_layer);
    }
}

pub(crate) fn forward_transform_interleaved_ext_via_base(
    ntt: &AdditiveNttF64,
    data: &mut [F192],
    num_ntts: usize,
    start_layer: usize,
) {
    const _: () = assert!(size_of::<F192>() == 3 * size_of::<F64>());
    const _: () = assert!(align_of::<F192>() == align_of::<F64>());
    // SAFETY: F192 is repr(C) over three u64 coefficients, and F64 is transparent over u64.
    // Base-field twiddles act independently on each coefficient, preserving the row layout.
    let coefficients = unsafe { std::slice::from_raw_parts_mut(data.as_mut_ptr().cast::<F64>(), 3 * data.len()) };
    ntt.forward_transform_interleaved_parallel_from_layer(coefficients, 3 * num_ntts, start_layer);
}

/// Scalar reference for the E-valued interleaved forward NTT (test oracle and
/// small-input path).
pub(crate) fn forward_transform_interleaved_ext_scalar_from_layer(
    ntt: &AdditiveNttF64,
    data: &mut [F192],
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
            let twiddle = ntt.twiddle(layer, block);
            let block_start = block * block_elems;
            for row in 0..block_size_half {
                let off_top = block_start + row * num_ntts;
                let off_bot = off_top + block_size_half * num_ntts;
                for lane in 0..num_ntts {
                    let v = data[off_bot + lane];
                    let new_u = data[off_top + lane] + v.mul_base(twiddle);
                    data[off_top + lane] = new_u;
                    data[off_bot + lane] = v + new_u;
                }
            }
        }
    }
}

/// Parallel interleaved forward NTT over E, cache-blocked like the F64 twin:
/// top layers sweep the full buffer (fused two-layer passes, row-parallel),
/// deep layers run as cache-resident sub-NTTs in parallel. Constants are
/// derived from the actual F192 element size.
pub(crate) fn forward_transform_interleaved_ext_parallel_from_layer(
    ntt: &AdditiveNttF64,
    data: &mut [F192],
    num_ntts: usize,
    start_layer: usize,
) {
    let n_total = data.len();
    let log_d = log2_strict_usize(n_total / num_ntts);

    // Keep each worker's subgroup cache-resident. F192 uses three words per position.
    const TARGET_SUBGROUP_LOG_BYTES: usize = 20;
    let log_bytes_per_position = log2_ceil_usize(num_ntts * core::mem::size_of::<F192>());
    let target_log_positions = TARGET_SUBGROUP_LOG_BYTES.saturating_sub(log_bytes_per_position);
    let cache_n_top = log_d.saturating_sub(target_log_positions);

    const PARALLEL_FLOOR_LOG_D: usize = 12;
    const MIN_SUB_LOG: usize = 8;
    let n_top = if log_d >= PARALLEL_FLOOR_LOG_D {
        let want_subs_log = log2_strict_usize(parallel::num_threads().next_power_of_two());
        let max_n_top = log_d.saturating_sub(MIN_SUB_LOG);
        cache_n_top.max(want_subs_log.min(max_n_top))
    } else {
        cache_n_top
    };
    if n_top == 0 || log_d < 8 {
        forward_transform_interleaved_ext_scalar_from_layer(ntt, data, num_ntts, start_layer);
        return;
    }

    // Top layers: full-buffer sweeps, rows fanned out to the pool.
    run_layers_ext(ntt, data, log_d, num_ntts, start_layer.min(n_top), n_top, 0, 0, true);

    // Deep layers: one sub-NTT per worker over a cache-resident sub-block. Layers
    // fuse here for the same reason they do above, only the pass being saved is
    // over L2/L3 rather than DRAM: a sub is about a megabyte, so sweeping it
    // once per layer re-reads it once per layer. The row loop inside a fused
    // kernel stays serial, since the parallelism is already spent on the subs and
    // a nested dispatch would deadlock.
    let sub_elems = (1usize << (log_d - n_top)) * num_ntts;
    parallel::chunks_mut(data, sub_elems, |sub_idx, sub_data| {
        run_layers_ext(
            ntt,
            sub_data,
            log_d,
            num_ntts,
            n_top.max(start_layer),
            log_d,
            n_top,
            sub_idx,
            false,
        );
    });
}

/// Apply layers `first_layer..end_layer` to `buf`, which holds sub-NTT `sub_idx`
/// of the `2^outer_log` the buffer was split into (`0`/`0` for the whole
/// codeword). Fuses three layers per pass where the block is wide enough, then
/// two, then one; the F64 twin's `run_layers` is the same ladder.
#[allow(clippy::too_many_arguments)]
fn run_layers_ext(
    ntt: &AdditiveNttF64,
    buf: &mut [F192],
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
                let t = ntt.twiddles_radix8(layer, global(block_in_buf));
                let start = block_in_buf * block_elems;
                fused_rows_ext::<8>(
                    &mut buf[start..start + block_elems],
                    eighth,
                    num_ntts,
                    par_rows,
                    |rows| radix8_butterflies_ext(rows, &t),
                );
            }
            layer += 3;
        } else if layer + 1 < end_layer && block_size >= 4 {
            let quarter = block_size >> 2;
            for block_in_buf in 0..num_blocks_in_buf {
                let gb = global(block_in_buf);
                let t = [
                    ntt.twiddle(layer, gb),
                    ntt.twiddle(layer + 1, 2 * gb),
                    ntt.twiddle(layer + 1, 2 * gb + 1),
                ];
                let start = block_in_buf * block_elems;
                fused_rows_ext::<4>(
                    &mut buf[start..start + block_elems],
                    quarter,
                    num_ntts,
                    par_rows,
                    |rows| radix4_butterflies_ext(rows, &t),
                );
            }
            layer += 2;
        } else {
            let block_size_half = block_size >> 1;
            for block_in_buf in 0..num_blocks_in_buf {
                let twiddle = ntt.twiddle(layer, global(block_in_buf));
                let start = block_in_buf * block_elems;
                let block = &mut buf[start..start + block_elems];
                if par_rows {
                    butterfly_interleaved_ext_block_par_rows(block, twiddle, block_size_half, num_ntts);
                } else {
                    butterfly_interleaved_ext_block(block, twiddle, block_size_half, num_ntts);
                }
            }
            layer += 1;
        }
    }
}

/// Hand `do_one` the `N` rows `block[i * stride + r * num_ntts ..][..num_ntts]`
/// for each `r`; see the F64 twin's `fused_rows` for the disjointness argument
/// that lets one base pointer stand in for `N` nested `split_at_mut`s.
fn fused_rows_ext<const N: usize>(
    block: &mut [F192],
    stride_rows: usize,
    num_ntts: usize,
    par_rows: bool,
    do_one: impl Fn(&mut [&mut [F192]; N]) + Sync,
) {
    const PARALLEL_ROW_THRESHOLD: usize = 512;
    let stride = stride_rows * num_ntts;
    debug_assert_eq!(block.len(), N * stride);

    let base = parallel::SendPtr(block.as_mut_ptr());
    let group = |r: usize| {
        let off = r * num_ntts;
        // SAFETY: see above; `off + num_ntts <= stride` because `r < stride_rows`.
        let mut rows: [&mut [F192]; N] = std::array::from_fn(|i| unsafe { base.slice(i * stride + off, num_ntts) });
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

fn butterfly_interleaved_ext_block_par_rows(block: &mut [F192], twiddle: F64, block_size_half: usize, num_ntts: usize) {
    const PARALLEL_ROW_THRESHOLD: usize = 1024;
    if block_size_half < PARALLEL_ROW_THRESHOLD {
        butterfly_interleaved_ext_block(block, twiddle, block_size_half, num_ntts);
        return;
    }
    let half_offset = block_size_half * num_ntts;
    let (top, bot) = block.split_at_mut(half_offset);
    let bot_base = parallel::SendPtr(bot.as_mut_ptr());
    parallel::chunks_mut(top, num_ntts, |r, top_row| {
        // SAFETY: distinct `r` take disjoint `num_ntts`-windows of `bot` (the
        // same windows `chunks_mut` proved disjoint in `top`), and the halves are
        // disjoint by `split_at_mut`.
        let bot_row = unsafe { bot_base.slice(r * num_ntts, top_row.len()) };
        butterfly_ext_lanes(top_row, bot_row, twiddle);
    });
}

/// Which rows each butterfly of a fused pass pairs, and which twiddle it takes:
/// layer `L` pairs at distance `N/2`, `L+1` at `N/4`, and so on down, with the
/// twiddles held breadth-first. The F64 twin spells the same schedule out in
/// `radix8_butterflies`.
const RADIX4_PAIRS: [(usize, usize, usize); 4] = [(0, 2, 0), (1, 3, 0), (0, 1, 1), (2, 3, 2)];
const RADIX8_PAIRS: [(usize, usize, usize); 12] = [
    (0, 4, 0),
    (1, 5, 0),
    (2, 6, 0),
    (3, 7, 0),
    (0, 2, 1),
    (1, 3, 1),
    (4, 6, 2),
    (5, 7, 2),
    (0, 1, 3),
    (2, 3, 4),
    (4, 5, 5),
    (6, 7, 6),
];

#[inline]
fn radix4_butterflies_ext(rows: &mut [&mut [F192]; 4], t: &[F64; 3]) {
    fused_butterflies_ext(rows, t, &RADIX4_PAIRS);
}

#[inline]
fn radix8_butterflies_ext(rows: &mut [&mut [F192]; 8], t: &[F64; 7]) {
    fused_butterflies_ext(rows, t, &RADIX8_PAIRS);
}

/// Run one fused pass's butterflies over `N` rows. The AVX-512 path holds all
/// `N` rows in SoA registers for the whole schedule, so each row pays the AoS
/// transpose once per pass rather than once per butterfly; fusing three layers
/// instead of two therefore buys both a third fewer passes over the codeword and
/// a third fewer transposes per butterfly.
#[inline]
fn fused_butterflies_ext<const N: usize, const P: usize, const T: usize>(
    rows: &mut [&mut [F192]; N],
    t: &[F64; T],
    pairs: &[(usize, usize, usize); P],
) {
    #[cfg(all(target_arch = "x86_64", target_feature = "vpclmulqdq", target_feature = "avx512f"))]
    {
        let len = rows[0].len();
        for i in 0..len / 8 {
            // SAFETY: target features are enabled at compile time, the rows are
            // pairwise disjoint, and each holds eight readable and writable F192
            // values at `8 * i`.
            unsafe {
                let ptrs: [*mut F192; N] = std::array::from_fn(|k| rows[k].as_mut_ptr().add(8 * i));
                fused_lanes_avx512(ptrs, t, pairs);
            }
        }
        for lane in 8 * (len / 8)..len {
            fused_lane_scalar(rows, t, pairs, lane);
        }
    }
    // A butterfly at a time, each over whole rows, as the F64 twin's
    // `radix8_butterflies` does. Holding a tile of every row in registers for
    // the whole schedule instead (the shape the AVX-512 arm takes, since it has
    // to transpose anyway) saves the reloads, but the rows never leave L1 and a
    // tile leaves only its own width of independent work to cover the
    // reduction's dependent PMULL folds, where a row leaves the whole lane
    // count. Measured both directions: the tile is worse here, and worse again
    // when the base encode's radix-8 group is given it.
    #[cfg(all(target_arch = "aarch64", target_feature = "aes"))]
    {
        let ptrs: [*mut u64; N] = std::array::from_fn(|k| rows[k].as_mut_ptr().cast());
        // SAFETY: `aes` is enabled at compile time, the rows are pairwise
        // disjoint, and each is `3 * len` contiguous u64 (`F192` is repr(C) over
        // three).
        unsafe {
            for &(top, bot, tw) in pairs {
                butterfly_row_neon(ptrs[top], ptrs[bot], t[tw].0, 3 * rows[0].len());
            }
        }
    }
    #[cfg(not(any(
        all(target_arch = "x86_64", target_feature = "vpclmulqdq", target_feature = "avx512f"),
        all(target_arch = "aarch64", target_feature = "aes")
    )))]
    for lane in 0..rows[0].len() {
        fused_lane_scalar(rows, t, pairs, lane);
    }
}

/// One lane of [`fused_butterflies_ext`]: the portable path and the AVX-512
/// path's ragged tail. The NEON arm works a coefficient at a time rather than a
/// lane, so it has its own tail and does not reach this.
#[cfg(not(all(target_arch = "aarch64", target_feature = "aes")))]
#[inline]
fn fused_lane_scalar<const N: usize, const P: usize, const T: usize>(
    rows: &mut [&mut [F192]; N],
    t: &[F64; T],
    pairs: &[(usize, usize, usize); P],
    lane: usize,
) {
    let mut v: [F192; N] = std::array::from_fn(|k| rows[k][lane]);
    for &(top, bot, tw) in pairs {
        let new_top = v[top] + v[bot].mul_base(t[tw]);
        v[bot] += new_top;
        v[top] = new_top;
    }
    for (row, value) in rows.iter_mut().zip(v) {
        row[lane] = value;
    }
}

#[inline]
fn butterfly_interleaved_ext_block(block: &mut [F192], twiddle: F64, block_size_half: usize, num_ntts: usize) {
    let half_offset = block_size_half * num_ntts;
    let (top, bot) = block.split_at_mut(half_offset);
    for r in 0..block_size_half {
        let off = r * num_ntts;
        butterfly_ext_lanes(&mut top[off..off + num_ntts], &mut bot[off..off + num_ntts], twiddle);
    }
}

/// Butterfly all extension-field lanes in a row pair. The production layout
/// has eight interleaved NTTs, which the AVX-512 path transposes from eight
/// AoS `F192`s into three coefficient vectors before multiplying.
#[inline]
fn butterfly_ext_lanes(top: &mut [F192], bot: &mut [F192], twiddle: F64) {
    debug_assert_eq!(top.len(), bot.len());
    #[cfg(all(target_arch = "x86_64", target_feature = "vpclmulqdq", target_feature = "avx512f"))]
    {
        let vectors = top.len() / 8;
        // SAFETY: target features are enabled at compile time and every call
        // addresses exactly eight readable and writable F192 values.
        unsafe {
            for i in 0..vectors {
                butterfly_ext_lanes_avx512(top.as_mut_ptr().add(8 * i), bot.as_mut_ptr().add(8 * i), twiddle.0);
            }
        }
        for lane in 8 * vectors..top.len() {
            let v = bot[lane];
            let new_u = top[lane] + v.mul_base(twiddle);
            top[lane] = new_u;
            bot[lane] = v + new_u;
        }
    }
    #[cfg(all(target_arch = "aarch64", target_feature = "aes"))]
    {
        // SAFETY: `aes` is enabled at compile time, and `F192` is repr(C) over
        // three u64, so each row is `3 * len` contiguous readable and writable
        // u64 in a region disjoint from the other's.
        unsafe {
            butterfly_row_neon(
                top.as_mut_ptr().cast(),
                bot.as_mut_ptr().cast(),
                twiddle.0,
                3 * top.len(),
            );
        }
    }
    #[cfg(not(any(
        all(target_arch = "x86_64", target_feature = "vpclmulqdq", target_feature = "avx512f"),
        all(target_arch = "aarch64", target_feature = "aes")
    )))]
    {
        for lane in 0..top.len() {
            let v = bot[lane];
            let new_u = top[lane] + v.mul_base(twiddle);
            top[lane] = new_u;
            bot[lane] = v + new_u;
        }
    }
}

/// The extension butterfly on NEON, over the coefficients as one flat u64 row.
///
/// `mul_base` scales all three coefficients of an `F192` by the same twiddle and
/// the adds are elementwise, so a butterfly over `n` interleaved F192 lanes is
/// exactly the base field's over `3n` u64. The AoS layout therefore needs no
/// transpose here, unlike the AVX-512 arm, whose register holds one coefficient
/// of eight lanes at a time and so has to gather them.
///
/// Four 128-bit pairs an iteration: eight products in flight cover the latency
/// of the reduction's dependent folds, as the F64 twin's eight-lane kernel does.
///
/// # Safety
/// Requires the `aes` target feature; `top` and `bot` must each address `n`
/// readable and writable u64 in regions disjoint from each other.
/// How many 128-bit vectors of the row a butterfly takes at once.
#[cfg(all(target_arch = "aarch64", target_feature = "aes"))]
const ROW_RUN: usize = 4;

#[cfg(all(target_arch = "aarch64", target_feature = "aes"))]
#[inline]
#[target_feature(enable = "aes")]
unsafe fn butterfly_row_neon(top: *mut u64, bot: *mut u64, twiddle: u64, n: usize) {
    use core::arch::aarch64::*;
    use primitives::field::gf2_64::aarch64::{pmull, pmull_hi, reduce_pair_pmull4};

    // SAFETY: the caller's regions cover every access below; the intrinsics are
    // covered by this function's target feature.
    unsafe {
        let tw = vdupq_n_u64(twiddle);
        let scale = |v: uint64x2_t| reduce_pair_pmull4(pmull(vgetq_lane_u64::<0>(v), twiddle), pmull_hi(v, tw));
        let mut i = 0;
        while i + 2 * ROW_RUN <= n {
            let v: [uint64x2_t; ROW_RUN] = std::array::from_fn(|k| vld1q_u64(bot.add(i + 2 * k)));
            let prod = v.map(scale);
            for k in 0..ROW_RUN {
                let new_u = veorq_u64(vld1q_u64(top.add(i + 2 * k)), prod[k]);
                vst1q_u64(top.add(i + 2 * k), new_u);
                vst1q_u64(bot.add(i + 2 * k), veorq_u64(v[k], new_u));
            }
            i += 2 * ROW_RUN;
        }
        while i + 2 <= n {
            let v = vld1q_u64(bot.add(i));
            let new_u = veorq_u64(vld1q_u64(top.add(i)), scale(v));
            vst1q_u64(top.add(i), new_u);
            vst1q_u64(bot.add(i), veorq_u64(v, new_u));
            i += 2;
        }
        if i < n {
            // `3 * len` is odd exactly when the lane count is.
            let v = F64(*bot.add(i));
            let new_u = F64(*top.add(i)) + v * F64(twiddle);
            *top.add(i) = new_u.0;
            *bot.add(i) = (v + new_u).0;
        }
    }
}

#[cfg(all(target_arch = "x86_64", target_feature = "vpclmulqdq", target_feature = "avx512f"))]
#[derive(Clone, Copy)]
struct F192x8 {
    c0: core::arch::x86_64::__m512i,
    c1: core::arch::x86_64::__m512i,
    c2: core::arch::x86_64::__m512i,
}

#[cfg(all(target_arch = "x86_64", target_feature = "vpclmulqdq", target_feature = "avx512f"))]
#[inline]
#[target_feature(enable = "avx512f")]
unsafe fn load_f192x8_avx512(ptr: *const F192) -> F192x8 {
    use core::arch::x86_64::*;

    // The 24 coefficients occupy three contiguous ZMM registers. Each result
    // first selects from the first two registers, then fills its tail from the
    // third register.
    unsafe {
        let p = ptr.cast::<u64>();
        let x0 = _mm512_loadu_si512(p.cast());
        let x1 = _mm512_loadu_si512(p.add(8).cast());
        let x2 = _mm512_loadu_si512(p.add(16).cast());

        let c0_head = _mm512_permutex2var_epi64(x0, _mm512_set_epi64(0, 0, 15, 12, 9, 6, 3, 0), x1);
        let c0_tail = _mm512_permutexvar_epi64(_mm512_set_epi64(5, 2, 0, 0, 0, 0, 0, 0), x2);
        let c1_head = _mm512_permutex2var_epi64(x0, _mm512_set_epi64(0, 0, 0, 13, 10, 7, 4, 1), x1);
        let c1_tail = _mm512_permutexvar_epi64(_mm512_set_epi64(6, 3, 0, 0, 0, 0, 0, 0), x2);
        let c2_head = _mm512_permutex2var_epi64(x0, _mm512_set_epi64(0, 0, 0, 14, 11, 8, 5, 2), x1);
        let c2_tail = _mm512_permutexvar_epi64(_mm512_set_epi64(7, 4, 1, 0, 0, 0, 0, 0), x2);

        F192x8 {
            c0: _mm512_mask_mov_epi64(c0_head, 0xc0, c0_tail),
            c1: _mm512_mask_mov_epi64(c1_head, 0xe0, c1_tail),
            c2: _mm512_mask_mov_epi64(c2_head, 0xe0, c2_tail),
        }
    }
}

#[cfg(all(target_arch = "x86_64", target_feature = "vpclmulqdq", target_feature = "avx512f"))]
#[inline]
#[target_feature(enable = "avx512f")]
unsafe fn store_f192x8_avx512(ptr: *mut F192, value: F192x8) {
    use core::arch::x86_64::*;

    unsafe {
        let x0_head = _mm512_permutex2var_epi64(value.c0, _mm512_set_epi64(10, 2, 0, 9, 1, 0, 8, 0), value.c1);
        let x0_tail = _mm512_permutexvar_epi64(_mm512_set_epi64(0, 0, 1, 0, 0, 0, 0, 0), value.c2);

        let x1_head = _mm512_permutex2var_epi64(value.c0, _mm512_set_epi64(5, 0, 12, 4, 0, 11, 3, 0), value.c1);
        let x1_tail = _mm512_permutexvar_epi64(_mm512_set_epi64(0, 4, 0, 0, 3, 0, 0, 2), value.c2);

        let x2_head = _mm512_permutex2var_epi64(value.c0, _mm512_set_epi64(0, 15, 7, 0, 14, 6, 0, 13), value.c1);
        let x2_tail = _mm512_permutexvar_epi64(_mm512_set_epi64(7, 0, 0, 6, 0, 0, 5, 0), value.c2);

        let p = ptr.cast::<u64>();
        _mm512_storeu_si512(p.cast(), _mm512_mask_mov_epi64(x0_head, 0x24, x0_tail));
        _mm512_storeu_si512(p.add(8).cast(), _mm512_mask_mov_epi64(x1_head, 0x49, x1_tail));
        _mm512_storeu_si512(p.add(16).cast(), _mm512_mask_mov_epi64(x2_head, 0x92, x2_tail));
    }
}

#[cfg(all(target_arch = "x86_64", target_feature = "vpclmulqdq", target_feature = "avx512f"))]
#[inline]
#[target_feature(enable = "vpclmulqdq", enable = "avx512f")]
unsafe fn mul_base_f192x8_avx512(value: F192x8, twiddle: u64) -> F192x8 {
    use core::arch::x86_64::*;

    #[inline]
    #[target_feature(enable = "vpclmulqdq", enable = "avx512f")]
    unsafe fn mul_coeff(value: __m512i, tw: __m512i, r: __m512i) -> __m512i {
        let even = _mm512_clmulepi64_epi128::<0x00>(value, tw);
        let even_t = _mm512_clmulepi64_epi128::<0x01>(even, r);
        let even_u = _mm512_clmulepi64_epi128::<0x01>(even_t, r);
        let even = _mm512_xor_si512(_mm512_xor_si512(even, even_t), even_u);

        let odd = _mm512_clmulepi64_epi128::<0x11>(value, tw);
        let odd_t = _mm512_clmulepi64_epi128::<0x01>(odd, r);
        let odd_u = _mm512_clmulepi64_epi128::<0x01>(odd_t, r);
        let odd = _mm512_shuffle_epi32::<0x4e>(_mm512_xor_si512(_mm512_xor_si512(odd, odd_t), odd_u));
        _mm512_mask_blend_epi64(0xaa, even, odd)
    }

    unsafe {
        let tw = _mm512_set1_epi64(twiddle as i64);
        let r = _mm512_set1_epi64(0x1b);
        F192x8 {
            c0: mul_coeff(value.c0, tw, r),
            c1: mul_coeff(value.c1, tw, r),
            c2: mul_coeff(value.c2, tw, r),
        }
    }
}

#[cfg(all(target_arch = "x86_64", target_feature = "vpclmulqdq", target_feature = "avx512f"))]
#[inline]
#[target_feature(enable = "avx512f")]
unsafe fn butterfly_f192x8_avx512(top: F192x8, bot: F192x8, twiddle: u64) -> (F192x8, F192x8) {
    use core::arch::x86_64::_mm512_xor_si512;

    unsafe {
        let p = mul_base_f192x8_avx512(bot, twiddle);
        let top = F192x8 {
            c0: _mm512_xor_si512(top.c0, p.c0),
            c1: _mm512_xor_si512(top.c1, p.c1),
            c2: _mm512_xor_si512(top.c2, p.c2),
        };
        let bot = F192x8 {
            c0: _mm512_xor_si512(bot.c0, top.c0),
            c1: _mm512_xor_si512(bot.c1, top.c1),
            c2: _mm512_xor_si512(bot.c2, top.c2),
        };
        (top, bot)
    }
}

/// One fused pass's butterflies over `N` rows of eight lanes, the rows loaded
/// into SoA registers once and stored once.
///
/// # Safety
/// Requires VPCLMULQDQ + AVX-512F; the `N` pointers must address pairwise
/// disjoint runs of eight readable and writable F192 values.
#[cfg(all(target_arch = "x86_64", target_feature = "vpclmulqdq", target_feature = "avx512f"))]
#[inline]
#[target_feature(enable = "vpclmulqdq", enable = "avx512f")]
unsafe fn fused_lanes_avx512<const N: usize, const P: usize, const T: usize>(
    rows: [*mut F192; N],
    t: &[F64; T],
    pairs: &[(usize, usize, usize); P],
) {
    unsafe {
        let mut v: [F192x8; N] = std::array::from_fn(|k| load_f192x8_avx512(rows[k]));
        for &(top, bot, tw) in pairs {
            let (x, y) = butterfly_f192x8_avx512(v[top], v[bot], t[tw].0);
            v[top] = x;
            v[bot] = y;
        }
        for (row, value) in rows.into_iter().zip(v) {
            store_f192x8_avx512(row, value);
        }
    }
}

/// Eight F192 butterflies with a shared base-field twiddle.
///
/// # Safety
/// Requires VPCLMULQDQ + AVX-512F; `top` and `bot` must each address eight
/// readable and writable F192 values.
#[cfg(all(target_arch = "x86_64", target_feature = "vpclmulqdq", target_feature = "avx512f"))]
#[inline]
#[target_feature(enable = "vpclmulqdq", enable = "avx512f")]
unsafe fn butterfly_ext_lanes_avx512(top: *mut F192, bot: *mut F192, twiddle: u64) {
    unsafe {
        let (u, v) = butterfly_f192x8_avx512(load_f192x8_avx512(top), load_f192x8_avx512(bot), twiddle);
        store_f192x8_avx512(top, u);
        store_f192x8_avx512(bot, v);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use primitives::test_rng::Rng;

    /// Both fused schedules against a butterfly-at-a-time oracle. The AVX-512
    /// path holds every row of a pass in registers at once, so a mispaired row
    /// or a wrong twiddle shows up here and nowhere else; the ragged lane count
    /// covers the scalar tail the production width never reaches.
    #[test]
    fn fused_butterflies_match_one_at_a_time() {
        let mut rng = Rng::new(0x56c8_1b92_d4a7_30ef);
        for lanes in [8, 11] {
            for _ in 0..50 {
                check::<4, 4, 3>(&mut rng, &RADIX4_PAIRS, lanes);
                check::<8, 12, 7>(&mut rng, &RADIX8_PAIRS, lanes);
            }
        }
    }

    fn check<const N: usize, const P: usize, const T: usize>(
        rng: &mut Rng,
        pairs: &[(usize, usize, usize); P],
        lanes: usize,
    ) {
        let mut rows: [Vec<F192>; N] = std::array::from_fn(|_| (0..lanes).map(|_| rng.ext()).collect());
        let t: [F64; T] = std::array::from_fn(|_| F64(rng.next_u64()));

        let mut want = rows.clone();
        for &(top, bot, tw) in pairs {
            for lane in 0..lanes {
                let new_top = want[top][lane] + want[bot][lane].mul_base(t[tw]);
                want[bot][lane] += new_top;
                want[top][lane] = new_top;
            }
        }

        fused_butterflies_ext(&mut rows.each_mut().map(|row| row.as_mut_slice()), &t, pairs);
        assert_eq!(rows, want);
    }
}
