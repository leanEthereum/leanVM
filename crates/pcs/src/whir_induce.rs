// CREDIT: https://github.com/succinctlabs/flock (flock-core), MIT OR Apache-2.0.
// Copyright (c) 2026 Bain Capital Crypto, LP and Ron Rothblum
// Modifications copyright 2026 Succinct Labs, Benedikt Bunz, William Wang
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! LCH novel-basis induction of the per-level sumcheck basis polynomial: the
//! dense per-query expansion, its succinct residual evaluator, and the sparse
//! transposed-NTT fast path with the dispatch between them.

use crate::ntt::AdditiveNttF64;
use crate::whir::build_eq_table_ext;
use primitives::field::{F64, F192, F192Unreduced};
use zk_alloc::ArenaVec;

// ===================================================================
// LCH novel-basis evaluations over K (mirror of whir's extension-field block)
// ===================================================================
//
// The subspace-polynomial recurrence runs entirely over the K evaluation
// domain (F64 values); results are lifted into E with `mul_base` only where
// they scale E-accumulators. Standard basis only (v_i = x^i = F64(1 << i)).

#[inline]
fn next_s(s: F64, s_at_root: F64) -> F64 {
    s * s + s_at_root * s
}

/// `sks_vks[k] = s_k(v_k)` for `k = 0..=log_n`, over K. Mirror of
/// `whir::eval_sk_at_vks`.
pub fn eval_sk_at_vks(log_n: usize) -> Vec<F64> {
    let mut sks_vks = vec![F64::ZERO; log_n + 1];
    sks_vks[0] = F64::ONE;
    if log_n == 0 {
        return sks_vks;
    }
    let mut layer: Vec<F64> = (1..=log_n).map(|i| F64(1u64 << i)).collect();
    let mut cur_len = log_n;
    for i in 0..log_n {
        for j in 0..cur_len {
            let sk_at_vk = next_s(layer[j], sks_vks[i]);
            if j == 0 {
                sks_vks[i + 1] = sk_at_vk;
            } else {
                layer[j - 1] = sk_at_vk;
            }
        }
        cur_len -= 1;
    }
    sks_vks
}

/// `out[i] = W-hat_i(x) = s_i(x) / s_i(v_i)`, the normalized LCH basis
/// exponents at the K point `x`. Stays entirely in K.
fn normalized_sks_at(x: F64, sks_vks: &[F64], inv_sks_vks: &[F64], out: &mut [F64]) {
    if out.is_empty() {
        return;
    }
    out[0] = x;
    for i in 1..out.len() {
        out[i] = next_s(out[i - 1], sks_vks[i - 1]);
    }
    for (v, &inv) in out.iter_mut().zip(inv_sks_vks) {
        *v *= inv;
    }
}

/// Row entries of an opened level: `F64` at L0 (mixed `mul_base` dot against
/// the E-valued eq weights), `F192` at every deeper level (full E dot).
pub(crate) trait RowElem: Copy + Sync {
    fn dot(row: &[Self], eq: &[F192]) -> F192;
}

impl RowElem for F64 {
    #[inline]
    fn dot(row: &[Self], eq: &[F192]) -> F192 {
        row.iter()
            .zip(eq.iter())
            .map(|(&r, &e)| e.mul_base(r))
            .fold(F192::ZERO, |a, v| a + v)
    }
}

impl RowElem for F192 {
    #[inline]
    fn dot(row: &[Self], eq: &[F192]) -> F192 {
        row.iter()
            .zip(eq.iter())
            .map(|(&r, &e)| r * e)
            .fold(F192::ZERO, |a, v| a + v)
    }
}

fn invert_sks(sks_vks: &[F64]) -> Vec<F64> {
    sks_vks
        .iter()
        .map(|&v| if v.is_zero() { F64::ZERO } else { v.inv() })
        .collect()
}

/// Dense induce: `basis_poly[j] = Σ_i w_i · W-hat_j(q_i)`,
/// `enforced_sum = Σ_i w_i · <row_i, eq(v_challenges, ·)>`, for the per-query
/// batching weights `w` of the level.
///
/// `W-hat_j(q)` is the product of the normalized subspace polynomials `s_k(q)` over the bits `k` set in `j`.
///
/// # Algorithm
///
/// An index splits into its low bits and the rest, `j = j_hi · 2^L + j_lo`:
///
/// ```text
///     basis[j] = Σ_i  (w_i · Π_{k >= L, bit k of j} s_k(q_i))  ·  low_i[j_lo]
///                     \_____________ one E scalar ___________/    \_ in K _/
///
///     low_i[j_lo] = Π_{k < L, bit k of j_lo} s_k(q_i)
/// ```
///
/// - Each query's low table is built once, `2^L` words of K.
/// - Each task owns `2^L` outputs, so no worker keeps a full-length accumulator.
/// - A task's sums stay unreduced until each output is written.
pub(crate) fn induce_sumcheck_poly<T: RowElem>(
    log_msg_cols: usize,
    sks_vks: &[F64],
    opened_rows: &[Vec<T>],
    v_challenges: &[F192],
    queries: &[usize],
    weights: &[F192],
) -> (ArenaVec<F192>, F192) {
    /// Low bits of an output index, tabulated per query: 2^10 words, 8 KiB of K a query.
    const LOW_BITS: usize = 10;
    /// Outputs one pass over the queries accumulates: 128 unreduced sums, 6 KiB.
    const SUB: usize = 128;

    let n = 1usize << log_msg_cols;
    let n_queries = queries.len();
    assert_eq!(opened_rows.len(), n_queries);
    debug_assert_eq!(weights.len(), n_queries);
    let low = log_msg_cols.min(LOW_BITS);
    let eq = build_eq_table_ext(v_challenges);
    let inv_sks_vks = invert_sks(sks_vks);
    debug_assert!(inv_sks_vks.len() > log_msg_cols);

    // Phase 1: per query, its normalized s_k and its low table.
    //
    //     low_i[0] = 1,   low_i[j + 2^k] = low_i[j] · s_k(q_i)   for j < 2^k
    let per_query: Vec<(Vec<F64>, Vec<F64>)> = parallel::map_collect(n_queries, |i| {
        let mut sks_at_x = vec![F64::ZERO; log_msg_cols];
        normalized_sks_at(F64(queries[i] as u64), sks_vks, &inv_sks_vks, &mut sks_at_x);
        let mut table = vec![F64::ONE; 1 << low];
        for (k, &s) in sks_at_x[..low].iter().enumerate() {
            let (lo, hi) = table.split_at_mut(1 << k);
            for (h, &l) in hi[..1 << k].iter_mut().zip(lo.iter()) {
                *h = l * s;
            }
        }
        (sks_at_x, table)
    });

    // Phase 2: the claimed sum, one opened row per query.
    let enforced_sum = opened_rows
        .iter()
        .zip(weights)
        .fold(F192::ZERO, |sum, (row, &w)| sum + T::dot(row, &eq) * w);

    // Phase 3: each task owns the 2^L outputs sharing their high bits.
    //
    // SAFETY: every task writes all of its chunk, and the chunks tile the output.
    let mut basis = unsafe { ArenaVec::<F192>::uninitialized(n) };
    parallel::chunks_mut(&mut basis, 1 << low, |hi_index, out| {
        // Each query's scalar: its weight times its factors on the high bits.
        let scalars: Vec<F192> = per_query
            .iter()
            .zip(weights)
            .map(|((sks_at_x, _), &w)| {
                sks_at_x[low..]
                    .iter()
                    .enumerate()
                    .filter(|&(k, _)| (hi_index >> k) & 1 == 1)
                    .fold(w, |acc, (_, &s)| acc.mul_base(s))
            })
            .collect();
        // Every query adds its scaled low table, 128 outputs at a time.
        for (sub_index, out) in out.chunks_mut(SUB).enumerate() {
            let at = sub_index * SUB;
            let mut acc = [F192Unreduced::ZERO; SUB];
            for ((_, table), &scalar) in per_query.iter().zip(&scalars) {
                for (a, &t) in acc.iter_mut().zip(&table[at..at + out.len()]) {
                    *a ^= scalar.mul_base_unreduced(t);
                }
            }
            for (o, a) in out.iter_mut().zip(acc) {
                *o = a.reduce();
            }
        }
    });
    (basis, enforced_sum)
}

/// Just the `enforced_sum` half of [`induce_sumcheck_poly`]:
///   `enforced_sum = Σ_i w_i · <opened_rows[i], eq(v_challenges, ·)>`
/// Cheap: O(num_queries x num_interleaved). The succinct verifier needs this
/// at level intro time (before the residual challenges are known).
pub(crate) fn induce_sumcheck_enforced_sum<T: RowElem>(
    opened_rows: &[Vec<T>],
    v_challenges: &[F192],
    queries: &[usize],
    weights: &[F192],
) -> F192 {
    assert_eq!(opened_rows.len(), queries.len());
    let eq = build_eq_table_ext(v_challenges);
    debug_assert_eq!(weights.len(), queries.len());
    let mut sum = F192::ZERO;
    for (i, row) in opened_rows.iter().enumerate() {
        debug_assert_eq!(row.len(), eq.len());
        sum += weights[i] * T::dot(row, &eq);
    }
    sum
}

/// SUCCINCT evaluator for the induced basis poly's MLE at residual points
/// (mirror of `whir::induce_sumcheck_evaluate_at_residual`). Replaces the
/// dense basis + `partial_eval_lsb` in the verifier via the closed form:
///   `MLE(basis_poly)(p) = Σ_i w_i · Π_k (1 + p[k] · (1 + W-hat_k(q_i)))`
/// where `q_i = F64(queries[i])` and the K-valued `W-hat_k(q_i)` lifts into E
/// through the char-2 factor. `ris_for_basis` is the fixed residual prefix
/// (length `log_msg_cols - yr_log_n`); returns evaluations at the `2^yr_log_n`
/// points `ris_for_basis ++ y_bits`.
pub(crate) fn induce_sumcheck_evaluate_at_residual(
    log_msg_cols: usize,
    sks_vks: &[F64],
    queries: &[usize],
    weights: &[F192],
    ris_for_basis: &[F192],
    yr_log_n: usize,
) -> ArenaVec<F192> {
    assert_eq!(ris_for_basis.len() + yr_log_n, log_msg_cols);
    let n_queries = queries.len();
    let yr_len = 1usize << yr_log_n;

    debug_assert_eq!(weights.len(), n_queries);
    let inv_sks_vks = invert_sks(sks_vks);
    let prefix_len = ris_for_basis.len();

    // Per-query precomputation: W-hat_k(q) for all k over K, split into a
    // fixed prefix product (E scalar) and the suffix W-hat values varied per y.
    struct PerQuery {
        prefix_prod: F192,
        suffix_w: Vec<F64>, // length = yr_log_n
    }
    let compute_query = |&q: &usize| -> PerQuery {
        let mut sks_at_x = vec![F64::ZERO; log_msg_cols];
        normalized_sks_at(F64(q as u64), sks_vks, &inv_sks_vks, &mut sks_at_x);
        // Prefix product: Π_{k<prefix_len} (1 + ris[k] · (1 + W-hat_k(q)))
        let mut prefix_prod = F192::ONE;
        for k in 0..prefix_len {
            prefix_prod *= F192::ONE + ris_for_basis[k] * (F192::ONE + F192::from(sks_at_x[k]));
        }
        let suffix_w = if log_msg_cols > prefix_len {
            sks_at_x[prefix_len..].to_vec()
        } else {
            Vec::new()
        };
        PerQuery { prefix_prod, suffix_w }
    };
    // Once per recursion level over verify-sized inputs; stay serial below
    // the dispatch crossover (mirror of the original's PAR_FLOOR).
    const PAR_FLOOR: usize = 1024;
    let per_query: Vec<PerQuery> = if n_queries > PAR_FLOOR {
        parallel::map_collect(n_queries, |i| compute_query(&queries[i]))
    } else {
        queries.iter().map(compute_query).collect()
    };

    // For each residual position y, accumulate the suffix product per query.
    let compute_y = |y: usize| -> F192 {
        let mut sum = F192::ZERO;
        for i in 0..n_queries {
            let pq = &per_query[i];
            let mut suffix_prod = F192::ONE;
            for j in 0..yr_log_n {
                let p_j = if (y >> j) & 1 == 1 { F192::ONE } else { F192::ZERO };
                suffix_prod *= F192::ONE + p_j * (F192::ONE + F192::from(pq.suffix_w[j]));
            }
            sum += weights[i] * pq.prefix_prod * suffix_prod;
        }
        sum
    };
    if yr_len > PAR_FLOOR {
        primitives::par_collect_arena(yr_len, compute_y)
    } else {
        (0..yr_len).map(compute_y).collect()
    }
}

/// Transposed forward additive NTT, `F^T`, in place over `2^log_d` E-values
/// with K-twiddles. Forward butterfly is `M = [[1, t], [1, t+1]]`; transpose
/// `M^T = [[1, 1], [t, t+1]]` is `s = a + b; top = s; bot = t*s + b` (here
/// `s.mul_base(t) + b`), applied in reverse layer order. Mirror of
/// `whir::transpose_forward_ntt` (one parallel sweep per layer).
fn transpose_forward_ntt_ext(ntt: &AdditiveNttF64, data: &mut [F192], log_d: usize) {
    debug_assert_eq!(data.len(), 1usize << log_d);
    debug_assert!(log_d <= ntt.log_domain_size());
    transpose_layers_ext(ntt, data, log_d, (0..log_d).rev());
}

/// Elements per cache-resident window of the layer-blocked run below.
const TRANSPOSE_CHUNK: usize = 1 << 16;

/// The transposed-butterfly sweep over `layers`, in the order given: parallel
/// over blocks once there are enough of them, over rows within a block
/// otherwise.
///
/// Layers arrive in descending order, so blocks GROW along the run and the ones
/// that fit a cache-resident window are a prefix. Blocks also nest, so such a
/// window holds complete blocks of every layer in that prefix and the whole
/// prefix runs back-to-back inside it: one read and one write of DRAM traffic
/// for the run instead of one sweep per layer. This is the sub-group
/// decomposition the interleaved encode already uses for its deep layers,
/// applied in the transpose direction.
fn transpose_layers_ext(ntt: &AdditiveNttF64, data: &mut [F192], log_d: usize, layers: impl Iterator<Item = usize>) {
    transpose_layers_ext_windowed(ntt, data, log_d, layers, TRANSPOSE_CHUNK);
}

fn transpose_layers_ext_windowed(
    ntt: &AdditiveNttF64,
    data: &mut [F192],
    log_d: usize,
    layers: impl Iterator<Item = usize>,
    window_len: usize,
) {
    let n_threads = parallel::num_threads();
    let butterfly = |t: F64, top: &mut [F192], bot: &mut [F192]| {
        for (a_ref, b_ref) in top.iter_mut().zip(bot.iter_mut()) {
            let a = *a_ref;
            let b = *b_ref;
            let s = a + b;
            *a_ref = s;
            *b_ref = s.mul_base(t) + b;
        }
    };
    let layers: Vec<usize> = layers.collect();
    debug_assert!(layers.windows(2).all(|w| w[0] > w[1]), "layers descend");
    // Keep a window per worker, or the blocked run costs more in lost
    // parallelism than it saves in traffic.
    let blocked = if data.len() >= window_len.saturating_mul(n_threads) {
        layers
            .iter()
            .position(|&l| (1usize << (log_d - l)) > window_len)
            .unwrap_or(layers.len())
    } else {
        0
    };
    if blocked > 1 {
        parallel::chunks_mut(data, window_len, |c, window: &mut [F192]| {
            let base = c * window_len;
            for &layer in &layers[..blocked] {
                let block_size = 1usize << (log_d - layer);
                let bsh = block_size >> 1;
                for (b, block) in window.chunks_mut(block_size).enumerate() {
                    let (top, bot) = block.split_at_mut(bsh);
                    butterfly(ntt.twiddle(layer, base / block_size + b), top, bot);
                }
            }
        });
    }
    let rest = &layers[if blocked > 1 { blocked } else { 0 }..];
    // The layers left are those whose blocks exceed a window: the lowest ones, 2^g blocks or fewer.
    //
    // When they are exactly g - 1 .. 0, rows `r + i * 2^(d - g)` for i < 2^g pair only with each other.
    // So one gathered pass runs them all, instead of one sweep each.
    let g = rest.len();
    if (1..=GATHER_LOG).contains(&g) && rest.iter().copied().eq((0..g).rev()) {
        transpose_low_layers_gathered(ntt, data, log_d, g);
        return;
    }
    for &layer in rest {
        let num_blocks = 1usize << layer;
        let block_size = 1usize << (log_d - layer);
        let bsh = block_size >> 1;
        if num_blocks >= n_threads {
            parallel::chunks_mut(data, block_size, |block, chunk: &mut [F192]| {
                let (top, bot) = chunk.split_at_mut(bsh);
                butterfly(ntt.twiddle(layer, block), top, bot);
            });
        } else {
            for block in 0..num_blocks {
                let t = ntt.twiddle(layer, block);
                let chunk = &mut data[block * block_size..(block + 1) * block_size];
                let (top, bot) = chunk.split_at_mut(bsh);
                let chunk_len = parallel::recommended_chunk_size(bsh);
                parallel::chunks_mut2(top, bot, chunk_len, |_, top_c, bot_c| butterfly(t, top_c, bot_c));
            }
        }
    }
}

/// Layers the gathered pass takes at most: a group is 2^6 rows.
const GATHER_LOG: usize = 6;

/// Residues one gathered task takes: 32 residues of 64 rows is 48 KiB, which stays in L2.
const GATHER_RESIDUES: usize = 32;

/// The transposed butterflies of layers `g - 1 .. 0`, in one pass over the data.
///
/// # Algorithm
///
/// With `step = 2^(d - g)`, layer `l < g` pairs rows `step * 2^(g - 1 - l)` apart.
///
/// So the rows `r + i * step`, for `i < 2^g`, pair only with each other:
///
/// ```text
///     d = 22, g = 6, step = 2^16:
///
///     rows r, r + 2^16, r + 2 * 2^16, ..., r + 63 * 2^16   one group, for each r < 2^16
/// ```
///
/// Row `r + i * step` sits in block `i >> (g - l)` of layer `l`, whatever `r`: its twiddle depends on `i` alone.
///
/// A task gathers the groups of consecutive residues, runs every layer on them in cache, and scatters them back.
fn transpose_low_layers_gathered(ntt: &AdditiveNttF64, data: &mut [F192], log_d: usize, g: usize) {
    let rows = 1usize << g;
    let step = 1usize << (log_d - g);
    let per_task = GATHER_RESIDUES.min(step);
    let base = parallel::SendPtr(data.as_mut_ptr());
    parallel::for_each(step / per_task, |task| {
        let r0 = task * per_task;
        // Scratch index `i * per_task + j` holds row `r0 + j + i * step`.
        let mut scratch = [F192::ZERO; GATHER_RESIDUES << GATHER_LOG];
        let scratch = &mut scratch[..rows * per_task];

        // Gather: one contiguous run of residues per group row.
        for (i, dst) in scratch.chunks_exact_mut(per_task).enumerate() {
            // SAFETY: tasks own disjoint residue ranges, so no other task touches these rows.
            dst.copy_from_slice(unsafe { base.slice(r0 + i * step, per_task) });
        }

        // Layers g - 1 .. 0, each a butterfly between group rows `half` apart.
        for layer in (0..g).rev() {
            let half = 1usize << (g - 1 - layer);
            for block in 0..1usize << layer {
                let t = ntt.twiddle(layer, block);
                let at = block * 2 * half * per_task;
                let (top, bot) = scratch[at..at + 2 * half * per_task].split_at_mut(half * per_task);
                for (a_ref, b_ref) in top.iter_mut().zip(bot.iter_mut()) {
                    let (a, b) = (*a_ref, *b_ref);
                    let s = a + b;
                    *a_ref = s;
                    *b_ref = s.mul_base(t) + b;
                }
            }
        }

        // Scatter: every group row returns to its place.
        for (i, src) in scratch.chunks_exact(per_task).enumerate() {
            // SAFETY: as for the gather.
            unsafe { base.slice(r0 + i * step, per_task) }.copy_from_slice(src);
        }
    });
}

/// Sparse-prefix variant of [`transpose_forward_ntt_ext`]: the input has only
/// `positions.len()` nonzeros and the first `k` transpose steps (forward
/// layers `log_d-1 .. log_d-k`, pairing distances `1 .. 2^(k-1)`) mix only
/// WITHIN `2^k`-aligned windows. We process just the windows that contain a
/// nonzero (a dense `2^k` transpose each, disjoint so window-parallel),
/// densify, then run the remaining steps as full dense sweeps. Output is
/// identical to `transpose_forward_ntt_ext` on the scattered input. Mirror
/// of `whir::transpose_forward_ntt_sparse`.
fn transpose_forward_ntt_sparse_ext(
    ntt: &AdditiveNttF64,
    positions: &[usize],
    values: &[F192],
    log_d: usize,
) -> ArenaVec<F192> {
    let _span = tracing::info_span!(
        "NTT",
        kind = "transpose induce",
        log_domain = log_d,
        nonzero = positions.len()
    )
    .entered();
    use std::collections::HashMap;
    let n = 1usize << log_d;
    // No prefix for small domains: just scatter + full dense transpose.
    let k = if log_d >= 12 { 8usize.min(log_d) } else { 0 };

    if k == 0 {
        // SAFETY: zero is a valid F192, and the scatter below reads these slots.
        let mut data = unsafe { ArenaVec::<F192>::zeroed(n) };
        for (&p, &v) in positions.iter().zip(values) {
            data[p] += v;
        }
        if log_d > 0 {
            transpose_forward_ntt_ext(ntt, &mut data, log_d);
        }
        return data;
    }

    let wmask = (1usize << k) - 1;
    // Group nonzeros into 2^k windows.
    let mut windows: HashMap<usize, Vec<F192>> = HashMap::new();
    for (&p, &v) in positions.iter().zip(values) {
        let buf = windows.entry(p >> k).or_insert_with(|| vec![F192::ZERO; 1 << k]);
        buf[p & wmask] += v;
    }

    // Steps s = 0..k-1 within each active window, in parallel (windows disjoint).
    let mut win_vec: Vec<(usize, Vec<F192>)> = windows.into_iter().collect();
    parallel::chunks_mut(&mut win_vec, 1, |_, win| {
        let (w, buf) = &mut win[0];
        let w = *w;
        for s in 0..k {
            let layer = log_d - 1 - s;
            let bsh = 1usize << s; // pairing distance
            let block_size = bsh << 1;
            let nblocks = (1usize << k) / block_size;
            for jb in 0..nblocks {
                // global block index = ((w<<k) + jb*block_size) >> (s+1).
                let t = ntt.twiddle(layer, (w << (k - s - 1)) + jb);
                let base = jb * block_size;
                for r in 0..bsh {
                    let a = buf[base + r];
                    let b = buf[base + r + bsh];
                    let sab = a + b;
                    buf[base + r] = sab;
                    buf[base + r + bsh] = sab.mul_base(t) + b;
                }
            }
        }
    });

    // Densify (active windows only; the rest stay zero, which is the correct
    // post-step-(k-1) state for an all-zero window).
    // SAFETY: zero is a valid F192, and the inactive windows must read as zero.
    let mut data = unsafe { ArenaVec::<F192>::zeroed(n) };
    for (w, buf) in &win_vec {
        data[(w << k)..((w + 1) << k)].copy_from_slice(buf);
    }

    // Remaining steps s = k..log_d-1 = forward layers (log_d-1-k) .. 0, dense.
    transpose_layers_ext(ntt, &mut data, log_d, (0..(log_d - k)).rev());
    data
}

/// `F^T`-based fast path for [`induce_sumcheck_poly`]: scatter per-query
/// E-weights into the codeword domain, apply `F^T` with K-twiddles, keep the
/// low `2^log_msg_cols` outputs. Byte-identical output to the dense path
/// (pinned by `induce_via_ntt_matches_dense`). Mirror of
/// `whir::induce_sumcheck_poly_via_ntt` with the L0 mixed row dot.
pub(crate) fn induce_sumcheck_poly_via_ntt_base(
    log_msg_cols: usize,
    log_inv_rate: usize,
    opened_rows: &[Vec<F64>],
    v_challenges: &[F192],
    queries: &[usize],
    weights: &[F192],
) -> (ArenaVec<F192>, F192) {
    let n = 1usize << log_msg_cols;
    let log_block = log_msg_cols + log_inv_rate;
    let block_len = 1usize << log_block;
    let n_queries = queries.len();
    assert_eq!(opened_rows.len(), n_queries);

    let eq = build_eq_table_ext(v_challenges);
    debug_assert_eq!(weights.len(), n_queries);

    let mut enforced_sum = F192::ZERO;
    for i in 0..n_queries {
        enforced_sum += F64::dot(&opened_rows[i], &eq) * weights[i];
    }

    let mut coeffs = if log_block == 0 {
        // SAFETY: zero is a valid F192, and the loop below reads these slots.
        let mut c = unsafe { ArenaVec::<F192>::zeroed(block_len) };
        for i in 0..n_queries {
            c[queries[i]] += weights[i];
        }
        c
    } else {
        let ntt = AdditiveNttF64::standard(log_block);
        transpose_forward_ntt_sparse_ext(&ntt, queries, weights, log_block)
    };
    coeffs.truncate(n);
    (coeffs, enforced_sum)
}

/// Query density threshold for choosing the sparse NTT over dense expansion.
const NTT_QUERIES_PER_BLOWUP: usize = 8;

/// Cost-based dispatch: the NTT overtakes the dense expansion once a level
/// opens more than [`NTT_QUERIES_PER_BLOWUP`] queries per unit of blowup.
#[inline]
pub(crate) fn induce_use_ntt_heuristic(log_msg_cols: usize, log_inv_rate: usize, n_queries: usize) -> bool {
    log_msg_cols >= 12 && n_queries > NTT_QUERIES_PER_BLOWUP * (1usize << log_inv_rate)
}

/// Dispatch between the dense [`induce_sumcheck_poly`] and the sparse
/// [`induce_sumcheck_poly_via_ntt_base`] for L0 (base-field rows). Mirror of
/// `whir::induce_sumcheck_poly_auto`: in the recursive PCS this fires
/// only at the top level (large message domain, many queries); deeper levels
/// stay dense. Both paths produce identical output, so a mis-dispatch only
/// costs time.
pub(crate) fn induce_sumcheck_poly_auto_base(
    log_msg_cols: usize,
    log_inv_rate: usize,
    sks_vks: &[F64],
    opened_rows: &[Vec<F64>],
    v_challenges: &[F192],
    queries: &[usize],
    weights: &[F192],
) -> (ArenaVec<F192>, F192) {
    if induce_use_ntt_heuristic(log_msg_cols, log_inv_rate, queries.len()) {
        induce_sumcheck_poly_via_ntt_base(log_msg_cols, log_inv_rate, opened_rows, v_challenges, queries, weights)
    } else {
        induce_sumcheck_poly(log_msg_cols, sks_vks, opened_rows, v_challenges, queries, weights)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use primitives::test_rng::Rng;

    #[test]
    fn blocked_and_gathered_transposes_match_layer_by_layer() {
        // Invariant: the windowed prefix and the gathered tail compute the plain transposed NTT.
        let mut rng = Rng::new(0x7A55);
        // Fixture state: a window of 2^(d - 6) elements leaves layers 5 .. 0 for the gathered pass.
        //
        //     d = 12:  step 2^6, 32 residues a task
        //     d = 8:   step 2^2, 4 residues a task
        for log_d in [12, 8] {
            let ntt = AdditiveNttF64::standard(log_d);
            let data: Vec<F192> = rng.ext_vec(1 << log_d);

            // Reference: one layer at a time, highest first, every block's butterflies in place.
            let mut want = data.clone();
            for layer in (0..log_d).rev() {
                let half = 1usize << (log_d - 1 - layer);
                for (block, chunk) in want.chunks_mut(2 * half).enumerate() {
                    let t = ntt.twiddle(layer, block);
                    let (top, bot) = chunk.split_at_mut(half);
                    for (a, b) in top.iter_mut().zip(bot.iter_mut()) {
                        let s = *a + *b;
                        (*a, *b) = (s, s.mul_base(t) + *b);
                    }
                }
            }

            let mut got = data;
            transpose_layers_ext_windowed(&ntt, &mut got, log_d, (0..log_d).rev(), 1 << (log_d - 6));
            assert_eq!(got, want, "log_d={log_d}");
        }
    }
}
