// CREDIT: https://github.com/succinctlabs/flock (flock-core), MIT OR Apache-2.0.
// Copyright (c) 2026 Bain Capital Crypto, LP and Ron Rothblum
// Modifications copyright 2026 Succinct Labs, Benedikt Bunz, William Wang
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! LCH novel-basis induction of the per-level sumcheck basis polynomial: the
//! dense per-query expansion, its succinct residual evaluator, and the sparse
//! transposed-NTT fast path with the dispatch between them.

use crate::ntt::AdditiveNttF64;
use crate::whir::build_eq_table_ext;
use primitives::field::{F64, F192};

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
/// `whir::eval_sk_at_vks`. Public for the recursion harness, which dumps
/// these vanishing-polynomial values as guest hints (base-field, embedded into
/// the tower with both extension limbs zero).
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
/// batching weights `w` of [`primitives::field::powers`]. Mirror of the
/// dense `whir::induce_sumcheck_poly` (per-worker accumulation).
///
/// The LCH doubling recurrence runs into a HALF-size scratch and its last level
/// expands straight into the worker's accumulator, so each query touches the
/// accumulator once instead of writing a full-size table and adding it back.
/// Addition in E is XOR, so reassociating across workers is bit-exact.
pub(crate) fn induce_sumcheck_poly<T: RowElem>(
    log_msg_cols: usize,
    sks_vks: &[F64],
    opened_rows: &[Vec<T>],
    v_challenges: &[F192],
    queries: &[usize],
    weights: &[F192],
) -> (Vec<F192>, F192) {
    let n = 1usize << log_msg_cols;
    let n_queries = queries.len();
    assert_eq!(opened_rows.len(), n_queries);
    debug_assert_eq!(
        v_challenges.len(),
        opened_rows
            .first()
            .map(|r| r.len().trailing_zeros() as usize)
            .unwrap_or(0)
    );

    let eq = build_eq_table_ext(v_challenges);
    debug_assert_eq!(weights.len(), n_queries);
    let inv_sks_vks = invert_sks(sks_vks);
    debug_assert!(inv_sks_vks.len() > log_msg_cols);

    let half = 1usize << log_msg_cols.saturating_sub(1);
    parallel::map_reduce_with_state(
        n_queries,
        || (vec![F64::ZERO; log_msg_cols.max(1)], vec![F192::ZERO; half]),
        // SAFETY: zero is a valid F192, and the expansion below accumulates into it.
        || (vec![F192::ZERO; n], F192::ZERO),
        |(sks_at_x, scratch), (accum_basis, local_sum), i| {
            let ap = weights[i];
            *local_sum += T::dot(&opened_rows[i], &eq) * ap;

            if log_msg_cols == 0 {
                accum_basis[0] += ap;
                return;
            }
            let q_field = F64(queries[i] as u64);
            normalized_sks_at(q_field, sks_vks, &inv_sks_vks, &mut sks_at_x[..log_msg_cols]);
            scratch[0] = ap;
            for k in 0..log_msg_cols - 1 {
                let s_at_x = sks_at_x[k];
                let (lo, hi) = scratch.split_at_mut(1usize << k);
                for (h, &l) in hi.iter_mut().zip(lo.iter()) {
                    *h = l.mul_base(s_at_x);
                }
            }
            let s_at_x = sks_at_x[log_msg_cols - 1];
            let (lo, hi) = accum_basis.split_at_mut(half);
            for ((l, h), &v) in lo.iter_mut().zip(hi.iter_mut()).zip(scratch.iter()) {
                *l += v;
                *h += v.mul_base(s_at_x);
            }
        },
        |(mut basis_poly, sum), (partial, partial_sum)| {
            const PAR_THRESHOLD: usize = 4096;
            if n < PAR_THRESHOLD {
                for (acc, &v) in basis_poly.iter_mut().zip(partial.iter()) {
                    *acc += v;
                }
            } else {
                let chunk = parallel::recommended_chunk_size(n);
                parallel::chunks_mut_zip(&mut basis_poly, &partial, chunk, |_, accs, vs| {
                    for (acc, &v) in accs.iter_mut().zip(vs) {
                        *acc += v;
                    }
                });
            }
            (basis_poly, sum + partial_sum)
        },
    )
}

/// Just the `enforced_sum` half of [`induce_sumcheck_poly`]:
///   `enforced_sum = Σ_i w_i · <opened_rows[i], eq(v_challenges, ·)>`
/// Cheap: O(num_queries x num_interleaved). The prover needs it for its last
/// level, whose induced basis it never materializes.
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

/// SUCCINCT evaluator for the induced basis poly's MLE at residual points,
/// in place of the dense basis, via the closed form:
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
) -> Vec<F192> {
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
    // Once per opening over query-count-sized inputs; stay serial below
    // the dispatch crossover.
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
        primitives::par_collect(yr_len, compute_y)
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
    for &layer in &layers[if blocked > 1 { blocked } else { 0 }..] {
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

/// Sparse-prefix variant of [`transpose_forward_ntt_ext`], keeping only the first
/// `keep` outputs: the input has only `positions.len()` nonzeros, and the first
/// `k` transpose steps (forward layers `log_d-1 .. log_d-k`, pairing distances
/// `1 .. 2^(k-1)`) mix only WITHIN `2^k`-aligned windows. We process just the
/// windows that contain a nonzero (a dense `2^k` transpose each, disjoint so
/// window-parallel), then the remaining steps in two sweeps of the buffer (see
/// [`transpose_dense_rest`]). Output is identical to the first `keep` entries of
/// `transpose_forward_ntt_ext` on the scattered input. Mirror of
/// `whir::transpose_forward_ntt_sparse`.
fn transpose_forward_ntt_sparse_ext(
    ntt: &AdditiveNttF64,
    positions: &[usize],
    values: &[F192],
    log_d: usize,
    keep: usize,
) -> Vec<F192> {
    let _span = tracing::info_span!(
        "NTT",
        kind = "transpose induce",
        log_domain = log_d,
        nonzero = positions.len()
    )
    .entered();
    transpose_sparse_windowed(ntt, positions, values, log_d, keep, TRANSPOSE_WINDOW_LOG)
}

fn transpose_sparse_windowed(
    ntt: &AdditiveNttF64,
    positions: &[usize],
    values: &[F192],
    log_d: usize,
    keep: usize,
    window_log: usize,
) -> Vec<F192> {
    use std::collections::HashMap;
    let n = 1usize << log_d;
    assert!(keep.is_power_of_two() && keep <= n);
    // No prefix for small domains: just scatter + full dense transpose.
    let k = if log_d >= 12 { 8usize.min(log_d) } else { 0 };

    if k == 0 {
        // SAFETY: zero is a valid F192, and the scatter below reads these slots.
        let mut data = vec![F192::ZERO; n];
        for (&p, &v) in positions.iter().zip(values) {
            data[p] += v;
        }
        if log_d > 0 {
            transpose_forward_ntt_ext(ntt, &mut data, log_d);
        }
        data.truncate(keep);
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
    win_vec.sort_unstable_by_key(|(w, _)| *w);
    transpose_dense_rest(ntt, &win_vec, k, log_d, keep, window_log)
}

/// Rows, as a log, of the cache-resident windows of [`transpose_dense_rest`].
const TRANSPOSE_WINDOW_LOG: usize = 15;

/// Consecutive residues one gathered group of [`transpose_dense_rest`] takes: eight E values are three whole cache lines.
const TRANSPOSE_RESIDUES: usize = 8;

/// The dense steps after the sparse prefix, in two sweeps of the buffer.
///
/// ```text
///     window pass:    one task per 2^w-row window, built from the sparse windows inside it,
///                     every layer whose blocks fit the window run there
///     gathered pass:  one task per group of rows r + i * 2^w, for 8 consecutive residues r,
///                     the remaining top layers run in a scratch, layer 0 only for the outputs kept
/// ```
fn transpose_dense_rest(
    ntt: &AdditiveNttF64,
    windows: &[(usize, Vec<F192>)],
    k: usize,
    log_d: usize,
    keep: usize,
    window_log: usize,
) -> Vec<F192> {
    use crate::ntt::{prefetch, transposed_butterfly_lanes};
    let n = 1usize << log_d;
    let w_log = window_log.min(log_d).max(k);
    let win = 1usize << w_log;
    // The top layers left after the windows, run as one gathered transform of 2^top rows.
    let top = log_d - w_log;
    let as_words = |e: &mut [F192]| {
        // SAFETY: an F192 is three F64 words with no padding.
        unsafe { std::slice::from_raw_parts_mut(e.as_mut_ptr().cast::<F64>(), 3 * e.len()) }
    };

    // SAFETY: the window pass writes every slot before the gathered pass reads it.
    let mut data = unsafe { primitives::uninit_vec::<F192>(n) };
    parallel::chunks_mut(&mut data, win, |c, window| {
        window.fill(F192::ZERO);
        let base = c << w_log;
        let first = windows.partition_point(|(w, _)| (*w << k) < base);
        for (w, buf) in windows[first..].iter().take_while(|(w, _)| (*w << k) < base + win) {
            window[(*w << k) - base..][..buf.len()].copy_from_slice(buf);
        }
        // Layers whose blocks fit the window, block sizes 2^(k+1) .. 2^w.
        for layer in (top..log_d - k).rev() {
            let block_size = 1usize << (log_d - layer);
            for (b, block) in window.chunks_mut(block_size).enumerate() {
                let (lo, hi) = block.split_at_mut(block_size / 2);
                transposed_butterfly_lanes(
                    as_words(lo),
                    as_words(hi),
                    ntt.twiddle(layer, (base >> (log_d - layer)) + b),
                );
            }
        }
    });
    if top == 0 {
        data.truncate(keep);
        return data;
    }
    assert!(keep < n, "layer 0 keeps only its top half");
    // Rows kept from each group: those below `keep`.

    let rows = 1usize << top;
    let kept_rows = (keep >> w_log).max(1);
    let group = TRANSPOSE_RESIDUES.min(win);
    let base = parallel::SendPtr(data.as_mut_ptr());
    parallel::for_each_chunk(win / group, |lo, hi| {
        let mut scratch = vec![F192::ZERO; rows * group];
        for g in lo..hi {
            let r = g * group;
            let at = |i: usize| (i << w_log) + r;
            for (i, dst) in scratch.chunks_exact_mut(group).enumerate() {
                if i + 8 < rows {
                    prefetch(base.0.wrapping_add(at(i + 8)).cast::<F64>(), 3 * group);
                }
                // SAFETY: the window pass wrote every row, and this group alone owns these residues.
                dst.copy_from_slice(unsafe { base.slice(at(i), group) });
            }
            // Layer `layer` pairs rows 2^(top-1-layer) apart, inside blocks of 2^(top-layer) rows.
            for layer in (0..top).rev() {
                let block_rows = 1usize << (top - layer);
                for (b, block) in scratch.chunks_mut(block_rows * group).enumerate() {
                    let (lo, hi) = block.split_at_mut(block_rows / 2 * group);
                    if kept_rows <= block_rows / 2 {
                        // Every later layer reads only the first `kept_rows` of each block, all in its top
                        // half, whose output is the sum.
                        for (a, &b) in lo[..kept_rows * group].iter_mut().zip(hi.iter()) {
                            *a += b;
                        }
                    } else {
                        transposed_butterfly_lanes(as_words(lo), as_words(hi), ntt.twiddle(layer, b));
                    }
                }
            }
            for (i, src) in scratch.chunks_exact(group).take(kept_rows).enumerate() {
                // SAFETY: as above.
                unsafe { base.slice(at(i), group) }.copy_from_slice(src);
            }
        }
    });
    data.truncate(keep);
    data
}

/// `F^T`-based fast path for [`induce_sumcheck_poly`]: scatter per-query
/// E-weights into the codeword domain, apply `F^T` with K-twiddles, keep the
/// low `2^log_msg_cols` outputs. Byte-identical output to the dense path
/// (pinned by `induce_via_ntt_matches_dense`).
pub(crate) fn induce_sumcheck_poly_via_ntt<T: RowElem>(
    log_msg_cols: usize,
    log_inv_rate: usize,
    opened_rows: &[Vec<T>],
    v_challenges: &[F192],
    queries: &[usize],
    weights: &[F192],
) -> (Vec<F192>, F192) {
    let n = 1usize << log_msg_cols;
    let log_block = log_msg_cols + log_inv_rate;
    let block_len = 1usize << log_block;
    let n_queries = queries.len();
    assert_eq!(opened_rows.len(), n_queries);
    assert!(queries.iter().all(|&q| q < block_len), "queries lie in the codeword");

    let eq = build_eq_table_ext(v_challenges);
    debug_assert_eq!(weights.len(), n_queries);

    let mut enforced_sum = F192::ZERO;
    for i in 0..n_queries {
        enforced_sum += T::dot(&opened_rows[i], &eq) * weights[i];
    }

    let mut coeffs = if log_block == 0 {
        // SAFETY: zero is a valid F192, and the loop below reads these slots.
        let mut c = vec![F192::ZERO; block_len];
        for i in 0..n_queries {
            c[queries[i]] += weights[i];
        }
        c
    } else {
        let ntt = AdditiveNttF64::standard(log_block);
        transpose_forward_ntt_sparse_ext(&ntt, queries, weights, log_block, n)
    };
    coeffs.truncate(n);
    (coeffs, enforced_sum)
}

/// Cost-based dispatch: the dense expansion costs a pass over the `2^log_msg_cols`
/// outputs per query, the NTT a few passes over the `2^log_inv_rate` times larger
/// codeword domain, so the NTT wins once a level opens more queries than its blowup.
#[inline]
pub(crate) fn induce_use_ntt_heuristic(log_msg_cols: usize, log_inv_rate: usize, n_queries: usize) -> bool {
    log_msg_cols >= 12 && n_queries > 1usize << log_inv_rate
}

/// Dispatch between the dense [`induce_sumcheck_poly`] and the sparse
/// [`induce_sumcheck_poly_via_ntt`]. Both paths produce identical output, so a
/// mis-dispatch only costs time.
pub(crate) fn induce_sumcheck_poly_auto<T: RowElem>(
    log_msg_cols: usize,
    log_inv_rate: usize,
    sks_vks: &[F64],
    opened_rows: &[Vec<T>],
    v_challenges: &[F192],
    queries: &[usize],
    weights: &[F192],
) -> (Vec<F192>, F192) {
    if induce_use_ntt_heuristic(log_msg_cols, log_inv_rate, queries.len()) {
        induce_sumcheck_poly_via_ntt(log_msg_cols, log_inv_rate, opened_rows, v_challenges, queries, weights)
    } else {
        induce_sumcheck_poly(log_msg_cols, sks_vks, opened_rows, v_challenges, queries, weights)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use primitives::test_rng::Rng;

    /// The sparse transpose against the dense one, with windows small enough to leave a gathered pass.
    #[test]
    fn sparse_transpose_matches_dense() {
        let mut rng = Rng::new(0x7A);
        for (log_d, window_log, keep_log) in [(13usize, 9usize, 12usize), (14, 11, 11), (12, 12, 11), (16, 8, 15)] {
            let ntt = AdditiveNttF64::standard(log_d);
            let n = 1usize << log_d;
            let positions: Vec<usize> = (0..50).map(|_| rng.next_u64() as usize % n).collect();
            let values = rng.ext_vec(positions.len());
            let mut want = vec![F192::ZERO; n];
            for (&p, &v) in positions.iter().zip(&values) {
                want[p] += v;
            }
            transpose_forward_ntt_ext(&ntt, &mut want, log_d);
            want.truncate(1 << keep_log);
            let got = transpose_sparse_windowed(&ntt, &positions, &values, log_d, 1 << keep_log, window_log);
            assert_eq!(got, want, "log_d={log_d}, window_log={window_log}");
        }
    }
}
