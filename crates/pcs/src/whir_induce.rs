// CREDIT: https://github.com/succinctlabs/flock (flock-core), MIT OR Apache-2.0.
// Copyright (c) 2026 Bain Capital Crypto, LP and Ron Rothblum
// Modifications copyright 2026 Succinct Labs, Benedikt Bunz, William Wang
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! LCH novel-basis induction of the per-level sumcheck basis polynomial: the
//! dense per-query expansion, its succinct residual evaluator, and the sparse
//! transposed-NTT fast path with the dispatch between them.

use crate::ntt::{AdditiveNttF64, transpose_butterfly_lanes};
use crate::whir::build_eq_table_ext;
use crate::whir_ntt_ext::words_mut;
use primitives::field::{F64, F192, Weights8, dot_base};

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

/// `sks_vks[k] = s_k(v_k)` for `k = 0..=log_n`, over K. Public for the recursion harness, which dumps
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
/// batching weights `w` of [`primitives::field::powers`].
///
/// `W-hat_j(q) = Π_k W-hat_k(q)^(bit k of j)` is a K value and a tensor over the
/// bits of `j`. Split at `lo` bits, `basis_poly[j] = Σ_i (w_i · high_i(j >> lo)) ·
/// low_i(j mod 2^lo)`: one packed mixed dot over the queries per output.
pub(crate) fn induce_sumcheck_poly<T: RowElem>(
    log_msg_cols: usize,
    sks_vks: &[F64],
    opened_rows: &[T],
    v_challenges: &[F192],
    queries: &[usize],
    weights: &[F192],
) -> (Vec<F192>, F192) {
    let enforced_sum = induce_sumcheck_enforced_sum(opened_rows, v_challenges, queries, weights);
    (induce_basis(log_msg_cols, sks_vks, queries, weights), enforced_sum)
}

/// The basis half of [`induce_sumcheck_poly`]: `basis_poly[j] = Σ_i w_i · W-hat_j(q_i)`.
pub(crate) fn induce_basis(log_msg_cols: usize, sks_vks: &[F64], queries: &[usize], weights: &[F192]) -> Vec<F192> {
    let n_queries = queries.len();
    assert_eq!(weights.len(), n_queries);
    let inv_sks_vks = invert_sks(sks_vks);
    let lo = log_msg_cols / 2;
    let padded = n_queries.next_multiple_of(8);
    // `low[j * padded + i] = low_i(j)`, `high[i << (log_msg_cols - lo) | j] = high_i(j)`.
    let mut low = vec![F64::ZERO; padded << lo];
    let mut high = Vec::with_capacity(n_queries << (log_msg_cols - lo));
    let mut sks = vec![F64::ZERO; log_msg_cols];
    let mut tensor = Vec::with_capacity(1 << lo);
    for (i, &q) in queries.iter().enumerate() {
        normalized_sks_at(F64(q as u64), sks_vks, &inv_sks_vks, &mut sks);
        tensor.clear();
        extend_tensor_k(&mut tensor, &sks[..lo]);
        for (j, &v) in tensor.iter().enumerate() {
            low[j * padded + i] = v;
        }
        extend_tensor_k(&mut high, &sks[lo..]);
    }
    // `packed[j * (padded / 8) + g]` holds the weights `w_i · high_i(j)` of the queries `8g..8g + 8`.
    let groups = padded / 8;
    // SAFETY: the fill writes every element before it reads any.
    let packed = unsafe {
        primitives::filled_vec(groups << (log_msg_cols - lo), |packed| {
            parallel::chunks_mut(packed, groups, |j, row| {
                let scaled = |i: usize| match weights.get(i) {
                    Some(w) => w.mul_base(high[(i << (log_msg_cols - lo)) | j]),
                    None => F192::ZERO,
                };
                for (g, slot) in row.iter_mut().enumerate() {
                    *slot = Weights8::new(&std::array::from_fn(|t| scaled(8 * g + t)));
                }
            });
        })
    };
    // SAFETY: the fill writes every element before it reads any.
    unsafe {
        primitives::filled_vec(1 << log_msg_cols, |basis| {
            parallel::chunks_mut(basis, 1 << lo, |j, out: &mut [F192]| {
                for (out, low) in out.iter_mut().zip(low.chunks_exact(padded)) {
                    *out = dot_base(&packed[j * groups..][..groups], low).reduce();
                }
            });
        })
    }
}

/// Appends `t[j] = Π_k s[k]^(bit k of j)`, over K, to `out`.
fn extend_tensor_k(out: &mut Vec<F64>, s: &[F64]) {
    let start = out.len();
    out.push(F64::ONE);
    for &x in s {
        for j in start..out.len() {
            out.push(out[j] * x);
        }
    }
}

/// Just the `enforced_sum` half of [`induce_sumcheck_poly`]:
///   `enforced_sum = Σ_i w_i · <opened_rows[i], eq(v_challenges, ·)>`
/// Cheap: O(num_queries x num_interleaved). The prover needs it for its last
/// level, whose induced basis it never materializes.
pub(crate) fn induce_sumcheck_enforced_sum<T: RowElem>(
    opened_rows: &[T],
    v_challenges: &[F192],
    queries: &[usize],
    weights: &[F192],
) -> F192 {
    let eq = build_eq_table_ext(v_challenges);
    assert_eq!(opened_rows.len(), queries.len() * eq.len());
    debug_assert_eq!(weights.len(), queries.len());
    let mut sum = F192::ZERO;
    for (row, &w) in opened_rows.chunks_exact(eq.len()).zip(weights) {
        sum += w * T::dot(row, &eq);
    }
    sum
}

/// The transposed forward butterfly, applied to each pair of E elements as K words. The forward
/// butterfly is `M = [[1, t], [1, t+1]]`, so `M^T = [[1, 1], [t, t+1]]` is
/// `s = a + b; top = s; bot = t*s + b`. At `t = 0`, the first block of a layer, it needs no product.
fn transpose_butterfly_ext(t: F64, top: &mut [F192], bot: &mut [F192]) {
    if t.is_zero() {
        top.iter_mut().zip(bot.iter()).for_each(|(a, &b)| *a += b);
    } else {
        transpose_butterfly_lanes(words_mut(top), words_mut(bot), t);
    }
}

/// Log of the elements per window of the first pass of [`transpose_forward_ntt_sparse_ext`].
const WINDOW_LOG: usize = 10;
/// Elements per column strip of its second pass.
const STRIP: usize = 16;

/// `F^T` of a sparse input, keeping only the low `2^(log_d - log_inv_rate)` outputs.
///
/// The input has `positions.len()` nonzeros. Transpose step `s` mixes only within
/// `2^(s+1)`-aligned blocks, and every step acts within one of the `2^log_inv_rate`
/// replicas of the message domain. The last `log_inv_rate` steps pair across
/// replicas and every kept output is a `top = a + b` of them, so they collapse to
/// a sum over the replicas: the transpose of the encode's free replication.
///
/// The steps run as a two-level decomposition, so that a replica is never swept
/// layer by layer:
/// - Pass 1 cuts the domain into windows of `2^WINDOW_LOG` elements, runs the steps
///   that stay inside a window on the windows that hold a nonzero (the others stay
///   zero), and stores each strip of `STRIP` columns of them together.
/// - Pass 2 runs the steps that pair windows, one strip of columns at a time over
///   the rows (windows) of each replica, and sums the replicas. A layer skips the
///   blocks of rows that are still zero, as pass 1 does, and the sum is the only
///   thing written to the output.
fn transpose_forward_ntt_sparse_ext(
    ntt: &AdditiveNttF64,
    positions: &[usize],
    values: &[F192],
    log_d: usize,
    log_inv_rate: usize,
) -> Vec<F192> {
    let _span = tracing::info_span!(
        "NTT",
        kind = "transpose induce",
        log_domain = log_d,
        nonzero = positions.len()
    )
    .entered();
    let log_keep = log_d - log_inv_rate;
    let log_window = WINDOW_LOG.min(log_keep);
    let (n_keep, window, strip) = (1usize << log_keep, 1usize << log_window, STRIP.min(1 << log_window));
    let (k, n_replicas) = (log_keep - log_window, 1usize << log_inv_rate);
    let rows = 1usize << k;
    let mut nonzeros: Vec<(usize, F192)> = positions.iter().copied().zip(values.iter().copied()).collect();
    nonzeros.sort_unstable_by_key(|&(p, _)| p);
    let mut occupied = vec![false; 1 << (log_d - log_window)];
    for &(p, _) in &nonzeros {
        occupied[p >> log_window] = true;
    }

    // Window `r` of replica `j`, strip `c` is at `j * n_keep + (c * rows + r) * strip`: a strip's rows are contiguous.
    // SAFETY: pass 1 writes every element of an occupied window, and pass 2 reads only those.
    let mut stage = unsafe { primitives::uninit_vec::<F192>(1 << log_d) };
    let stage_ptr = parallel::SendPtr(stage.as_mut_ptr());
    parallel::for_each_chunk(occupied.len(), |first, end| {
        let mut data = vec![F192::ZERO; window];
        for w in (first..end).filter(|&w| occupied[w]) {
            let range = nonzeros.partition_point(|&(p, _)| p < w << log_window)
                ..nonzeros.partition_point(|&(p, _)| p < (w + 1) << log_window);
            data.fill(F192::ZERO);
            transpose_window(ntt, &nonzeros[range], &mut data, w << log_window, log_d);
            let (replica, row) = (w / rows, w % rows);
            for (c, src) in data.chunks_exact(strip).enumerate() {
                // SAFETY: each (window, strip) pair owns its `strip` elements.
                unsafe { stage_ptr.slice(replica * n_keep + (c * rows + row) * strip, strip) }.copy_from_slice(src);
            }
        }
    });

    // Per replica and layer `j` of pass 2, the blocks of `2^(j+1)` rows that are not zero, with their twiddles.
    // Layer `i = replica * k + j` is `plan[ends[i]..ends[i + 1]]`.
    let (mut plan, mut ends, mut live) = (Vec::new(), vec![0], vec![false; rows]);
    for replica in 0..n_replicas {
        live.copy_from_slice(&occupied[replica * rows..(replica + 1) * rows]);
        for j in 0..k {
            let len = 2 << j;
            let layer = log_d - log_window - 1 - j;
            for b in 0..rows / len {
                if live[b * len..(b + 1) * len].contains(&true) {
                    live[b * len..(b + 1) * len].fill(true);
                    plan.push((b, ntt.twiddle(layer, (replica << (k - 1 - j)) + b)));
                }
            }
            ends.push(plan.len());
        }
    }

    let layers = |replica: usize| (replica * k..(replica + 1) * k).map(|i| &plan[ends[i]..ends[i + 1]]);

    // SAFETY: pass 2 writes every element.
    let mut kept = unsafe { primitives::uninit_vec::<F192>(n_keep) };
    let kept_ptr = parallel::SendPtr(kept.as_mut_ptr());
    parallel::for_each_chunk(window / strip, |first, end| {
        let (mut sum, mut tile) = (vec![F192::ZERO; rows * strip], vec![F192::ZERO; rows * strip]);
        let stream = primitives::stream::Stream::new();
        for c in first..end {
            let run_replica = |tile: &mut [F192], replica: usize| {
                for (r, row) in tile.chunks_exact_mut(strip).enumerate() {
                    if occupied[replica * rows + r] {
                        row.copy_from_slice(&stage[replica * n_keep + (c * rows + r) * strip..][..strip]);
                    } else {
                        row.fill(F192::ZERO);
                    }
                }
                transpose_rows(tile, k, layers(replica));
            };
            run_replica(&mut sum, 0);
            for replica in 1..n_replicas {
                run_replica(&mut tile, replica);
                sum.iter_mut().zip(&tile).for_each(|(s, &t)| *s += t);
            }
            for (r, src) in sum.chunks_exact(strip).enumerate() {
                // SAFETY: each (strip, row) pair owns its `strip` elements.
                unsafe { stream.copy_uninit(kept_ptr.add(r * window + c * strip), src) };
            }
        }
    });
    kept
}

/// The steps of [`transpose_forward_ntt_sparse_ext`] that act within one window `data` of the
/// domain, at `offset`: it holds zeros but for the `nonzeros`, whose positions are in the window.
fn transpose_window(ntt: &AdditiveNttF64, nonzeros: &[(usize, F192)], data: &mut [F192], offset: usize, log_d: usize) {
    let log_window = data.len().ilog2() as usize;
    let mut local = Vec::with_capacity(nonzeros.len());
    for &(p, v) in nonzeros {
        data[p - offset] += v;
        local.push(p - offset);
    }
    let mut blocks: Vec<usize> = Vec::with_capacity(local.len());
    let mut s = 0;
    while s < log_window {
        blocks.clear();
        blocks.extend(local.iter().map(|&p| p >> (s + 1)));
        blocks.sort_unstable();
        blocks.dedup();
        if 2 * (blocks.len() << (s + 1)) > data.len() {
            break;
        }
        let (layer, half) = (log_d - 1 - s, 1usize << s);
        for &b in &blocks {
            let (top, bot) = data[2 * b * half..2 * (b + 1) * half].split_at_mut(half);
            transpose_butterfly_ext(ntt.twiddle(layer, (offset >> (s + 1)) + b), top, bot);
        }
        s += 1;
    }
    for layer in (log_d - log_window..log_d - s).rev() {
        let block_size = 1usize << (log_d - layer);
        for (b, block) in data.chunks_exact_mut(block_size).enumerate() {
            let (top, bot) = block.split_at_mut(block_size / 2);
            transpose_butterfly_ext(ntt.twiddle(layer, offset / block_size + b), top, bot);
        }
    }
}

/// One layer per entry of `plan` over the `2^k` equal rows of `tile`, row distance `1, 2, 4, ..`:
/// the `(block, twiddle)` pairs to butterfly. Rows pair element by element, so a block of
/// `2^(j+1)` rows is one contiguous pair of halves.
fn transpose_rows<'a>(tile: &mut [F192], k: usize, plan: impl Iterator<Item = &'a [(usize, F64)]>) {
    for (j, blocks) in plan.enumerate() {
        let len = tile.len() >> (k - 1 - j);
        for &(b, t) in blocks {
            let (top, bot) = tile[b * len..(b + 1) * len].split_at_mut(len / 2);
            transpose_butterfly_ext(t, top, bot);
        }
    }
}

/// `F^T`-based fast path for [`induce_sumcheck_poly`]: scatter per-query
/// E-weights into the codeword domain, apply `F^T` with K-twiddles, keep the
/// low `2^log_msg_cols` outputs. Byte-identical output to the dense path
/// (pinned by `induce_via_ntt_matches_dense`).
pub(crate) fn induce_sumcheck_poly_via_ntt_base(
    log_msg_cols: usize,
    log_inv_rate: usize,
    opened_rows: &[F64],
    v_challenges: &[F192],
    queries: &[usize],
    weights: &[F192],
) -> (Vec<F192>, F192) {
    let log_block = log_msg_cols + log_inv_rate;
    let enforced_sum = induce_sumcheck_enforced_sum(opened_rows, v_challenges, queries, weights);

    let ntt = AdditiveNttF64::standard(log_block);
    let coeffs = transpose_forward_ntt_sparse_ext(&ntt, queries, weights, log_block, log_inv_rate);
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
/// [`induce_sumcheck_poly_via_ntt_base`] for L0 (base-field rows): in the recursive PCS this fires
/// only at the top level (large message domain, many queries); deeper levels
/// stay dense. Both paths produce identical output, so a mis-dispatch only
/// costs time.
pub(crate) fn induce_sumcheck_poly_auto_base(
    log_msg_cols: usize,
    log_inv_rate: usize,
    sks_vks: &[F64],
    opened_rows: &[F64],
    v_challenges: &[F192],
    queries: &[usize],
    weights: &[F192],
) -> (Vec<F192>, F192) {
    if induce_use_ntt_heuristic(log_msg_cols, log_inv_rate, queries.len()) {
        induce_sumcheck_poly_via_ntt_base(log_msg_cols, log_inv_rate, opened_rows, v_challenges, queries, weights)
    } else {
        induce_sumcheck_poly(log_msg_cols, sks_vks, opened_rows, v_challenges, queries, weights)
    }
}
