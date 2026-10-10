// CREDIT: https://github.com/succinctlabs/flock (flock-core), MIT OR Apache-2.0.
// Copyright (c) 2026 Bain Capital Crypto, LP and Ron Rothblum
// Modifications copyright 2026 Succinct Labs, Benedikt Bunz, William Wang
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! The induced basis: the weight of a level's batched consistency claims, in the novel basis.
//!
//! # What is induced
//!
//! A query at position `q` asserts `Enc(f)[q] = c_q`, a weighted claim on `f` with weight `X_j(q)` on coefficient `j`.
//! Batched by the weights `w_i`, the level's queries give one weight, the induced basis:
//!
//! ```text
//!     basis[j]  =  sum_i w_i X_j(q_i),    X_j(q) = prod_{k : bit k of j set} s_k(q) / s_k(v_k)
//! ```
//!
//! Here `s_k` is the `k`-th subspace polynomial of the novel basis and `v_k = 2^k` the `k`-th basis vector of `K`.
//!
//! # Three ways to compute it
//!
//! - The dense expansion, per query and output, for every level.
//! - A closed form for the basis's multilinear extension at given points, for the last level.
//! - The transposed NTT of the queries' weights, for L0 when it opens many queries.
//!
//! Every subspace-polynomial value lives in `K`; it is lifted into `E` only where it scales an accumulator in `E`.

use crate::ntt::AdditiveNttF64;
use crate::ntt::transposed_butterfly_lanes;
use parallel::SendPtr;
use primitives::field::{F64, F192, F192Unreduced};
use primitives::multilinear::{eq_table, inner_product, inner_product_base};
use std::collections::HashMap;

/// One step of the subspace-polynomial recurrence: `s_{k+1}(x) = s_k(x) (s_k(x) + s_k(v_k))`.
///
/// `s` is `s_k(x)` and `s_at_root` is `s_k(v_k)`.
#[inline]
fn next_s(s: F64, s_at_root: F64) -> F64 {
    s * (s + s_at_root)
}

/// The normalizers `s_k(v_k)` for `k = 0..=log_n`, over `K`, with `v_k = 2^k`.
///
/// Row `i` of the recurrence holds `s_i(v_j)` for `j > i`, and its first entry gives `s_{i+1}(v_{i+1})`.
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

/// Write `out[i] = s_i(x) / s_i(v_i)`, the normalized subspace polynomials at the point `x` of `K`.
///
/// A zero normalizer has inverse zero in `inv_sks_vks`.
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

/// An entry of an opened row: a word of `K` at L0, an element of `E` at every deeper level.
pub(crate) trait RowElem: Copy + Sync {
    /// The inner product `sum_l row[l] * eq[l]`, in `E`.
    fn dot(row: &[Self], eq: &[F192]) -> F192;
}

impl RowElem for F64 {
    #[inline]
    fn dot(row: &[Self], eq: &[F192]) -> F192 {
        inner_product_base(row, eq)
    }
}

impl RowElem for F192 {
    #[inline]
    fn dot(row: &[Self], eq: &[F192]) -> F192 {
        inner_product(row, eq)
    }
}

/// The inverse of each normalizer, zero for a zero one.
fn invert_sks(sks_vks: &[F64]) -> Vec<F64> {
    sks_vks
        .iter()
        .map(|&v| if v.is_zero() { F64::ZERO } else { v.inv() })
        .collect()
}

/// The dense induced basis over `2^log_msg_cols` coefficients, and the batch's claimed sum.
///
/// ```text
///     basis[j]      =  sum_i w_i X_j(q_i)
///     enforced_sum  =  sum_i w_i <row_i, eq(v_challenges, .)>
/// ```
///
/// `w` is `weights`, the level's batching powers, one per query.
/// `X_j(q)` is the product of the normalized `s_k(q)` over the bits `k` set in `j`.
///
/// # Algorithm
///
/// An index splits into its low `L` bits and the rest, `j = j_hi * 2^L + j_lo`:
///
/// ```text
///     basis[j]     =  sum_i  (w_i * prod_{k >= L, bit k of j} s_k(q_i))  *  low_i[j_lo]
///                            \____ one scalar of E per query and task ____/     \_ in K _/
///
///     low_i[j_lo]  =  prod_{k < L, bit k of j_lo} s_k(q_i)
/// ```
///
/// - Each query's low table is built once, `2^L` words of `K`.
/// - Each task owns `2^L` outputs, so no worker keeps a full-length accumulator.
/// - A task's sums stay unreduced until each output is written.
///
/// # Panics
///
/// Panics unless there is one opened row per query.
pub(crate) fn induce_sumcheck_poly<T: RowElem>(
    log_msg_cols: usize,
    sks_vks: &[F64],
    opened_rows: &[Vec<T>],
    v_challenges: &[F192],
    queries: &[usize],
    weights: &[F192],
) -> (Vec<F192>, F192) {
    /// Low bits of an output index, tabulated per query: `2^10` words of `K`, 8 KiB a query.
    const LOW_BITS: usize = 10;
    /// Outputs one pass over the queries accumulates: 128 unreduced sums, 6 KiB.
    const SUB: usize = 128;

    let n = 1usize << log_msg_cols;
    let n_queries = queries.len();
    assert_eq!(opened_rows.len(), n_queries);
    debug_assert_eq!(weights.len(), n_queries);
    let low = log_msg_cols.min(LOW_BITS);
    let eq = eq_table(v_challenges);
    let inv_sks_vks = invert_sks(sks_vks);
    debug_assert!(inv_sks_vks.len() > log_msg_cols);

    // Phase 1: per query, its normalized `s_k` and its low table, doubled one bit at a time.
    //
    //     low_i[0] = 1,   low_i[j + 2^k] = low_i[j] * s_k(q_i)   for j < 2^k
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

    // Phase 3: each task owns the `2^L` outputs sharing their high bits.
    let mut basis = Box::new_uninit_slice(n);
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
        // Every query adds its scaled low table, `SUB` outputs at a time.
        for (sub_index, out) in out.chunks_mut(SUB).enumerate() {
            let at = sub_index * SUB;
            let mut acc = [F192Unreduced::ZERO; SUB];
            for ((_, table), &scalar) in per_query.iter().zip(&scalars) {
                for (a, &t) in acc.iter_mut().zip(&table[at..at + out.len()]) {
                    *a ^= scalar.mul_base_unreduced(t);
                }
            }
            for (o, a) in out.iter_mut().zip(acc) {
                o.write(a.reduce());
            }
        }
    });
    // SAFETY: every task wrote all of its chunk, and the chunks tile the output.
    (unsafe { basis.assume_init() }.into_vec(), enforced_sum)
}

/// The batch's claimed sum alone: `sum_i w_i <opened_rows[i], eq(v_challenges, .)>`.
///
/// It costs one inner product per query, each of one row's length.
///
/// # Panics
///
/// Panics unless there is one opened row per query.
pub(crate) fn induce_sumcheck_enforced_sum<T: RowElem>(
    opened_rows: &[Vec<T>],
    v_challenges: &[F192],
    queries: &[usize],
    weights: &[F192],
) -> F192 {
    assert_eq!(opened_rows.len(), queries.len());
    let eq = eq_table(v_challenges);
    debug_assert_eq!(weights.len(), queries.len());
    let mut sum = F192::ZERO;
    for (i, row) in opened_rows.iter().enumerate() {
        debug_assert_eq!(row.len(), eq.len());
        sum += weights[i] * T::dot(row, &eq);
    }
    sum
}

/// The induced basis on its Boolean cube of `log_msg_cols` variables, from its closed form.
///
/// With `q_i` the position `queries[i]` read in `K`:
///
/// ```text
///     basis(y)  =  sum_i w_i prod_k (1 + y_k (1 + s_k(q_i) / s_k(v_k)))
/// ```
///
/// # Returns
///
/// One value per `y`, the bits of the output index being `y`'s coordinates, lowest first.
pub(crate) fn induce_basis_on_cube(
    log_msg_cols: usize,
    sks_vks: &[F64],
    queries: &[usize],
    weights: &[F192],
) -> Vec<F192> {
    debug_assert_eq!(weights.len(), queries.len());
    let inv_sks_vks = invert_sks(sks_vks);

    // Per query, the normalized `s_k(q)`.
    let normalized: Vec<Vec<F64>> = (queries.iter())
        .map(|&q| {
            let mut sks_at_q = vec![F64::ZERO; log_msg_cols];
            normalized_sks_at(F64(q as u64), sks_vks, &inv_sks_vks, &mut sks_at_q);
            sks_at_q
        })
        .collect();

    // At a Boolean `y`, factor `k` is one where `y_k = 0`, and the normalized `s_k(q)` where `y_k = 1`.
    (0..1usize << log_msg_cols)
        .map(|y| {
            (normalized.iter().zip(weights)).fold(F192::ZERO, |sum, (s, &w)| {
                let product = (s.iter().enumerate())
                    .filter(|&(k, _)| (y >> k) & 1 == 1)
                    .fold(F64::ONE, |acc, (_, &s_k)| acc * s_k);
                sum + w.mul_base(product)
            })
        })
        .collect()
}

/// The transposed butterfly `s = a + b; a' = s; b' = t*s + b` on every pair of a top and a bottom row.
///
/// An element of `E` is three words of `K` and `t` is in `K`, so the rows are lanes of `K` sharing one twiddle.
fn transposed_butterflies(t: F64, top: &mut [F192], bot: &mut [F192]) {
    // SAFETY:
    // - An element of `E` is laid out as three words of `K`, and an element of `K` as one word.
    // - So each view covers exactly the memory of the slice it came from, which it shadows for its lifetime.
    let (top, bot) = unsafe {
        (
            std::slice::from_raw_parts_mut(top.as_mut_ptr().cast::<F64>(), 3 * top.len()),
            std::slice::from_raw_parts_mut(bot.as_mut_ptr().cast::<F64>(), 3 * bot.len()),
        )
    };
    transposed_butterfly_lanes(top, bot, t);
}

/// Elements per cache-resident window of the layer-blocked run below.
const TRANSPOSE_CHUNK: usize = 1 << 16;

/// The transposed-butterfly sweep over `layers`, which descend, in the order given.
///
/// # Layer blocking
///
/// Layers descend, so a layer's blocks grow along the run, and the layers whose blocks fit a window are a prefix.
/// Blocks nest, so a window holds whole blocks of every layer in that prefix.
///
/// That prefix then runs back to back inside each window: one read and one write of memory instead of one per layer.
///
/// # Parallelism
///
/// - The blocked prefix runs one window per task.
/// - A later layer runs one block per task once there are as many blocks as threads, and splits its rows otherwise.
/// - When the layers left after that prefix are at most `GATHER_LOG` consecutive ones, one gathered pass runs them.
fn transpose_layers_ext(ntt: &AdditiveNttF64, data: &mut [F192], log_d: usize, layers: impl Iterator<Item = usize>) {
    transpose_layers_ext_windowed(ntt, data, log_d, layers, TRANSPOSE_CHUNK);
}

/// The sweep of the function above, with a window of `window_len` elements, which tests shrink.
fn transpose_layers_ext_windowed(
    ntt: &AdditiveNttF64,
    data: &mut [F192],
    log_d: usize,
    layers: impl Iterator<Item = usize>,
    window_len: usize,
) {
    let n_threads = parallel::num_threads();
    let layers: Vec<usize> = layers.collect();
    debug_assert!(layers.windows(2).all(|w| w[0] > w[1]), "layers descend");
    // Why the size floor: without a window per worker, the blocked run loses more parallelism than it saves traffic.
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
                    transposed_butterflies(ntt.twiddle(layer, base / block_size + b), top, bot);
                }
            }
        });
    }
    let rest = &layers[if blocked > 1 { blocked } else { 0 }..];
    // The layers left take the gathered pass when they are at most `GATHER_LOG` consecutive ones, ending at `low`.
    // The run may stop above layer zero: its `2^low` outer blocks are then independent.
    let g = rest.len();
    let low = rest.last().copied().unwrap_or(0);
    if (1..=GATHER_LOG).contains(&g) && rest.iter().copied().eq((low..low + g).rev()) {
        transpose_low_layers_gathered(ntt, data, log_d, low, g);
        return;
    }
    for &layer in rest {
        let num_blocks = 1usize << layer;
        let block_size = 1usize << (log_d - layer);
        let bsh = block_size >> 1;
        if num_blocks >= n_threads {
            parallel::chunks_mut(data, block_size, |block, chunk: &mut [F192]| {
                let (top, bot) = chunk.split_at_mut(bsh);
                transposed_butterflies(ntt.twiddle(layer, block), top, bot);
            });
        } else {
            for block in 0..num_blocks {
                let t = ntt.twiddle(layer, block);
                let chunk = &mut data[block * block_size..(block + 1) * block_size];
                let (top, bot) = chunk.split_at_mut(bsh);
                let chunk_len = parallel::recommended_chunk_size(bsh);
                parallel::chunks_mut2(top, bot, chunk_len, |_, top_c, bot_c| {
                    transposed_butterflies(t, top_c, bot_c);
                });
            }
        }
    }
}

/// Layers the gathered pass takes at most: a group is `2^6` rows.
const GATHER_LOG: usize = 6;

/// Residues one gathered task takes: 32 residues of 64 rows is 48 KiB, sized to stay in L2.
const GATHER_RESIDUES: usize = 32;

/// The transposed butterflies of layers `low + g - 1` down to `low`, in one gathered pass.
///
/// The `2^low` outer blocks are independent.
/// Within one, the rows `r + i * step` for `i < 2^g` pair only with each other, where `step = 2^(log_d - low - g)`.
///
/// A task gathers a run of consecutive residues `r`, runs every layer on them in cache, and scatters them back.
/// Its twiddles include the outer block's offset in the full domain.
fn transpose_low_layers_gathered(ntt: &AdditiveNttF64, data: &mut [F192], log_d: usize, low: usize, g: usize) {
    let rows = 1usize << g;
    let step = 1usize << (log_d - low - g);
    let per_task = GATHER_RESIDUES.min(step);
    let base = SendPtr(data.as_mut_ptr());
    let tasks_per_block = step / per_task;
    parallel::for_each((1usize << low) * tasks_per_block, |task| {
        let outer = task / tasks_per_block;
        let r0 = outer * (1usize << (log_d - low)) + (task % tasks_per_block) * per_task;
        // Scratch index `i * per_task + j` holds row `r0 + j + i * step`.
        let mut scratch = [F192::ZERO; GATHER_RESIDUES << GATHER_LOG];
        let scratch = &mut scratch[..rows * per_task];

        // Gather: one contiguous run of residues per group row.
        for (i, dst) in scratch.chunks_exact_mut(per_task).enumerate() {
            // SAFETY: the rows `r0 + j + i * step`, `j < per_task`, lie inside this task's outer block.
            // Tasks own disjoint pairs of outer block and residue range, so no other task touches these rows.
            dst.copy_from_slice(unsafe { base.slice(r0 + i * step, per_task) });
        }

        // Relative layers g - 1 .. 0 pair group rows `half` apart.
        for layer in (0..g).rev() {
            let half = 1usize << (g - 1 - layer);
            for block in 0..1usize << layer {
                let t = ntt.twiddle(low + layer, (outer << layer) + block);
                let at = block * 2 * half * per_task;
                let (top, bot) = scratch[at..at + 2 * half * per_task].split_at_mut(half * per_task);
                transposed_butterflies(t, top, bot);
            }
        }

        // Scatter: every group row returns to its place.
        for (i, src) in scratch.chunks_exact(per_task).enumerate() {
            // SAFETY: as for the gather.
            unsafe { base.slice(r0 + i * step, per_task) }.copy_from_slice(src);
        }
    });
}

/// Add the `2^log_inv_rate` blocks of `data` into its first block, which is retained.
///
/// Through the omitted lowest `log_inv_rate` layers, a retained output depends only on top outputs, `a' = a + b`.
/// So those layers reduce to `N - n` additions and no product, for `N` inputs and `n` retained outputs.
fn fold_transpose_blocks(data: &mut [F192], log_inv_rate: usize) {
    if log_inv_rate == 0 {
        return;
    }
    let n = data.len() >> log_inv_rate;
    let (retained, rest) = data.split_at_mut(n);
    let chunk_len = parallel::recommended_chunk_size(n);
    parallel::chunks_mut(retained, chunk_len, |chunk, out| {
        let start = chunk * chunk_len;
        for block in rest.chunks_exact(n) {
            for (out, &value) in out.iter_mut().zip(&block[start..]) {
                *out += value;
            }
        }
    });
}

/// The transposed forward additive NTT of a sparse input, keeping only the first `2^(log_d - log_inv_rate)` outputs.
///
/// The input is `values` at `positions` of a domain of `2^log_d` elements, repeated positions adding.
///
/// # Algorithm
///
/// 1. The first `k` transposed layers mix only within `2^k`-aligned windows, so only occupied windows run them.
/// 2. The windows are written into a dense vector, the empty ones staying zero.
/// 3. The remaining layers run densely down to layer `log_inv_rate`.
/// 4. The lowest `log_inv_rate` layers are replaced by adding the blocks into the first one.
///
/// # Returns
///
/// A vector of `2^log_d` elements whose first `2^(log_d - log_inv_rate)` are the outputs.
/// The caller truncates it; the remaining entries are unspecified.
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

    debug_assert!(log_inv_rate <= log_d);
    let n = 1usize << log_d;
    // Windows of `2^8` elements from a domain of `2^12` up; their layers stop before the block fold.
    let k = if log_d >= 12 { 8usize.min(log_d) } else { 0 };
    let prefix_steps = k.min(log_d - log_inv_rate);

    if k == 0 {
        let mut data = vec![F192::ZERO; n];
        for (&p, &v) in positions.iter().zip(values) {
            data[p] += v;
        }
        transpose_layers_ext(ntt, &mut data, log_d, (log_inv_rate..log_d).rev());
        fold_transpose_blocks(&mut data, log_inv_rate);
        return data;
    }

    let wmask = (1usize << k) - 1;
    // Group the nonzero inputs into windows of `2^k` elements.
    let mut windows: HashMap<usize, Vec<F192>> = HashMap::new();
    for (&p, &v) in positions.iter().zip(values) {
        let buf = windows.entry(p >> k).or_insert_with(|| vec![F192::ZERO; 1 << k]);
        buf[p & wmask] += v;
    }

    // The prefix layers inside each occupied window, in parallel since windows are disjoint.
    let mut win_vec: Vec<(usize, Vec<F192>)> = windows.into_iter().collect();
    parallel::chunks_mut(&mut win_vec, 1, |_, win| {
        let (w, buf) = &mut win[0];
        let w = *w;
        for s in 0..prefix_steps {
            let layer = log_d - 1 - s;
            let bsh = 1usize << s; // pairing distance
            let block_size = bsh << 1;
            let nblocks = (1usize << k) / block_size;
            for jb in 0..nblocks {
                // The block's index in the whole domain: `((w << k) + jb * block_size) >> (s + 1)`.
                let t = ntt.twiddle(layer, (w << (k - s - 1)) + jb);
                let (top, bot) = buf[jb * block_size..(jb + 1) * block_size].split_at_mut(bsh);
                transposed_butterflies(t, top, bot);
            }
        }
    });

    // Densify the occupied windows; an empty window stays zero, which its prefix layers would leave it.
    let mut data = vec![F192::ZERO; n];
    for (w, buf) in &win_vec {
        data[(w << k)..((w + 1) << k)].copy_from_slice(buf);
    }

    // The dense layers stop before the ones the block fold replaces.
    transpose_layers_ext(ntt, &mut data, log_d, (log_inv_rate..(log_d - prefix_steps)).rev());
    fold_transpose_blocks(&mut data, log_inv_rate);
    data
}

/// The induced basis and the claimed sum at L0, through the transposed encode.
///
/// The basis is the transposed encode matrix applied to the queries' weights:
///
/// ```text
///     basis[j]  =  sum_x X_j(x) u(x),    u(x) = sum_{i : q_i = x} w_i
/// ```
///
/// So the weights are scattered into the codeword domain and the transposed NTT runs with twiddles in `K`.
/// The low `2^log_msg_cols` outputs are kept.
///
/// The output equals the dense expansion's, and a test pins the two together.
///
/// # Panics
///
/// Panics unless there is one opened row per query.
pub(crate) fn induce_sumcheck_poly_via_ntt_base(
    log_msg_cols: usize,
    log_inv_rate: usize,
    opened_rows: &[Vec<F64>],
    v_challenges: &[F192],
    queries: &[usize],
    weights: &[F192],
) -> (Vec<F192>, F192) {
    let n = 1usize << log_msg_cols;
    let log_block = log_msg_cols + log_inv_rate;
    let n_queries = queries.len();
    assert_eq!(opened_rows.len(), n_queries);

    let eq = eq_table(v_challenges);
    debug_assert_eq!(weights.len(), n_queries);

    let mut enforced_sum = F192::ZERO;
    for i in 0..n_queries {
        enforced_sum += F64::dot(&opened_rows[i], &eq) * weights[i];
    }

    let ntt = AdditiveNttF64::standard(log_block);
    let mut coeffs = transpose_forward_ntt_sparse_ext(&ntt, queries, weights, log_block, log_inv_rate);
    coeffs.truncate(n);
    (coeffs, enforced_sum)
}

/// Queries per unit of blowup above which the transposed NTT replaces the dense expansion.
const NTT_QUERIES_PER_BLOWUP: usize = 8;

/// Whether the transposed NTT should compute the induced basis.
///
/// It does once the message has at least `2^12` coefficients.
/// The level must also open more than `NTT_QUERIES_PER_BLOWUP` queries per unit of blowup.
#[inline]
pub(crate) const fn induce_use_ntt_heuristic(log_msg_cols: usize, log_inv_rate: usize, n_queries: usize) -> bool {
    log_msg_cols >= 12 && n_queries > NTT_QUERIES_PER_BLOWUP * (1usize << log_inv_rate)
}

/// The induced basis and the claimed sum at L0, by the dense expansion or the transposed NTT.
///
/// Only L0, with its large message and many queries, reaches the transposed NTT.
/// Both paths give the same output, so the choice only costs time.
pub(crate) fn induce_sumcheck_poly_auto_base(
    log_msg_cols: usize,
    log_inv_rate: usize,
    sks_vks: &[F64],
    opened_rows: &[Vec<F64>],
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

#[cfg(test)]
mod tests {
    use super::*;
    use primitives::test_util::Rng;

    #[test]
    fn blocked_and_gathered_transposes_match_layer_by_layer() {
        // Invariant: the windowed prefix and the gathered tail compute the plain transposed NTT.
        let mut rng = Rng::new(0x7A55);
        // At most six layers are left to the gathered pass.
        // The shapes cover a nonzero lowest layer, several outer blocks and fewer than 32 residues.
        for (log_d, low) in [(12, 0), (12, 1), (12, 3), (12, 6), (8, 0), (8, 2), (8, 7)] {
            let ntt = AdditiveNttF64::standard(log_d);
            let data: Vec<F192> = rng.ext_vec(1 << log_d);

            // Reference: one layer at a time, highest first, every block's butterflies in place.
            let mut want = data.clone();
            for layer in (low..log_d).rev() {
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
            let gathered = GATHER_LOG.min(log_d - low);
            transpose_layers_ext_windowed(&ntt, &mut got, log_d, (low..log_d).rev(), 1 << (log_d - low - gathered));
            assert_eq!(got, want, "log_d={log_d}, low={low}");
        }
    }
}
