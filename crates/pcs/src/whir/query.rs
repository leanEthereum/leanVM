// CREDIT: https://github.com/succinctlabs/flock (flock-core), MIT OR Apache-2.0.
// Copyright (c) 2026 Bain Capital Crypto, LP and Ron Rothblum
// Modifications copyright 2026 Succinct Labs, Benedikt Bunz, William Wang
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! The weight a level's queries induce on its message, in the novel basis.
//!
//! # What is induced
//!
//! A query at position `q` asserts `Enc(f)[q] = c_q`, a weighted claim on `f` with weight `X_j(q)` on coefficient `j`.
//!
//! Batched by the weights `w_i`, a level's queries give one weight:
//!
//! ```text
//!     w[j]  =  sum_i w_i X_j(q_i),    X_j(q) = prod_{k : bit k of j set} s_k(q) / s_k(v_k)
//! ```
//!
//! Here `s_k` is the `k`-th subspace polynomial of the novel basis and `v_k = 2^k` the `k`-th basis vector of `K`.
//!
//! # Two ways to compute it
//!
//! - The direct expansion, per query and coefficient.
//! - The transposed encode of the queries' weights, for a large message opened by many queries.
//!
//! Every subspace-polynomial value lives in `K`; it is lifted into `E` only where it scales an accumulator in `E`.

use crate::ntt::{AdditiveNttF64, transposed_butterfly_lanes};
use parallel::SendPtr;
use primitives::field::{F64, F192, F192Unreduced};
use primitives::multilinear::{eq_table, inner_product, inner_product_base};
use std::collections::HashMap;

/// The subspace polynomials' normalizers on the standard basis, `s_k(v_k)` for `k <= log_n`, and their inverses.
///
/// Each is nonzero: `v_k` lies outside the span of `v_0, ..., v_(k-1)`, where `s_k` vanishes.
#[derive(Clone, Debug)]
pub(crate) struct Normalizers {
    /// `s_k(v_k)`, for `k = 0..=log_n`.
    at_roots: Vec<F64>,
    /// `1 / s_k(v_k)`.
    inverses: Vec<F64>,
}

impl Normalizers {
    /// The normalizers of a domain of `2^log_n` points.
    pub(crate) fn new(log_n: usize) -> Self {
        // The recurrence `s_(k+1)(x) = s_k(x) (s_k(x) + s_k(v_k))`, run on every basis vector above the current one.
        //
        // Row `k` holds `s_k(v_j)` for `j > k`; its first entry gives the next normalizer.
        let mut at_roots = vec![F64::ONE; log_n + 1];
        let mut row: Vec<F64> = (1..=log_n).map(|i| F64(1u64 << i)).collect();
        for k in 0..log_n {
            row = row.iter().map(|&s| s * (s + at_roots[k])).collect();
            at_roots[k + 1] = row.remove(0);
        }
        let inverses = at_roots.iter().map(|s| s.inv()).collect();
        Self { at_roots, inverses }
    }

    /// `s_k(v_k)`, for `k = 0..=log_n`.
    pub(crate) fn at_roots(&self) -> &[F64] {
        &self.at_roots
    }

    /// `1 / s_k(v_k)`, for `k = 0..=log_n`.
    pub(crate) fn inverses(&self) -> &[F64] {
        &self.inverses
    }

    /// The normalized `s_k(x) / s_k(v_k)`, for `k < out.len()`.
    fn normalized_at(&self, x: F64, out: &mut [F64]) {
        // The unnormalized recurrence first, from `s_0(x) = x`.
        let mut s = x;
        for (k, o) in out.iter_mut().enumerate() {
            if k > 0 {
                s *= s + self.at_roots[k - 1];
            }
            *o = s * self.inverses[k];
        }
    }
}

/// `W_m(s)` for `s = F64(2^(m + r))`, the first basis element past a `2^(m + r)`-point domain.
///
/// A hiding commitment's padding is `W_m(X + s) = W_m(X) + W_m(s)` times its polynomial: `W_m` vanishes on the domain's first `2^m` points and maps it onto the span of `W_m(F64(2^b))`, `m <= b < m + r`, which `W_m(s)` lies outside, so the factor vanishes nowhere on the domain.
pub(crate) fn padding_shift(log_msg_cols: usize, log_inv_rate: usize) -> F64 {
    let mut w = vec![F64::ZERO; log_msg_cols + 1];
    Normalizers::new(log_msg_cols).normalized_at(F64(1 << (log_msg_cols + log_inv_rate)), &mut w);
    w[log_msg_cols]
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

/// Queries per unit of blowup above which the transposed encode replaces the direct expansion.
const TRANSPOSED_QUERIES_PER_BLOWUP: usize = 8;

/// One level's queries: their positions in the codeword, and their batching weights.
#[derive(Clone, Copy, Debug)]
pub(crate) struct QueryBatch<'a> {
    positions: &'a [usize],
    weights: &'a [F192],
}

impl<'a> QueryBatch<'a> {
    /// The batch of queries at `positions`, query `i` weighted by `weights[i]`.
    ///
    /// # Panics
    ///
    /// Panics unless there is one weight per query.
    pub(crate) fn new(positions: &'a [usize], weights: &'a [F192]) -> Self {
        assert_eq!(positions.len(), weights.len(), "one weight per query");
        Self { positions, weights }
    }

    /// The batch's claimed sum, from each query's opened row and the level's fold challenges.
    ///
    /// ```text
    ///     sum_i w_i <row_i, eq(fold, .)>
    /// ```
    ///
    /// # Panics
    ///
    /// Panics unless there is one opened row per query.
    pub(crate) fn claimed_sum<T: RowElem>(&self, rows: &[Vec<T>], fold: &[F192]) -> F192 {
        assert_eq!(rows.len(), self.positions.len(), "one opened row per query");
        let eq = eq_table(fold);
        (rows.iter().zip(self.weights)).fold(F192::ZERO, |sum, (row, &w)| sum + w * T::dot(row, &eq))
    }

    /// The weight the batch induces on a message of `2^log_msg_cols` coefficients, encoded at rate `2^-log_inv_rate`.
    ///
    /// A large message opened by many queries takes the transposed encode, the others the direct expansion.
    ///
    /// Both give the same weight.
    pub(crate) fn induced_weight(&self, log_msg_cols: usize, log_inv_rate: usize) -> Vec<F192> {
        if self.takes_transposed(log_msg_cols, log_inv_rate) {
            self.transposed(log_msg_cols, log_inv_rate)
        } else {
            self.expanded(log_msg_cols)
        }
    }

    /// What a padding whose lane fold is `g1` adds to the batch's claimed sum over lanes of `2^m` words at rate `2^-r`, `s` as in [`padding_shift`]:
    ///
    /// ```text
    ///     sum_i w_i W_m(q_i + s) sum_{j < k} g1[j] X_j(q_i)
    /// ```
    pub(crate) fn padding_correction(&self, log_msg_cols: usize, log_inv_rate: usize, g1: &[F192]) -> F192 {
        let normalizers = Normalizers::new(log_msg_cols);
        let shift = padding_shift(log_msg_cols, log_inv_rate);
        let mut w = vec![F64::ZERO; log_msg_cols + 1];
        let mut g = Vec::with_capacity(g1.len());
        (self.positions.iter().zip(self.weights)).fold(F192::ZERO, |acc, (&q, &weight)| {
            normalizers.normalized_at(F64(q as u64), &mut w);
            // `sum_j g1[j] X_j`, folding the top bit of `j` at a time: `X_j` is the product of the `W_b` over the bits `b` of `j`.
            g.clear();
            g.extend_from_slice(g1);
            while g.len() > 1 {
                let half = g.len().next_power_of_two() >> 1;
                let w_b = w[half.trailing_zeros() as usize];
                let (lo, hi) = g.split_at_mut(half);
                for (l, &h) in lo.iter_mut().zip(hi.iter()) {
                    *l += h.mul_base(w_b);
                }
                g.truncate(half);
            }
            let p = g.first().copied().unwrap_or(F192::ZERO);
            acc + weight * p.mul_base(w[log_msg_cols] + shift)
        })
    }

    /// Whether the transposed encode computes the induced weight.
    ///
    /// It does from `2^12` coefficients on, past `TRANSPOSED_QUERIES_PER_BLOWUP` queries per unit of blowup.
    pub(super) const fn takes_transposed(&self, log_msg_cols: usize, log_inv_rate: usize) -> bool {
        log_msg_cols >= 12 && self.positions.len() > TRANSPOSED_QUERIES_PER_BLOWUP * (1usize << log_inv_rate)
    }

    /// The induced weight by the direct expansion.
    ///
    /// # Algorithm
    ///
    /// An index splits into its low `L` bits and the rest, `j = j_hi * 2^L + j_lo`:
    ///
    /// ```text
    ///     w[j]         =  sum_i  (w_i * prod_{k >= L, bit k of j} s_k(q_i))  *  low_i[j_lo]
    ///                            \____ one scalar of E per query and task ____/     \_ in K _/
    ///
    ///     low_i[j_lo]  =  prod_{k < L, bit k of j_lo} s_k(q_i)
    /// ```
    ///
    /// - Each query's low table is built once, `2^L` words of `K`.
    /// - Each task owns `2^L` outputs, so no worker keeps a full-length accumulator.
    /// - A task's sums stay unreduced until each output is written.
    pub(super) fn expanded(&self, log_msg_cols: usize) -> Vec<F192> {
        /// Low bits of an output index, tabulated per query: `2^10` words of `K`, 8 KiB a query.
        const LOW_BITS: usize = 10;
        /// Outputs one pass over the queries accumulates: 128 unreduced sums, 6 KiB.
        const SUB: usize = 128;

        let low = log_msg_cols.min(LOW_BITS);
        let normalizers = Normalizers::new(log_msg_cols);

        // Phase 1: per query, its normalized `s_k` and its low table, doubled one bit at a time.
        //
        //     low_i[0] = 1,   low_i[j + 2^k] = low_i[j] * s_k(q_i)   for j < 2^k
        let per_query: Vec<(Vec<F64>, Vec<F64>)> = parallel::map_collect(self.positions.len(), |i| {
            let mut s = vec![F64::ZERO; log_msg_cols];
            normalizers.normalized_at(F64(self.positions[i] as u64), &mut s);
            let mut table = vec![F64::ONE; 1 << low];
            for (k, &s_k) in s[..low].iter().enumerate() {
                let (lo, hi) = table.split_at_mut(1 << k);
                for (h, &l) in hi[..1 << k].iter_mut().zip(lo.iter()) {
                    *h = l * s_k;
                }
            }
            (s, table)
        });

        // Phase 2: each task owns the `2^L` outputs sharing their high bits.
        let mut weight = Box::new_uninit_slice(1 << log_msg_cols);
        parallel::chunks_mut(&mut weight, 1 << low, |hi_index, out| {
            // Each query's scalar: its weight times its factors on the high bits.
            let scalars: Vec<F192> = (per_query.iter().zip(self.weights))
                .map(|((s, _), &w)| {
                    (s[low..].iter().enumerate())
                        .filter(|&(k, _)| (hi_index >> k) & 1 == 1)
                        .fold(w, |acc, (_, &s_k)| acc.mul_base(s_k))
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
        unsafe { weight.assume_init() }.into_vec()
    }

    /// The induced weight by the transposed encode of the queries' weights.
    ///
    /// The induced weight is the encode matrix's transpose applied to the weights scattered on the codeword domain:
    ///
    /// ```text
    ///     w[j]  =  sum_x X_j(x) u(x),    u(x) = sum_{i : q_i = x} w_i
    /// ```
    ///
    /// Its twiddles are in `K`, and only the low `2^log_msg_cols` outputs are kept.
    pub(super) fn transposed(&self, log_msg_cols: usize, log_inv_rate: usize) -> Vec<F192> {
        let encode = TransposedEncode::new(log_msg_cols + log_inv_rate);
        let mut weight = encode.apply_sparse(self.positions, self.weights, log_inv_rate);
        weight.truncate(1 << log_msg_cols);
        weight
    }
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

/// Elements per cache-resident window of the layer-blocked run.
const TRANSPOSE_CHUNK: usize = 1 << 16;

/// Layers the gathered pass takes at most: a group is `2^6` rows.
const GATHER_LOG: usize = 6;

/// Residues one gathered task takes: 32 residues of 64 rows is 48 KiB, sized to stay in L2.
const GATHER_RESIDUES: usize = 32;

/// The transpose of the additive NTT on a domain of `2^log_d` points, applied to vectors of `E`.
struct TransposedEncode {
    ntt: AdditiveNttF64,
    log_d: usize,
}

impl TransposedEncode {
    /// The transposed encode of a domain of `2^log_d` points.
    fn new(log_d: usize) -> Self {
        Self {
            ntt: AdditiveNttF64::standard(log_d),
            log_d,
        }
    }

    /// The transposed encode of a sparse input, its first `2^(log_d - log_inv_rate)` outputs valid.
    ///
    /// The input is `values` at `positions`, repeated positions adding.
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
    /// A vector of `2^log_d` elements whose first `2^(log_d - log_inv_rate)` are the outputs; the rest are unspecified.
    fn apply_sparse(&self, positions: &[usize], values: &[F192], log_inv_rate: usize) -> Vec<F192> {
        let log_d = self.log_d;
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

        let mut data = vec![F192::ZERO; n];
        if k == 0 {
            for (&p, &v) in positions.iter().zip(values) {
                data[p] += v;
            }
        } else {
            // Group the nonzero inputs into windows of `2^k` elements.
            let wmask = (1usize << k) - 1;
            let mut windows: HashMap<usize, Vec<F192>> = HashMap::new();
            for (&p, &v) in positions.iter().zip(values) {
                let buf = windows.entry(p >> k).or_insert_with(|| vec![F192::ZERO; 1 << k]);
                buf[p & wmask] += v;
            }

            // The prefix layers inside each occupied window, in parallel since windows are disjoint.
            let mut windows: Vec<(usize, Vec<F192>)> = windows.into_iter().collect();
            parallel::chunks_mut(&mut windows, 1, |_, window| {
                let (w, buf) = &mut window[0];
                for s in 0..prefix_steps {
                    let layer = log_d - 1 - s;
                    let half = 1usize << s;
                    for (jb, block) in buf.chunks_mut(2 * half).enumerate() {
                        // The block's index in the whole domain: `((w << k) + jb * 2 half) >> (s + 1)`.
                        let t = self.ntt.twiddle(layer, (*w << (k - s - 1)) + jb);
                        let (top, bot) = block.split_at_mut(half);
                        transposed_butterflies(t, top, bot);
                    }
                }
            });

            // Densify the occupied windows; an empty window stays zero, which its prefix layers would leave it.
            for (w, buf) in &windows {
                data[(w << k)..((w + 1) << k)].copy_from_slice(buf);
            }
        }

        // The dense layers stop before the ones the block fold replaces.
        self.run_layers(&mut data, (log_inv_rate..(log_d - prefix_steps)).rev(), TRANSPOSE_CHUNK);
        fold_blocks(&mut data, log_inv_rate);
        data
    }

    /// The transposed-butterfly sweep over `layers`, which descend, in the order given.
    ///
    /// # Layer blocking
    ///
    /// - Layers descend, so a layer's blocks grow along the run, and the layers whose blocks fit a window are a prefix.
    /// - Blocks nest, so a window of `window_len` elements holds whole blocks of every layer in that prefix.
    /// - That prefix then runs back to back inside each window: one read and one write of memory instead of one per layer.
    ///
    /// # Parallelism
    ///
    /// - The blocked prefix runs one window per task.
    /// - A later layer runs one block per task once there are as many blocks as threads, and splits its rows otherwise.
    /// - When the layers left after that prefix are at most `GATHER_LOG` consecutive ones, one gathered pass runs them.
    fn run_layers(&self, data: &mut [F192], layers: impl Iterator<Item = usize>, window_len: usize) {
        let log_d = self.log_d;
        let n_threads = parallel::num_threads();
        let layers: Vec<usize> = layers.collect();
        debug_assert!(layers.windows(2).all(|w| w[0] > w[1]), "layers descend");
        // Why the size floor: without a window per worker, the blocked run loses more parallelism than it saves traffic.
        let blocked = if data.len() >= window_len.saturating_mul(n_threads) {
            (layers.iter())
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
                    for (b, block) in window.chunks_mut(block_size).enumerate() {
                        let (top, bot) = block.split_at_mut(block_size >> 1);
                        transposed_butterflies(self.ntt.twiddle(layer, base / block_size + b), top, bot);
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
            self.run_gathered(data, low, g);
            return;
        }
        for &layer in rest {
            let num_blocks = 1usize << layer;
            let block_size = 1usize << (log_d - layer);
            let half = block_size >> 1;
            if num_blocks >= n_threads {
                parallel::chunks_mut(data, block_size, |block, chunk: &mut [F192]| {
                    let (top, bot) = chunk.split_at_mut(half);
                    transposed_butterflies(self.ntt.twiddle(layer, block), top, bot);
                });
            } else {
                for (block, chunk) in data.chunks_mut(block_size).enumerate() {
                    let t = self.ntt.twiddle(layer, block);
                    let (top, bot) = chunk.split_at_mut(half);
                    let chunk_len = parallel::recommended_chunk_size(half);
                    parallel::chunks_mut2(top, bot, chunk_len, |_, top, bot| transposed_butterflies(t, top, bot));
                }
            }
        }
    }

    /// The transposed butterflies of layers `low + g - 1` down to `low`, in one gathered pass.
    ///
    /// - The `2^low` outer blocks are independent.
    /// - Within one, the rows `r + i * step` for `i < 2^g` pair only with each other, where `step = 2^(log_d - low - g)`.
    /// - A task gathers a run of consecutive residues `r`, runs every layer on them in cache, and scatters them back.
    ///
    /// Its twiddles include the outer block's offset in the full domain.
    fn run_gathered(&self, data: &mut [F192], low: usize, g: usize) {
        let (log_d, ntt) = (self.log_d, &self.ntt);
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
}

/// Add the `2^log_inv_rate` blocks of `data` into its first block, which is retained.
///
/// Through the omitted lowest `log_inv_rate` layers, a retained output depends only on top outputs, `a' = a + b`.
///
/// So those layers reduce to `N - n` additions and no product, for `N` inputs and `n` retained outputs.
fn fold_blocks(data: &mut [F192], log_inv_rate: usize) {
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
            let encode = TransposedEncode::new(log_d);
            let data: Vec<F192> = rng.ext_vec(1 << log_d);

            // Reference: one layer at a time, highest first, every block's butterflies in place.
            let mut want = data.clone();
            for layer in (low..log_d).rev() {
                let half = 1usize << (log_d - 1 - layer);
                for (block, chunk) in want.chunks_mut(2 * half).enumerate() {
                    let t = encode.ntt.twiddle(layer, block);
                    let (top, bot) = chunk.split_at_mut(half);
                    for (a, b) in top.iter_mut().zip(bot.iter_mut()) {
                        let s = *a + *b;
                        (*a, *b) = (s, s.mul_base(t) + *b);
                    }
                }
            }

            let mut got = data;
            let gathered = GATHER_LOG.min(log_d - low);
            encode.run_layers(&mut got, (low..log_d).rev(), 1 << (log_d - low - gathered));
            assert_eq!(got, want, "log_d={log_d}, low={low}");
        }
    }

    #[test]
    fn the_transposed_encode_is_the_expansion() {
        // Invariant: both ways of computing the induced weight agree, repeated positions included.
        let mut rng = Rng::new(0x1D0C);
        for (log_msg_cols, log_inv_rate, n_queries) in [(12, 1, 40), (12, 2, 70), (13, 1, 17)] {
            let domain = 1usize << (log_msg_cols + log_inv_rate);
            let mut positions: Vec<usize> = (0..n_queries).map(|_| rng.next_u64() as usize % domain).collect();
            positions[1] = positions[0];
            let weights: Vec<F192> = rng.ext_vec(n_queries);
            let batch = QueryBatch::new(&positions, &weights);
            assert_eq!(
                batch.transposed(log_msg_cols, log_inv_rate),
                batch.expanded(log_msg_cols),
                "log_msg_cols={log_msg_cols}, log_inv_rate={log_inv_rate}"
            );
        }
    }
}
