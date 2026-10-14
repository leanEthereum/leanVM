// CREDIT: https://github.com/succinctlabs/flock (flock-core), MIT OR Apache-2.0.
// Copyright (c) 2026 Bain Capital Crypto, LP and Ron Rothblum
// Modifications copyright 2026 Succinct Labs, Benedikt Bunz, William Wang
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! A level's queries: their positions, and the weight they induce on the level's message.
//!
//! # Where queries land
//!
//! The positions are stratified: each binary digit of the query count is a group, its queries spread over the cosets of their top bits.
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

use crate::ntt::{AdditiveNtt, NovelBasis, basis_values};
use fiat_shamir::Challenger;
use fiat_shamir::arith::{Arith, Native};
use primitives::field::{F64, F192, F192Unreduced, Subfield};
use primitives::multilinear::eq_table;

/// Where a query of a batch lands: the top `bits` bits of its position are `index`, the rest uniform.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Stratum {
    /// How many of the position's top bits are fixed.
    pub bits: usize,
    /// Their value.
    pub index: usize,
}

impl Stratum {
    /// The strata of a batch of `count` queries into `2^depth` positions, in query order.
    ///
    /// # Overview
    ///
    /// The batch is cut by the binary digits of `count`, highest first.
    ///
    /// ```text
    ///     a group of 2^g queries, s = min(g, depth):
    ///         query j fixes the top s bits of its position to j mod 2^s
    ///         so each of the 2^s cosets of those bits holds equally many of the group's queries
    /// ```
    ///
    /// # Why it is sound
    ///
    /// - A set every query misses with probability at most `1 - delta` is missed by the batch with probability at most `(1 - delta)^count`.
    /// - That is the bound of independent queries (the PCS annex, `thm:rbr`).
    /// - The top `s` levels of a group's Merkle paths are then one complete subtree, hashed once by the verifier.
    pub fn batch(count: usize, depth: usize) -> Vec<Self> {
        let mut out = Vec::with_capacity(count);
        let mut g = usize::BITS as usize;
        while g > 0 {
            g -= 1;
            if count >> g & 1 == 1 {
                Self::push_group(&mut out, g, g.min(depth));
            }
        }
        out
    }

    /// A group of `2^g` queries: query `j` fixes its top `bits` bits to `j mod 2^bits`.
    fn push_group(out: &mut Vec<Self>, g: usize, bits: usize) {
        let mut j = 0;
        while j < 1usize << g {
            out.push(Self {
                bits,
                index: j & ((1 << bits) - 1),
            });
            j += 1;
        }
    }
}

/// Sample `count` query positions of `depth` bits, in transcript order.
///
/// - Each squeezed element of `E` yields `floor(192 / depth)` positions: its disjoint `depth`-bit chunks, low bits first.
/// - Each position then takes its stratum: its top bits are replaced by the stratum's.
///
/// Positions are neither sorted nor deduplicated.
///
/// A repeated position opens the same authenticated row again, which is harmless.
pub(crate) fn sample_queries(ch: &mut impl Challenger, depth: usize, count: usize) -> Vec<usize> {
    let per = 192 / depth;
    let mut out = Vec::with_capacity(count);
    while out.len() < count {
        let v: F192 = ch.verifier_message();
        let take = per.min(count - out.len());
        push_chunks(&mut out, [v.c0, v.c1, v.c2], depth, take);
    }
    let strata = Stratum::batch(count, depth);
    let mut i = 0;
    while i < out.len().min(strata.len()) {
        let s = strata[i];
        let low = depth - s.bits;
        out[i] = (out[i] & ((1 << low) - 1)) | s.index << low;
        i += 1;
    }
    out
}

/// Push the first `take` disjoint `depth`-bit chunks of the limbs, low bits first.
fn push_chunks(out: &mut Vec<usize>, limbs: [u64; 3], depth: usize, take: usize) {
    let mut j = 0;
    while j < take {
        let off = j * depth;
        let (li, sh) = (off / 64, off % 64);
        let mut chunk = limbs[li] >> sh;
        if sh + depth > 64 {
            chunk |= limbs[li + 1] << (64 - sh);
        }
        out.push(chunk as usize & ((1 << depth) - 1));
        j += 1;
    }
}

/// The padding of a hiding commitment's level-0 lanes, as both sides take its share off a folded row.
///
/// A lane of `2^m` words is padded by `W_m(X + s) R(X)`, `R` of degree below `k` in the novel basis.
///
/// # Why the shift
///
/// `s = F64(2^(m + r))` is the first basis element past a `2^(m + r)`-point domain, and the factor must vanish nowhere on the domain.
///
/// - `W_m` vanishes on the domain's first `2^m` points.
/// - It is `F_2`-linear and injective on the span of the basis elements from `m` up.
/// - So it maps the domain onto the span of `W_m(2^b)`, `m <= b < m + r`, which `W_m(s)` lies outside.
pub(crate) struct Padding {
    /// The log of a lane's words, `m`.
    log_msg_cols: usize,
    /// `W_m(s)`, the padding factor's shift.
    shift: F64,
    /// The subspace polynomials up to `W_m`.
    basis: NovelBasis,
}

impl Padding {
    /// The padding of lanes of `2^log_msg_cols` words at rate `2^-log_inv_rate`.
    pub(crate) fn new(log_msg_cols: usize, log_inv_rate: usize) -> Self {
        let basis = NovelBasis::new(log_msg_cols);
        let mut normalized = vec![F64::ZERO; log_msg_cols + 1];
        basis.normalized_at(F64(1 << (log_msg_cols + log_inv_rate)), &mut normalized);
        Self {
            log_msg_cols,
            shift: normalized[log_msg_cols],
            basis,
        }
    }

    /// `W_m(s)`, the constant the padding factor `W_m(X + s) = W_m(X) + W_m(s)` adds.
    pub(crate) const fn shift(&self) -> F64 {
        self.shift
    }

    /// The share at `x` of a padding whose lane fold is `g1`.
    ///
    /// ```text
    ///     W_m(x + s) * sum_j g1[j] X_j(x)
    /// ```
    ///
    /// Adding it, which in characteristic two takes it off, leaves the folded data's codeword.
    ///
    /// The same code runs natively, in the verifier, and in the recursion machine's rows.
    pub(crate) fn share<A: Arith>(&self, ar: &mut A, x: A::E, g1: &[A::E]) -> A::E {
        let m = self.log_msg_cols;
        let inverses = self.basis.inverses();
        // W_b(x) for the bits of j < k, then W_m(x), by the subspace polynomials' recurrence.
        let bits = g1.len().next_power_of_two().trailing_zeros() as usize;
        let mut s = x;
        let mut w = Vec::with_capacity(bits);
        // An index loop rather than an enumerating iterator.
        let mut b = 0;
        while b <= m {
            if b > 0 {
                s = self.basis.next(ar, s, b - 1);
            }
            if b < bits {
                w.push(ar.mul_const(s, F192::from(inverses[b])));
            }
            b += 1;
        }
        let w_m = ar.mul_const(s, F192::from(inverses[m]));
        let w_m = ar.add_const(w_m, F192::from(self.shift));
        // sum_j g1[j] X_j(x), folding the top bit of j at a time: X_j is the product of W_b over the bits b of j.
        let mut g = g1.to_vec();
        while g.len() > 1 {
            let half = g.len().next_power_of_two() >> 1;
            let w_b = w[half.trailing_zeros() as usize];
            for j in 0..g.len() - half {
                g[j] = ar.mul_add(w_b, g[j + half], g[j]);
            }
            g.truncate(half);
        }
        if g.is_empty() { ar.zero() } else { ar.mul(w_m, g[0]) }
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
    /// Panics unless there is one opened row per query, each one fold wide.
    pub(crate) fn claimed_sum<T: Subfield>(&self, rows: &[Vec<T>], fold: &[F192]) -> F192 {
        assert_eq!(rows.len(), self.positions.len(), "one opened row per query");
        let eq = eq_table(fold);
        (rows.iter().zip(self.weights)).fold(F192::ZERO, |sum, (row, &w)| {
            assert_eq!(row.len(), eq.len(), "a row is one fold's width");
            sum + w * T::dot(&eq, row, F192::ZERO)
        })
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

    /// What a padding whose lane fold is `g1` adds to the batch's claimed sum: each query's share, weighted.
    pub(crate) fn padding_correction(&self, padding: &Padding, g1: &[F192]) -> F192 {
        (self.positions.iter().zip(self.weights)).fold(F192::ZERO, |acc, (&q, &weight)| {
            let x = F192::from(F64(q as u64));
            acc + weight * padding.share(&mut Native, x, g1)
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
        let basis = NovelBasis::new(log_msg_cols);

        // Phase 1: per query, its normalized `s_k`, and its basis polynomials over the low bits.
        let per_query: Vec<(Vec<F64>, Vec<F64>)> = parallel::map_collect(self.positions.len(), |i| {
            let mut s = vec![F64::ZERO; log_msg_cols];
            basis.normalized_at(F64(self.positions[i] as u64), &mut s);
            let table = basis_values(&s[..low]);
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
        let ntt = AdditiveNtt::standard(log_msg_cols + log_inv_rate);
        let mut weight = ntt.transpose_sparse(self.positions, self.weights, log_inv_rate);
        weight.truncate(1 << log_msg_cols);
        weight
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use primitives::test_util::Rng;

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

    #[test]
    fn each_group_of_strata_covers_its_cosets_equally() {
        // Invariant: each group covers every coset of its fixed bits equally often, which the stratified queries' soundness rests on.
        for depth in [1usize, 3, 7, 22] {
            for count in 1..=300usize {
                let strata = Stratum::batch(count, depth);
                assert_eq!(strata.len(), count);
                let mut at = 0;
                for g in (0..usize::BITS as usize).rev().filter(|&g| count >> g & 1 == 1) {
                    let group = &strata[at..at + (1 << g)];
                    let bits = g.min(depth);
                    let mut hits = vec![0usize; 1 << bits];
                    for s in group {
                        assert_eq!(s.bits, bits, "count {count}, depth {depth}");
                        hits[s.index] += 1;
                    }
                    assert!(
                        hits.iter().all(|&h| h == 1 << (g - bits)),
                        "count {count}, depth {depth}"
                    );
                    at += 1 << g;
                }
            }
        }
    }
}
