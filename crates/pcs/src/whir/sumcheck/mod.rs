// CREDIT: https://github.com/succinctlabs/flock (flock-core), MIT OR Apache-2.0.
// Copyright (c) 2026 Bain Capital Crypto, LP and Ron Rothblum
// Modifications copyright 2026 Succinct Labs, Benedikt Bunz, William Wang
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! The opening's sumcheck over `E`: its round messages, and the running claim each level's queries join.
//!
//! The witness is in `K` until the first fold, and in `E` after it.
//!
//! The submodules:
//!
//! - `first_pass`: the first lane rounds' messages, from one pass over the witness and the initial weight.
//! - `kernels`: the fold and message kernels of every round.
//! - `weight`: the weight the rounds fold against.
//!
//! The constants below size the prover's work only: the round messages do not depend on them.

mod first_pass;
mod kernels;
mod weight;

pub(crate) use weight::{DenseWeight, InitialWeight};

use fiat_shamir::arith::{Arith, Native, RoundWeight, Verifier};
use fiat_shamir::{ProverState, TranscriptError};
use first_pass::InitialRounds;
use kernels::{
    fold_and_message, fold_block_pair, fold_blocks, fold_lanes_base, fold_witness_and_msg, round_message,
    round_message_and_sum,
};
use primitives::field::{F64, F192};
use primitives::multilinear::eq_table;
use std::sync::Arc;
use weight::Weight;

/// Lane rounds whose messages the first pass precomputes.
const PRECOMPUTED_ROUNDS: usize = 4;

/// Work items below which a loop runs on the calling thread, where dispatch costs more than the work.
const PAR_THRESHOLD: usize = 4096;

/// The same threshold for the first pass, counted in words over all its lanes.
const FIRST_PASS_PAR_THRESHOLD: usize = 8192;

/// Elements per task wherever a round is chunked: the adjacent-pair fold and the lane rounds.
///
/// A lane block is the whole witness divided by the lane count, so its tasks must split inside a block pair.
const ROUND_CHUNK: usize = 2048;

/// Words of the initial weight one fill call writes: one chunk, aligned to its size.
///
/// - A lane block smaller than this is filled whole.
/// - The ARM EOR3 byte-table maps use longer runs before switching maps.
/// - Other backends keep their compact scratch.
pub(crate) const INITIAL_BASIS_CHUNK: usize = if cfg!(all(target_arch = "aarch64", target_feature = "sha3")) {
    1024
} else {
    256
};

/// One round's message, both coefficients in `E`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct SumcheckMessage {
    /// `h(0)`, the constant coefficient.
    u_0: F192,
    /// The coefficient of `X^2`, also written `h(inf)`.
    u_2: F192,
}

impl SumcheckMessage {
    /// Send the constant and quadratic coefficients.
    ///
    /// The claim the message answers fixes the linear one, so it is not sent.
    pub(super) fn send(self, ps: &mut ProverState, claim: F192) {
        ps.send_round(&[self.u_0, claim + self.u_2, self.u_2], RoundWeight::Plain);
    }
}

/// A round's quadratic `c + b X + a X^2`, as the prover and the verifier both track it.
///
/// Its elements are field elements, or whatever a verifier holds them as.
#[derive(Clone, Copy, Debug)]
pub(crate) struct RoundQuad<E = F192> {
    /// The constant coefficient.
    c: E,
    /// The linear coefficient.
    b: E,
    /// The quadratic coefficient.
    a: E,
}

impl RoundQuad {
    /// The quadratic a message stands for, given the claim `t_r` it answers.
    ///
    /// `h(0) + h(1) = t_r` fixes the linear coefficient.
    #[inline]
    fn from_msg(msg: SumcheckMessage, t_r: F192) -> Self {
        Self {
            c: msg.u_0,
            b: t_r + msg.u_2,
            a: msg.u_2,
        }
    }
}

impl<E: Copy> RoundQuad<E> {
    /// Read the next round's quadratic, its linear coefficient fixed by the running claim.
    ///
    /// # Errors
    ///
    /// Returns an error past the end of the proof.
    pub(crate) fn read<V: Verifier<E = E>>(v: &mut V, claim: E) -> Result<Self, TranscriptError> {
        // Indexed rather than an array conversion, which the extraction does not translate: the round has three coefficients.
        let h = v.read_round(3, claim, None)?;
        Ok(Self {
            c: h[0],
            b: h[1],
            a: h[2],
        })
    }

    /// The quadratic at `x`, by Horner's rule.
    pub(crate) fn eval<A: Arith<E = E>>(self, ar: &mut A, x: E) -> E {
        let u = ar.mul_add(self.a, x, self.b);
        ar.mul_add(u, x, self.c)
    }

    /// `self + s * other`, coefficient by coefficient: two claims' quadratics batched by `s`.
    pub(crate) fn fold<A: Arith<E = E>>(self, ar: &mut A, other: Self, s: E) -> Self {
        Self {
            c: ar.mul_add(s, other.c, self.c),
            b: ar.mul_add(s, other.b, self.b),
            a: ar.mul_add(s, other.a, self.a),
        }
    }
}

/// What the round after a lane round pairs.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum NextRound {
    /// Blocks of lanes: another lane round follows.
    Lanes,
    /// The adjacent words of the single block the lane rounds leave.
    Words,
}

/// A claim added at the current round, until the next batching.
struct PendingClaim {
    /// Its weight, one value per word of the witness.
    weight: Vec<F192>,
    /// Its claimed sum.
    sum: F192,
    /// Its round's quadratic.
    quad: RoundQuad,
}

/// The two-phase witness: the committed `K` words until the first fold, an `E` vector after it.
enum Witness<'a> {
    /// The caller's committed words, read only until the first fold.
    Base(&'a [F64]),
    /// The folded witness, shared with the level commitment that keeps it.
    Ext(Arc<Vec<F192>>),
}

/// The running sumcheck over the committed base witness and its folds in `E`.
pub(super) struct SumcheckProver<'a> {
    /// The witness, in `K` until the first fold and in `E` after it.
    witness: Witness<'a>,
    /// The one combined weight: batching adds each new claim `tau` as `lambda^tau` times its weight.
    ///
    /// `tau` counts from 1, the running claim keeping `lambda^0 = 1`.
    weight: Weight<'a>,
    /// The running claim: `h(0) + h(1) = t_r` fixes the linear coefficient.
    t_r: F192,
    /// The current round's quadratic.
    quad: RoundQuad,
    /// The number of rounds folded so far.
    round: usize,
    /// The first pass's sums, which give the first lane rounds' messages.
    initial: InitialRounds,
    /// The lane challenges drawn while those rounds defer their fold.
    lane_rs: Vec<F192>,
    /// The level's new claims, until the next batching.
    ///
    /// They come in Protocol 1 step 1 order: the out-of-domain claims, then the query batch.
    pending: Vec<PendingClaim>,
}

impl<'a> SumcheckProver<'a> {
    /// The sumcheck of `sum_x f(x) * w(x) = h1`, and its first message.
    ///
    /// `block` is the lane block length `2^(log_n - initial_k)`.
    /// The first `initial_k` rounds are the lane fold, so round 0's message already pairs whole blocks.
    pub(super) fn new(
        f: &'a [F64],
        w: &'a dyn InitialWeight,
        h1: F192,
        block: usize,
        initial_k: usize,
    ) -> (Self, SumcheckMessage) {
        let initial = tracing::info_span!("First pass").in_scope(|| InitialRounds::new(f, block, initial_k, w));
        assert!(initial.rounds <= initial_k);
        let msg = initial.message(0, &[]);
        let inst = Self {
            witness: Witness::Base(f),
            weight: Weight::Initial(w),
            t_r: h1,
            quad: RoundQuad::from_msg(msg, h1),
            round: 0,
            lane_rs: Vec::with_capacity(initial.rounds),
            initial,
            pending: Vec::new(),
        };
        (inst, msg)
    }

    /// The claim that fixes the next message's linear coefficient.
    #[inline]
    pub(super) const fn claim(&self) -> F192 {
        self.t_r
    }

    /// The base-two logarithm of the witness's length, rounded down, for the round spans.
    ///
    /// A lane round's length is `n_lanes * block`, generally not a power of two.
    fn log_size(&self) -> u32 {
        match &self.witness {
            Witness::Base(f) => f.len().ilog2(),
            Witness::Ext(f) => f.len().ilog2(),
        }
    }

    /// One lane round at challenge `r`: folds block `2i` with block `2i + 1` and returns the next round's message.
    ///
    /// - With an odd block count, the last block folds with the absent zero padding.
    /// - `next` says whether the next round pairs blocks or the adjacent words of the one block left.
    /// - During the first pass's rounds the fold waits, and each message is interpolated from the pass's sums.
    /// - The last of those rounds folds all their lane bits at once.
    pub(super) fn fold_lane(&mut self, r: F192, block: usize, next: NextRound) -> SumcheckMessage {
        self.t_r = self.quad.eval(&mut Native, r);
        self.round += 1;
        let _span = tracing::info_span!("Sumcheck round", round = self.round, log_size = self.log_size()).entered();
        let (nf, nb, msg) = match (&self.witness, &self.weight) {
            (Witness::Base(f), Weight::Initial(w)) => {
                self.lane_rs.push(r);
                if self.round < self.initial.rounds {
                    let msg = self.initial.message(self.round, &self.lane_rs);
                    self.quad = RoundQuad::from_msg(msg, self.t_r);
                    return msg;
                }
                // The weight folds in closed form, the witness by its lanes' eq weights.
                let nb = tracing::info_span!("Fold weight").in_scope(|| w.fold_lanes(&self.lane_rs));
                let (nf, msg) = fold_lanes_base(f, block, &self.lane_rs, &nb, next);
                (nf, nb, msg)
            }
            (Witness::Ext(f), Weight::Dense(b)) => {
                let n_out = (f.len() / block).div_ceil(2);
                let nb = fold_blocks(b, block, r);
                let (nf, msg) = fold_witness_and_msg(n_out, block, &nb, next, |out_blk, x0, stage| {
                    fold_block_pair(f, block, r, out_blk, x0, stage);
                });
                (nf, nb, msg)
            }
            _ => unreachable!("the first fold lifts the witness and folds the initial weight together"),
        };
        self.witness = Witness::Ext(Arc::new(nf));
        self.weight = Weight::Dense(nb);
        self.quad = RoundQuad::from_msg(msg, self.t_r);
        msg
    }

    /// One adjacent-pair round at challenge `r`: folds the witness and the weight, and returns the next message.
    ///
    /// # Panics
    ///
    /// Panics before the first fold.
    pub(super) fn fold(&mut self, r: F192) -> SumcheckMessage {
        self.t_r = self.quad.eval(&mut Native, r);
        self.round += 1;
        let _span = tracing::info_span!("Sumcheck round", round = self.round, log_size = self.log_size()).entered();
        let folded = fold_and_message(self.f_ext(), self.weight.dense(), r);
        // Swap the folded buffers in and drop the consumed ones.
        // Why: the allocator then serves the next round's fold from their memory.
        drop(std::mem::replace(
            &mut self.witness,
            Witness::Ext(Arc::new(folded.witness)),
        ));
        drop(std::mem::replace(&mut self.weight, Weight::Dense(folded.weight)));
        self.quad = RoundQuad::from_msg(folded.message, self.t_r);
        folded.message
    }

    /// Adds a claim with weight `weight` and claimed sum `sum`, and returns its message at the current round.
    ///
    /// The message is that of `sum_x f(x) * weight(x)`; the claim joins the running one at the next batching.
    ///
    /// # Panics
    ///
    /// Before the first fold, or if `weight` is not as long as the witness.
    pub(super) fn introduce(&mut self, weight: Vec<F192>, sum: F192) -> SumcheckMessage {
        let f = self.f_ext();
        assert_eq!(weight.len(), f.len());
        let msg = round_message(f, &weight);
        self.pending.push(PendingClaim {
            weight,
            sum,
            quad: RoundQuad::from_msg(msg, sum),
        });
        msg
    }

    /// Adds a claim with weight `weight`, computing its claimed sum in the same pass as its message.
    ///
    /// Out-of-domain claims come only after the first fold, when the witness is already in `E`.
    ///
    /// # Returns
    ///
    /// The claim's message at the current round, and its claimed sum.
    ///
    /// # Panics
    ///
    /// Before the first fold, or if `weight` is not as long as the witness.
    pub(super) fn introduce_evaluated(&mut self, weight: Vec<F192>) -> (SumcheckMessage, F192) {
        let f = self.f_ext();
        assert_eq!(weight.len(), f.len());
        let (msg, sum) = round_message_and_sum(f, &weight);
        self.pending.push(PendingClaim {
            weight,
            sum,
            quad: RoundQuad::from_msg(msg, sum),
        });
        (msg, sum)
    }

    /// Send `count` OOD claims on the folded witness, right after its root enters the transcript.
    ///
    /// For each claim, in transcript order:
    ///
    /// 1. sample the point `z` of `n_vars` coordinates,
    /// 2. send the value `y` of the folded witness at `z`,
    /// 3. send the claim's intro message.
    ///
    /// The claims stay pending until the level's batching challenge is drawn, after its query positions.
    /// The verifier replays the same steps in the same order.
    pub(super) fn send_ood(&mut self, ps: &mut ProverState, n_vars: usize, count: usize) {
        for _ in 0..count {
            let z = ps.verifier_messages(n_vars);
            let (intro, y) = self.introduce_evaluated(eq_table(&z));
            ps.prover_message(&y);
            intro.send(ps, y);
        }
    }

    /// Join a level's query claim, then batch the level's pending claims by powers of `lambda`.
    ///
    /// The claim's weight is the one the queries induce on the folded witness, and its value their claimed sum.
    pub(super) fn join(&mut self, ps: &mut ProverState, lambda: F192, claimed_sum: F192, induced_weight: Vec<F192>) {
        let intro = self.introduce(induced_weight, claimed_sum);
        intro.send(ps, claimed_sum);
        self.batch_pending(lambda);
    }

    /// Batches every claim added since the last batching into the running one, by powers of `lambda`.
    ///
    /// Claim `tau`, counting from 1, adds `lambda^tau` times its weight to the weight, and its sum to the claim.
    /// The running claim keeps `lambda^0 = 1` (PCS annex, Protocol 1 step 1).
    ///
    /// # Panics
    ///
    /// If no claim was added.
    pub(super) fn batch_pending(&mut self, lambda: F192) {
        let pending = std::mem::take(&mut self.pending);
        assert!(!pending.is_empty(), "a batching takes at least one claim");
        let mut scalar = F192::ONE;
        for claim in pending {
            scalar *= lambda;
            let combined = self.weight.dense_mut();
            assert_eq!(claim.weight.len(), combined.len());
            if combined.len() < PAR_THRESHOLD {
                for (acc, &v) in combined.iter_mut().zip(claim.weight.iter()) {
                    *acc += scalar * v;
                }
            } else {
                let chunk = parallel::recommended_chunk_size(combined.len());
                parallel::chunks_mut_zip(combined, &claim.weight, chunk, |_, accs, news| {
                    for (acc, &v) in accs.iter_mut().zip(news) {
                        *acc += scalar * v;
                    }
                });
            }
            self.t_r += scalar * claim.sum;
            self.quad = self.quad.fold(&mut Native, claim.quad, scalar);
        }
    }

    /// The folded witness, always in `E`.
    ///
    /// # Panics
    ///
    /// Before the first fold; the base phase never reaches a commitment.
    pub(super) fn f_ext(&self) -> &[F192] {
        self.shared_ext()
    }

    /// The folded witness, shared: a later fold replaces it here but leaves it to its other holders.
    ///
    /// # Panics
    ///
    /// Before the first fold.
    pub(super) fn shared_ext(&self) -> &Arc<Vec<F192>> {
        match &self.witness {
            Witness::Ext(f) => f,
            Witness::Base(_) => panic!("witness still in base phase (no fold yet)"),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::whir::config::INITIAL_FOLDING_FACTOR;
    use primitives::multilinear::inner_product;
    use primitives::test_util::Rng;

    /// What follows lane round `j` of `initial_k`: the last one hands over to adjacent words.
    fn next_round(j: usize, initial_k: usize) -> NextRound {
        if j + 1 == initial_k {
            NextRound::Words
        } else {
            NextRound::Lanes
        }
    }

    /// One lane bit folded the naive way: block `2i` with block `2i + 1`, the last with zeros.
    fn fold_lane_bit(v: &[F192], block: usize, r: F192) -> Vec<F192> {
        let lanes = v.len() / block;
        let mut out = vec![F192::ZERO; lanes.div_ceil(2) * block];
        for (word, o) in out.iter_mut().enumerate() {
            let (pair, x) = (word / block, word % block);
            let lo = v[2 * pair * block + x];
            let hi = if 2 * pair + 1 < lanes {
                v[(2 * pair + 1) * block + x]
            } else {
                F192::ZERO
            };
            *o = lo + r * (lo + hi);
        }
        out
    }

    /// A lane round's message the naive way: `h(0)` and `h(inf)` summed over block pairs, the last against zeros.
    fn lane_message(f: &[F192], b: &[F192], block: usize) -> SumcheckMessage {
        let lanes = f.len() / block;
        let (mut u_0, mut u_2) = (F192::ZERO, F192::ZERO);
        for pair in 0..lanes.div_ceil(2) {
            for x in 0..block {
                let lo = 2 * pair * block + x;
                let (f1, b1) = if 2 * pair + 1 < lanes {
                    (f[lo + block], b[lo + block])
                } else {
                    (F192::ZERO, F192::ZERO)
                };
                u_0 += f[lo] * b[lo];
                u_2 += (f[lo] + f1) * (b[lo] + b1);
            }
        }
        SumcheckMessage { u_0, u_2 }
    }

    /// An adjacent-pair round's message the naive way.
    fn pair_message(f: &[F192], b: &[F192]) -> SumcheckMessage {
        let (mut u_0, mut u_2) = (F192::ZERO, F192::ZERO);
        for (&[f0, f1], &[b0, b1]) in f.as_chunks::<2>().0.iter().zip(b.as_chunks::<2>().0) {
            u_0 += f0 * b0;
            u_2 += (f0 + f1) * (b0 + b1);
        }
        SumcheckMessage { u_0, u_2 }
    }

    #[test]
    fn the_lane_rounds_are_one_bit_folds() {
        // Invariant: the first pass's interpolated messages and many-bit fold match folding one lane bit a round.
        // Invariant: so do the later lane rounds' single-bit folds.
        let mut rng = Rng::new(0xBA515);
        for initial_k in [1, 2, 3, PRECOMPUTED_ROUNDS, INITIAL_FOLDING_FACTOR] {
            let full = 1usize << initial_k;
            // Fixture state: blocks below and above one fill chunk and one task chunk.
            for block in [1, 16, INITIAL_BASIS_CHUNK, 2 * ROUND_CHUNK] {
                // Partial groups and odd counts meet the absent zero lanes.
                for lanes in [1, 2, 3, 5, full - 1, full, 37]
                    .into_iter()
                    .filter(|&l| l >= 1 && l <= full)
                {
                    let f: Vec<F64> = (0..block * lanes).map(|_| F64(rng.next_u64())).collect();
                    let table = DenseWeight {
                        weight: rng.ext_vec(f.len()),
                        block,
                    };
                    let rs = rng.ext_vec(initial_k);
                    let label = format!("initial_k={initial_k}, block={block}, lanes={lanes}");

                    // The reference: lift, then one naive lane fold a round, the last handing over to adjacent pairs.
                    let mut nf: Vec<F192> = f.iter().map(|&w| F192::from(w)).collect();
                    let mut nb = table.weight.clone();
                    let mut expected = vec![lane_message(&nf, &nb, block)];
                    for (j, &r) in rs.iter().enumerate() {
                        nf = fold_lane_bit(&nf, block, r);
                        nb = fold_lane_bit(&nb, block, r);
                        expected.push(if j + 1 == initial_k {
                            pair_message(&nf, &nb)
                        } else {
                            lane_message(&nf, &nb, block)
                        });
                    }

                    let (mut sc, msg) = SumcheckProver::new(&f, &table, F192::ZERO, block, initial_k);
                    let mut actual = vec![msg];
                    for (j, &r) in rs.iter().enumerate() {
                        actual.push(sc.fold_lane(r, block, next_round(j, initial_k)));
                    }
                    assert_eq!(actual, expected, "messages, {label}");
                    assert_eq!(sc.f_ext(), &*nf, "witness, {label}");
                    assert_eq!(&**sc.weight.dense(), &*nb, "weight, {label}");
                }
            }
        }
    }

    #[test]
    fn the_folds_bind_the_rotated_point() {
        // Invariant: at the end, the witness and the weight are their MLEs at the challenges rotated by `initial_k`.
        // Why: that rotated point is the one the verifier evaluates its weight at.
        let mut rng = Rng::new(0x707A7E);
        let dense_mle = |table: &[F192], point: &[F192]| inner_product(table, &eq_table(point));
        // Fixture state: `log_n = 15` makes the lane block longer than one fold task.
        // Fixture state: lane counts below `2^initial_k` leave absent lanes, zero in the dense tables.
        for (log_n, initial_k, lanes) in [(9usize, 3usize, &[1usize, 5, 8][..]), (15, 3, &[3, 8][..])] {
            let block = 1usize << (log_n - initial_k);
            for &n_lanes in lanes {
                let used = n_lanes * block;
                let mut f = vec![F64::ZERO; 1 << log_n];
                f[..used].iter_mut().for_each(|w| *w = F64(rng.next_u64()));
                let mut b = vec![F192::ZERO; 1 << log_n];
                b[..used].copy_from_slice(&rng.ext_vec(used));

                let table = DenseWeight {
                    weight: b[..used].to_vec(),
                    block,
                };
                let (mut sc, _) = SumcheckProver::new(&f[..used], &table, F192::ZERO, block, initial_k);
                let rounds = rng.ext_vec(log_n);
                for (j, &r) in rounds[..initial_k].iter().enumerate() {
                    sc.fold_lane(r, block, next_round(j, initial_k));
                }
                for &r in &rounds[initial_k..] {
                    sc.fold(r);
                }

                let mut point = rounds;
                point.rotate_left(initial_k);
                let lifted: Vec<F192> = f.iter().map(|&w| F192::from(w)).collect();
                assert_eq!(
                    sc.f_ext(),
                    [dense_mle(&lifted, &point)],
                    "witness, log_n={log_n}, lanes={n_lanes}"
                );
                assert_eq!(
                    sc.weight.dense()[..],
                    [dense_mle(&b, &point)],
                    "weight, log_n={log_n}, lanes={n_lanes}"
                );
            }
        }
    }
}
