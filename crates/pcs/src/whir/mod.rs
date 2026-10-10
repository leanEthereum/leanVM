// CREDIT: https://github.com/succinctlabs/flock (flock-core), MIT OR Apache-2.0.
// Copyright (c) 2026 Bain Capital Crypto, LP and Ron Rothblum
// Modifications copyright 2026 Succinct Labs, Benedikt Bunz, William Wang
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! WHIR over `K = GF(2)[x]/(x^64 + x^4 + x^3 + x + 1)`, opened over `E = K[y]/(y^3 + y + 1)`.
//!
//! # Overview
//!
//! - The committed message is words of `K`.
//! - Every challenge, sumcheck message, folded witness and deeper codeword is in `E`.
//! - The evaluation domain and every twiddle stay in `K`, so a deeper level's encode takes mixed products only.
//!
//! The parameters come from an analysis over the challenge field's size, `2^192`.
//!
//! # Modules
//!
//! ```text
//!     commit    the L0 base encode and the deeper levels' encodes, Merkle-committed
//!     sumcheck  the round messages, the fold kernels, the running claim
//!     prove     the prover, level by level
//!     verify    the succinct verifier
//! ```

mod commit;
pub mod config;
mod prove;
mod query;
mod sumcheck;
mod verify;

use crate::verifier::OpeningVerifier;
use fiat_shamir::transcript::{Challenger, Transmitter};
use primitives::field::{F64, F192};
use primitives::multilinear::inner_product_base;

pub use config::{
    Config, INITIAL_FOLDING_FACTOR, L0_LIST_BITS, LOG_INV_RATE_0, MAX_LOG_INV_RATE, MAX_LOG_N, MIN_LOG_INV_RATE,
    MIN_LOG_N, MIN_LOG_N_HIDING, QUERY_GRINDING_BITS, RESIDUAL_MAX_LOG, RS_DOMAIN_INITIAL_REDUCTION_FACTOR,
    SECURITY_BITS, SUBSEQUENT_FOLDING_FACTOR, config_for_rate, config_for_rate_hiding,
};

#[cfg(test)]
pub(crate) use commit::commit;
pub use commit::{ProverData, commit_hiding};
pub(crate) use prove::prove;
pub(crate) use sumcheck::{DenseWeight, INITIAL_BASIS_CHUNK, InitialWeight};
pub use verify::WhirError;
pub(crate) use verify::verify;

/// The opening of a commitment made by [`commit_hiding`].
///
/// After the lane fold's last challenge the prover sends the padding's fold `g_1`, the configuration's [`Config::padding`] scalars, and level 0's queries take it off the folded codeword (the module docs of [`crate::stack`]).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Hiding {
    /// The scalars before the lane fold's end travelled under one-time keys: first turn hiding off and send the running claim in the clear, which the verifier checks against the one it holds and continues from.
    pub hidden_claim: bool,
}

/// Prove `sum_x witness(x) * w(x) = target` against a hiding commitment `l0`, for a weight `w` held whole.
///
/// It exists for a zero-knowledge proof's key commitment: its weight, the outer proof's linear claims on the keys, is neither a point claim nor a ring-switched one, so no [`crate::stack::Statement`] states it.
/// The arguments are those of the stacked opening's WHIR run, `weight` covering the committed lanes.
///
/// # Panics
///
/// Panics on a weight of another length than the witness, or as the opening does.
#[expect(
    clippy::too_many_arguments,
    reason = "The proof kernel keeps its independent inputs explicit."
)]
pub fn open_hiding(
    config: &Config,
    log_n: usize,
    witness: &[F64],
    weight: Vec<F192>,
    target: F192,
    l0: &ProverData,
    hiding: Hiding,
    ps: &mut impl Transmitter,
) {
    assert_eq!(weight.len(), witness.len(), "a weight per committed word");
    let weight = DenseWeight {
        weight,
        block: 1 << (log_n - config.initial_k()),
    };
    prove(config, log_n, witness, &weight, target, l0, Some(hiding), ps);
}

/// Verify an opening made by [`open_hiding`], the weight's multilinear extension evaluated once by `weight_at`, at the terminal point.
///
/// # Errors
///
/// As the WHIR verifier.
#[expect(
    clippy::too_many_arguments,
    reason = "The verifier keeps its independent inputs explicit, as the prover does."
)]
pub fn verify_hiding<V: OpeningVerifier>(
    v: &mut V,
    config: &Config,
    log_n: usize,
    n_lanes: usize,
    target: V::E,
    root: V::Root,
    hiding: Hiding,
    weight_at: impl FnOnce(&mut V, &[V::E]) -> V::E,
) -> Result<(), WhirError> {
    verify(v, config, log_n, n_lanes, target, root, Some(hiding), weight_at)
}

/// The inner product `sum_i b[i] · witness[i]` of a weight in `E` and a witness in `K`.
pub fn inner_product_base_ext(witness: &[F64], b: &[F192]) -> F192 {
    assert_eq!(witness.len(), b.len());
    const PAR_THRESHOLD: usize = 4096;
    if witness.len() < PAR_THRESHOLD {
        return inner_product_base(witness, b);
    }
    parallel::map_reduce(
        witness.len(),
        || F192::ZERO,
        |i| b[i].mul_base(witness[i]),
        |a, v| a + v,
    )
}

/// Where a query of a batch lands: the top `bits` bits of its position are `index`, the rest uniform.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Stratum {
    /// How many of the position's top bits are fixed.
    pub bits: usize,
    /// Their value.
    pub index: usize,
}

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
pub fn strata(count: usize, depth: usize) -> Vec<Stratum> {
    let mut out = Vec::with_capacity(count);
    for g in (0..usize::BITS as usize).rev().filter(|&g| count >> g & 1 == 1) {
        let bits = g.min(depth);
        out.extend((0..1usize << g).map(|j| Stratum {
            bits,
            index: j & ((1 << bits) - 1),
        }));
    }
    out
}

/// Sample `count` query positions of a domain of `block_len = 2^d`, in transcript order.
///
/// - Each squeezed element of `E` yields `floor(192 / d)` positions: its disjoint `d`-bit chunks, low bits first.
/// - Each position then takes its stratum: its top bits are replaced by the stratum's.
///
/// Positions are neither sorted nor deduplicated.
///
/// A repeated position opens the same authenticated row again, which is harmless.
pub(crate) fn sample_queries_ordered(ch: &mut impl Challenger, block_len: usize, count: usize) -> Vec<usize> {
    let d = block_len.trailing_zeros() as usize;
    let per = 192 / d;
    let mut out = Vec::with_capacity(count);
    while out.len() < count {
        let v = ch.sample();
        for j in 0..per.min(count - out.len()) {
            let off = j * d;
            let limbs = [v.c0, v.c1, v.c2];
            let (li, sh) = (off / 64, off % 64);
            let mut chunk = limbs[li] >> sh;
            if sh + d > 64 {
                chunk |= limbs[li + 1] << (64 - sh);
            }
            out.push(chunk as usize & (block_len - 1));
        }
    }
    for (x, s) in out.iter_mut().zip(strata(count, d)) {
        let low = d - s.bits;
        *x = (*x & ((1 << low) - 1)) | s.index << low;
    }
    out
}

#[cfg(test)]
mod tests {
    use super::sumcheck::tests::Table;
    use super::*;
    use crate::merkle::Hash;
    use crate::whir::config::tests::test_config_for;
    use crate::whir::query::QueryBatch;
    use fiat_shamir::transcript::{ProofTranscript, ProverState, TranscriptError, VerifierState};
    use primitives::multilinear::{eq_eval, eq_table, inner_product};
    use primitives::test_util::Rng;
    use std::panic::AssertUnwindSafe;

    struct Instance {
        vc: Config,
        log_n: usize,
        /// The eq-point behind `b_initial` (for the succinct closure).
        point: Vec<F192>,
        b_initial: Vec<F192>,
        target: F192,
        root: Hash,
        /// The transcript: every scalar WHIR transmitted, plus its opening phases.
        fs: ProofTranscript,
    }

    fn prove_instance(log_n: usize, seed: u64) -> Instance {
        let pc = test_config_for(log_n);
        let mut rng = Rng::new(seed);
        let witness: Vec<F64> = (0..1usize << log_n).map(|_| F64(rng.next_u64())).collect();
        let pd = commit(&witness, log_n, pc.initial_k(), pc.log_inv_rates()[0]);
        let point: Vec<F192> = (0..log_n).map(|_| rng.ext()).collect();
        let b_initial = eq_table(&point);
        let target = inner_product_base_ext(&witness, &b_initial);
        let mut ps = ProverState::from_label(b"whir-test");
        let weight = Table {
            weight: b_initial.to_vec(),
            block: 1 << (log_n - pc.initial_k()),
        };
        prove(&pc, log_n, &witness, &weight, target, &pd, None, &mut ps);
        Instance {
            vc: pc,
            log_n,
            point,
            b_initial,
            target,
            root: pd.root(),
            fs: ps.into_proof(),
        }
    }

    /// The multilinear extension of `table` at `point`, from the whole table.
    fn dense_mle(table: &[F192], point: &[F192]) -> F192 {
        inner_product(table, &eq_table(point))
    }

    fn verify_with(
        inst: &Instance,
        fs: &ProofTranscript,
        eval_b_at: impl Fn(&[F192]) -> F192,
    ) -> Result<(), WhirError> {
        let mut vs = VerifierState::from_label(b"whir-test", fs);
        verify(
            &mut vs,
            &inst.vc,
            inst.log_n,
            1 << inst.vc.initial_k(),
            inst.target,
            inst.root,
            None,
            |_, point| eval_b_at(point),
        )
    }

    /// The weight evaluated in closed form at the terminal fold point.
    fn verify_closed_form(inst: &Instance, fs: &ProofTranscript) -> bool {
        verify_with(inst, fs, |fold_point| eq_eval(&inst.point, fold_point)).is_ok()
    }

    /// The weight evaluated from its whole table at the terminal fold point.
    fn verify_dense_weight(inst: &Instance, fs: &ProofTranscript) -> bool {
        verify_with(inst, fs, |fold_point| dense_mle(&inst.b_initial, fold_point)).is_ok()
    }

    /// Both weight evaluations on the same proof, asserting they agree.
    ///
    /// Returns the shared verdict.
    fn verify_both_agree(inst: &Instance, fs: &ProofTranscript, what: &str) -> bool {
        let closed_form = verify_closed_form(inst, fs);
        let dense = verify_dense_weight(inst, fs);
        assert_eq!(closed_form, dense, "closed-form/dense verdict split on {what}");
        closed_form
    }

    #[test]
    fn configs_johnson_profile_shape() {
        // Invariant: the production profile is the Johnson/OOD one: no OOD sample at L0, at least one after, full grinding.
        //
        // Below its floor the tests use the small fallback config instead.
        let pc = config_for_rate(16, LOG_INV_RATE_0).expect("Johnson profile feasible at log_n = 16");
        assert_eq!(pc.initial_k(), 6);
        assert!(pc.level_steps() >= 1);
        assert_eq!(pc.ood_samples()[0], 0);
        assert!(pc.ood_samples().iter().skip(1).all(|&s| s >= 1));
        assert!(pc.grinding_bits().iter().all(|&b| b == QUERY_GRINDING_BITS));
        // And log_n = 12 is below the production ladder's feasibility floor, so
        // the tests there use the default_config fallback.
        assert!(config_for_rate(12, LOG_INV_RATE_0).is_err());
    }

    #[test]
    fn roundtrip_log_n_18_sparse_induce() {
        // Invariant: at log_n = 18 the L0 induce takes the sparse transposed NTT, and the proof still verifies.
        //
        // Fixture state: L0 has 2^12 message columns, enough queries to trip the dispatch; at log_n = 16 it stays dense.
        let takes_transposed = |log_n: usize| {
            let pc = config_for_rate(log_n, LOG_INV_RATE_0).unwrap();
            let positions = vec![0; pc.queries()[0]];
            let weights = vec![F192::ZERO; positions.len()];
            QueryBatch::new(&positions, &weights).takes_transposed(log_n - pc.initial_k(), pc.log_inv_rates()[0])
        };
        assert!(
            takes_transposed(18),
            "shape must select the sparse transposed-NTT induce at L0"
        );
        // And the smaller roundtrips stay on the dense path (cols < 12).
        assert!(!takes_transposed(16));
        let inst = prove_instance(18, 8);
        assert!(verify_dense_weight(&inst, &inst.fs), "honest proof rejected");
        assert!(
            verify_closed_form(&inst, &inst.fs),
            "closed-form weight rejected an honest proof at log_n=18"
        );
    }

    #[test]
    fn tampered_proofs_are_rejected() {
        // Invariant: an honest proof verifies, and a single flipped bit anywhere is refused.
        //
        // Both weight evaluations agree on every verdict: in closed form, and from the whole table.
        //
        // Fixture state: a fallback shape (log_n = 12) and the production shape (log_n = 16).
        for (log_n, seed) in [(12usize, 11u64), (16, 12)] {
            let inst = prove_instance(log_n, seed);
            assert!(verify_both_agree(&inst, &inst.fs, "honest proof"));

            let mut rng = Rng::new(seed ^ 0xABCD);
            // One Merkle phase per level, in level order: phase 0 opens L0, the
            // last phase opens the final level.
            type Tamper = fn(&mut ProofTranscript, u64);
            let tampers: &[(&str, Tamper)] = &[
                ("L0 opened row", |p, r| {
                    let rows = &mut p.merkle[0].leaf_data;
                    let row = (r as usize) % rows.len();
                    rows[row][0].0 ^= 1;
                }),
                ("final-level opened row", |p, r| {
                    let rows = &mut p.merkle.last_mut().unwrap().leaf_data;
                    let row = (r as usize) % rows.len();
                    rows[row][0].0 ^= 1;
                }),
                ("merkle proof node", |p, r| {
                    let sibs = &mut p.merkle[0].sibling_hashes;
                    let idx = (r as usize) % sibs.len();
                    sibs[idx][0] ^= 1;
                }),
            ];
            for (what, tamper) in tampers {
                let mut bad_fs = inst.fs.clone();
                tamper(&mut bad_fs, rng.next_u64());
                assert!(
                    !verify_both_agree(&inst, &bad_fs, what),
                    "tampered {what} accepted at log_n={log_n}"
                );
            }
            // Every transmitted scalar (sumcheck messages, level roots, OOD
            // claims, `yr`, both kinds of grinding nonce) is one stream word, so
            // one sweep covers what used to be five per-field tampers: a bound
            // word re-rolls the challenges after it, a nonce word fails its PoW.
            let n_stream = inst.fs.stream.len();
            assert!(n_stream > 0, "WHIR transmitted nothing");
            for idx in (0..n_stream).step_by(1 + n_stream / 24) {
                let mut bad_fs = inst.fs.clone();
                bad_fs.stream[idx] += F192::ONE;
                assert!(
                    !verify_both_agree(&inst, &bad_fs, "stream word"),
                    "tampered stream word {idx} accepted at log_n={log_n}"
                );
            }
        }
    }

    #[test]
    fn tampered_stream_words_reject_without_panicking() {
        // Invariant: every stream word is the prover's, so a tampered one is refused, never a panic.
        //
        // That covers a level root's limbs and every digest half: a non-canonical half is refused before any decoding.
        let inst = prove_instance(12, 11);
        let mut short = inst.fs.clone();
        short.stream.truncate(1);
        assert_eq!(
            verify_with(&inst, &short, |point| eq_eval(&inst.point, point)),
            Err(WhirError::Transcript(TranscriptError::ExceededStream { len: 1 })),
        );
        for idx in 0..inst.fs.stream.len() {
            for tamper in [F192::ONE, F192::new(0, 0, 1)] {
                let mut bad = inst.fs.clone();
                bad.stream[idx] += tamper;
                let verdict = std::panic::catch_unwind(AssertUnwindSafe(|| verify_closed_form(&inst, &bad)));
                match verdict {
                    Ok(accepted) => assert!(!accepted, "tampered stream word {idx} accepted"),
                    Err(_) => panic!("verifier panicked on tampered stream word {idx}"),
                }
            }
        }
    }

    #[test]
    fn truncated_lanes_match_an_explicit_zero_tail() {
        // Invariant: committing only the lanes that carry data is committing the whole stack with a zero tail.
        //
        // Same root, the same transcript, and the verifier accepts against the weight over the whole cube.
        // `log_n = 18` puts the lane block over the fold's task chunk, so the fold runs
        // several x-chunks per block; at 13 it is one chunk per block. Both matter: the
        // chunked path is what production takes, and it is where a message pair could
        // straddle a task.
        for (log_n, lanes) in [(13usize, &[1usize, 5, 64][..]), (18, &[5, 64][..])] {
            let pc = test_config_for(log_n);
            let lane_block = 1usize << (log_n - pc.initial_k());
            for &n_lanes in lanes {
                let mut rng = Rng::new(0x5AFE + n_lanes as u64);
                let used = n_lanes * lane_block;
                let mut witness: Vec<F64> = (0..1usize << log_n).map(|_| F64(rng.next_u64())).collect();
                let mut b_initial: Vec<F192> = (0..1usize << log_n).map(|_| rng.ext()).collect();
                witness[used..].fill(F64::ZERO);
                b_initial[used..].fill(F192::ZERO);
                let target = inner_product_base_ext(&witness, &b_initial);

                let prove_with = |msg: &[F64], b: &[F192]| {
                    let pd = commit(msg, log_n, pc.initial_k(), pc.log_inv_rates()[0]);
                    let mut ps = ProverState::from_label(b"whir-test");
                    let weight = Table {
                        weight: b.to_vec(),
                        block: lane_block,
                    };
                    prove(&pc, log_n, msg, &weight, target, &pd, None, &mut ps);
                    (pd.root(), ps.into_proof())
                };
                let (root_trunc, fs_trunc) = prove_with(&witness[..used], &b_initial[..used]);
                let (root_full, fs_full) = prove_with(&witness, &b_initial);
                assert_eq!(root_trunc, root_full, "root differs at n_lanes = {n_lanes}");
                assert_eq!(
                    fs_trunc.stream, fs_full.stream,
                    "the protocol itself must not change at n_lanes = {n_lanes}"
                );

                // What the two proofs DO differ in, and the point of the exercise: the
                // truncated one stores each L0 row as the committed lanes alone, which is
                // exactly the full image with its leading padding zeros dropped.
                let leaf_words = 1usize << pc.initial_k();
                for (thin, full) in fs_trunc.merkle[0].leaf_data.iter().zip(&fs_full.merkle[0].leaf_data) {
                    assert_eq!(thin.len(), n_lanes);
                    assert_eq!(full.len(), leaf_words);
                    assert_eq!(thin[..], full[leaf_words - n_lanes..], "stored row is the image tail");
                    assert!(
                        full[..leaf_words - n_lanes].iter().all(|w| *w == F64::ZERO),
                        "the words the proof drops are the padding at n_lanes = {n_lanes}"
                    );
                }

                // The verifier evaluates the weight over the whole `2^log_n` cube.
                let verify = |fs: &ProofTranscript| {
                    let mut vs = VerifierState::from_label(b"whir-test", fs);
                    verify(&mut vs, &pc, log_n, n_lanes, target, root_trunc, None, |_, point| {
                        dense_mle(&b_initial, point)
                    })
                };
                assert_eq!(verify(&fs_trunc), Ok(()), "verify failed at n_lanes = {n_lanes}");

                // The image the octopus was built over is pinned by the announced widths,
                // so a row of any other width is rejected rather than zero-extended to
                // something that happens to hash.
                if n_lanes < leaf_words {
                    let mut bad_fs = fs_trunc.clone();
                    bad_fs.merkle[0].leaf_data[0].push(F64::ZERO);
                    assert!(
                        verify(&bad_fs).is_err(),
                        "a wrong-width row was accepted at n_lanes = {n_lanes}"
                    );
                }
            }
        }
    }

    #[test]
    fn each_group_of_strata_covers_its_cosets_equally() {
        // Invariant: each group covers every coset of its fixed bits equally often, which the stratified queries' soundness rests on.
        for depth in [1usize, 3, 7, 22] {
            for count in 1..=300usize {
                let strata = strata(count, depth);
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

    #[test]
    fn every_rate_roundtrips_at_the_lane_edges() {
        // Invariant: the production profile proves and verifies at every rate, with one lane, a partial group, and every lane.
        //
        // Mutation: a target off by one is refused.
        let log_n = MIN_LOG_N;
        for log_inv_rate in MIN_LOG_INV_RATE..=MAX_LOG_INV_RATE {
            let pc = config_for_rate(log_n, log_inv_rate).expect("a supported rate");
            let lane_block = 1usize << (log_n - pc.initial_k());
            for n_lanes in [1, (1 << pc.initial_k()) / 2 + 1, 1 << pc.initial_k()] {
                let mut rng = Rng::new((log_inv_rate * 1000 + n_lanes) as u64);
                let used = n_lanes * lane_block;
                let witness: Vec<F64> = (0..used).map(|_| F64(rng.next_u64())).collect();
                let mut weight = vec![F192::ZERO; 1 << log_n];
                weight[..used].copy_from_slice(&rng.ext_vec(used));
                let target = inner_product_base_ext(&witness, &weight[..used]);

                let pd = commit(&witness, log_n, pc.initial_k(), log_inv_rate);
                let mut ps = ProverState::from_label(b"whir-test");
                let table = Table {
                    weight: weight[..used].to_vec(),
                    block: lane_block,
                };
                prove(&pc, log_n, &witness, &table, target, &pd, None, &mut ps);
                let fs = ps.into_proof();

                let check = |target: F192| {
                    let mut vs = VerifierState::from_label(b"whir-test", &fs);
                    verify(&mut vs, &pc, log_n, n_lanes, target, pd.root(), None, |_, point| {
                        dense_mle(&weight, point)
                    })
                };
                let label = format!("rate={log_inv_rate}, n_lanes={n_lanes}");
                assert_eq!(check(target), Ok(()), "{label}");
                assert!(check(target + F192::ONE).is_err(), "{label}");
            }
        }
    }

    /// The novel basis at the point of codeword position `p` (the field element `F64(p)`): `X_j(p)` for `j < 2^m`, then `W_m(p)`.
    ///
    /// `X_j` is the product of the normalized subspace polynomials `W_b = s_b / s_b(v_b)` over the bits `b` of `j`, `s_b = s_{b-1} (s_{b-1} + s_{b-1}(v_{b-1}))`.
    fn novel_basis_at(p: usize, m: usize) -> (Vec<F64>, F64) {
        let sks = super::query::Normalizers::new(m).at_roots().to_vec();
        let mut s = F64(p as u64);
        let mut w = Vec::with_capacity(m + 1);
        for b in 0..=m {
            if b > 0 {
                s *= s + sks[b - 1];
            }
            w.push(s * sks[b].inv());
        }
        let mut x = vec![F64::ONE];
        for &w_b in &w[..m] {
            let high: Vec<F64> = x.iter().map(|&v| v * w_b).collect();
            x.extend(high);
        }
        (x, w[m])
    }

    /// Every lane of a hiding commitment is its `2^m + k` coefficients evaluated at every domain point: `Σ_j msg_j X_j(x) + W_m(x + s) Σ_j pad_j X_j(x)`, `s = F64(2^(m + r))`.
    ///
    /// The shapes take the encode's plans: replicas copied before a deep pass, and a gathered first pass at the rate layer (many lanes), at `r = 1` and beyond, the padding at most a whole lane.
    #[test]
    fn a_hiding_commitment_encodes_the_padded_lanes() {
        let mut rng = Rng::new(0x9AD);
        for (m, log_inv_rate, log_batch_size, n_lanes, k) in [
            (3usize, 1usize, 2usize, 3usize, 8usize),
            (5, 2, 3, 7, 5),
            (6, 4, 1, 2, 64),
            (9, 1, 3, 5, 37),
            (8, 1, 11, 2048, 13),
            (8, 2, 11, 2048, 9),
        ] {
            let log_n = m + log_batch_size;
            let msg: Vec<F64> = (0..n_lanes << m).map(|_| F64(rng.next_u64())).collect();
            let pads: Vec<F64> = (0..n_lanes * k).map(|_| F64(rng.next_u64())).collect();
            let pd = commit_hiding(&msg, log_n, log_batch_size, log_inv_rate, &pads);
            assert_eq!(pd.pads, pads);
            // Every lane of a narrow commitment; the ends and a spread of a wide one's.
            let lanes: Vec<usize> = (0..n_lanes)
                .filter(|&u| n_lanes < 64 || u % 97 == 0 || u + 1 == n_lanes)
                .collect();
            let s = 1usize << (m + log_inv_rate);
            for p in 0..s {
                let (x, _) = novel_basis_at(p, m);
                let (_, w_m_shifted) = novel_basis_at(p ^ s, m);
                for &u in &lanes {
                    let at = |coeffs: &[F64]| coeffs.iter().zip(&x).fold(F64::ZERO, |acc, (&c, &x_j)| acc + c * x_j);
                    let want = at(&msg[u << m..(u + 1) << m]) + w_m_shifted * at(&pads[u * k..(u + 1) * k]);
                    assert_eq!(
                        pd.codeword[p * n_lanes + n_lanes - 1 - u],
                        want,
                        "lane {u}, position {p}, m={m}, rate={log_inv_rate}, n_lanes={n_lanes}, k={k}"
                    );
                }
            }
        }
    }

    /// No domain point escapes the padding: a zero message padded by the constant one is nonzero everywhere.
    ///
    /// Padded by `W_m` alone, the first `2^m` points would show the message unmasked to any query landing there.
    #[test]
    fn a_hiding_commitment_pads_every_point() {
        for (m, log_inv_rate) in [(3usize, 1usize), (6, 2), (10, 1), (8, 4)] {
            let pd = commit_hiding(&vec![F64::ZERO; 1 << m], m + 1, 1, log_inv_rate, &[F64::ONE]);
            assert!(
                pd.codeword.iter().all(|&w| w != F64::ZERO),
                "an unpadded point at m={m}, rate={log_inv_rate}"
            );
        }
    }
}
