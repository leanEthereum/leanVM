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

use fiat_shamir::Challenger;
use primitives::field::{F64, F192};
use primitives::multilinear::inner_product_base;

pub use config::{
    Config, INITIAL_FOLDING_FACTOR, L0_LIST_BITS, LOG_INV_RATE_0, MAX_LOG_INV_RATE, MAX_LOG_N, MIN_LOG_INV_RATE,
    MIN_LOG_N, QUERY_GRINDING_BITS, RESIDUAL_MAX_LOG, RS_DOMAIN_INITIAL_REDUCTION_FACTOR, SECURITY_BITS,
    SUBSEQUENT_FOLDING_FACTOR, config_for_rate,
};

pub(crate) use commit::{ProverData, commit};
pub(crate) use prove::prove;
pub(crate) use sumcheck::{INITIAL_BASIS_CHUNK, InitialWeight};
pub use verify::WhirError;
pub(crate) use verify::verify;

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
        let v: F192 = ch.verifier_message();
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
    use crate::merkle::{Hash, PrunedMerklePaths};
    use crate::whir::config::tests::test_config_for;
    use crate::whir::query::QueryBatch;
    use fiat_shamir::{ProofTranscript, ProverState, SessionId, TranscriptError, VerifierState};
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
        let mut ps = ProverState::new(&SessionId::new(b"whir-test"), &0u64);
        let weight = Table {
            weight: b_initial.to_vec(),
            block: 1 << (log_n - pc.initial_k()),
        };
        prove(&pc, log_n, &witness, &weight, target, &pd, &mut ps);
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
        let mut vs = VerifierState::new(&SessionId::new(b"whir-test"), &0u64, fs);
        verify(
            &mut vs,
            &inst.vc,
            inst.log_n,
            1 << inst.vc.initial_k(),
            inst.target,
            inst.root,
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

            // One hint per level, in level order: hint 0 opens L0, the last hint opens the final level.
            //
            //     hint = [4-byte length | rows' words | siblings]
            type Tamper = fn(&mut ProofTranscript);
            let tampers: &[(&str, Tamper)] = &[
                ("L0 opened row", |p| {
                    let start = hint_starts(&p.hints)[0];
                    p.hints[start] ^= 1;
                }),
                ("final-level opened row", |p| {
                    let start = *hint_starts(&p.hints).last().unwrap();
                    p.hints[start] ^= 1;
                }),
                ("merkle proof node", |p| {
                    let end = hint_starts(&p.hints)[1] - 4;
                    p.hints[end - 1] ^= 1;
                }),
            ];
            for (what, tamper) in tampers {
                let mut bad_fs = inst.fs.clone();
                tamper(&mut bad_fs);
                assert!(
                    !verify_both_agree(&inst, &bad_fs, what),
                    "tampered {what} accepted at log_n={log_n}"
                );
            }
            // Every message (sumcheck messages, level roots, OOD claims, `yr`, the nonces) is NARG bytes.
            //
            // A bound byte re-rolls the challenges after it, a nonce byte fails its proof of work.
            let n_bytes = inst.fs.narg.len();
            assert!(n_bytes > 0, "WHIR sent nothing");
            for idx in (0..n_bytes).step_by(1 + n_bytes / 24) {
                let mut bad_fs = inst.fs.clone();
                bad_fs.narg[idx] ^= 1;
                assert!(
                    !verify_both_agree(&inst, &bad_fs, "message byte"),
                    "tampered message byte {idx} accepted at log_n={log_n}"
                );
            }
        }
    }

    // The first hint's bytes, past its 4-byte length.
    fn first_hint(fs: &ProofTranscript) -> &[u8] {
        let len = u32::from_le_bytes(fs.hints[..4].try_into().unwrap()) as usize;
        &fs.hints[4..4 + len]
    }

    // Where each hint's bytes start, past its 4-byte length.
    fn hint_starts(hints: &[u8]) -> Vec<usize> {
        let mut starts = Vec::new();
        let mut at = 0;
        while at < hints.len() {
            let len = u32::from_le_bytes(hints[at..at + 4].try_into().unwrap()) as usize;
            starts.push(at + 4);
            at += 4 + len;
        }
        starts
    }

    #[test]
    fn tampered_messages_reject_without_panicking() {
        // Invariant: every message byte is the prover's, so a tampered one is refused, never a panic.
        let inst = prove_instance(12, 11);
        let mut short = inst.fs.clone();
        short.narg.truncate(1);
        assert_eq!(
            verify_with(&inst, &short, |point| eq_eval(&inst.point, point)),
            Err(WhirError::Transcript(TranscriptError::Malformed { index: 0 })),
        );
        for idx in (0..inst.fs.narg.len()).step_by(5) {
            let mut bad = inst.fs.clone();
            bad.narg[idx] ^= 0x80;
            let verdict = std::panic::catch_unwind(AssertUnwindSafe(|| verify_closed_form(&inst, &bad)));
            match verdict {
                Ok(accepted) => assert!(!accepted, "tampered message byte {idx} accepted"),
                Err(_) => panic!("verifier panicked on tampered message byte {idx}"),
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
                    let mut ps = ProverState::new(&SessionId::new(b"whir-test"), &0u64);
                    let weight = Table {
                        weight: b.to_vec(),
                        block: lane_block,
                    };
                    prove(&pc, log_n, msg, &weight, target, &pd, &mut ps);
                    (pd.root(), ps.into_proof())
                };
                let (root_trunc, fs_trunc) = prove_with(&witness[..used], &b_initial[..used]);
                let (root_full, fs_full) = prove_with(&witness, &b_initial);
                assert_eq!(root_trunc, root_full, "root differs at n_lanes = {n_lanes}");
                assert_eq!(
                    fs_trunc.narg, fs_full.narg,
                    "the protocol itself must not change at n_lanes = {n_lanes}"
                );

                // What the two proofs DO differ in, and the point of the exercise: the
                // truncated one stores each L0 row as the committed lanes alone, which is
                // exactly the full image with its leading padding zeros dropped.
                let leaf_words = 1usize << pc.initial_k();
                let (thin, full) = (first_hint(&fs_trunc), first_hint(&fs_full));
                let distinct = (full.len() - thin.len()) / (8 * (leaf_words - n_lanes).max(1));
                let thin = PrunedMerklePaths::from_hint(thin, distinct, n_lanes).unwrap();
                let full = PrunedMerklePaths::from_hint(full, distinct, leaf_words).unwrap();
                for (thin, full) in thin.leaf_data.iter().zip(&full.leaf_data) {
                    assert_eq!(thin[..], full[leaf_words - n_lanes..], "stored row is the image tail");
                    assert!(
                        full[..leaf_words - n_lanes].iter().all(|w| *w == F64::ZERO),
                        "the words the proof drops are the padding at n_lanes = {n_lanes}"
                    );
                }

                // The verifier evaluates the weight over the whole `2^log_n` cube.
                let verify = |fs: &ProofTranscript| {
                    let mut vs = VerifierState::new(&SessionId::new(b"whir-test"), &0u64, fs);
                    verify(&mut vs, &pc, log_n, n_lanes, target, root_trunc, |_, point| {
                        dense_mle(&b_initial, point)
                    })
                };
                assert_eq!(verify(&fs_trunc), Ok(()), "verify failed at n_lanes = {n_lanes}");

                // The image the octopus was built over is pinned by the announced widths,
                // so a row of any other width is rejected rather than zero-extended to
                // something that happens to hash.
                if n_lanes < leaf_words {
                    // One more word in the first hint: 8 bytes inserted after the first row.
                    let mut bad_fs = fs_trunc.clone();
                    let len = u32::from_le_bytes(bad_fs.hints[..4].try_into().unwrap()) + 8;
                    bad_fs.hints[..4].copy_from_slice(&len.to_le_bytes());
                    let at = 4 + 8 * n_lanes;
                    bad_fs.hints.splice(at..at, [0; 8]);
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
                let mut ps = ProverState::new(&SessionId::new(b"whir-test"), &0u64);
                let table = Table {
                    weight: weight[..used].to_vec(),
                    block: lane_block,
                };
                prove(&pc, log_n, &witness, &table, target, &pd, &mut ps);
                let fs = ps.into_proof();

                let check = |target: F192| {
                    let mut vs = VerifierState::new(&SessionId::new(b"whir-test"), &0u64, &fs);
                    verify(&mut vs, &pc, log_n, n_lanes, target, pd.root(), |_, point| {
                        dense_mle(&weight, point)
                    })
                };
                let label = format!("rate={log_inv_rate}, n_lanes={n_lanes}");
                assert_eq!(check(target), Ok(()), "{label}");
                assert!(check(target + F192::ONE).is_err(), "{label}");
            }
        }
    }
}
