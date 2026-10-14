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
//!     config    the protocol's constants and one opening's per-level parameters
//!     commit    the L0 base encode and the deeper levels' encodes, Merkle-committed
//!     query     the query positions, and the weight a level's queries induce
//!     sumcheck  the round messages, the fold kernels, the running claim
//!     prove     the prover, level by level
//!     verify    the succinct verifier
//! ```

pub(crate) mod anchor;
mod commit;
pub(crate) mod config;
mod prove;
mod query;
mod sumcheck;
mod verify;

pub use commit::{Commitment, CommitmentShape};
pub use config::{
    Config, ConfigError, INITIAL_FOLDING_FACTOR, L0_LIST_BITS, LOG_INV_RATE_0, MAX_LOG_INV_RATE, MAX_LOG_N,
    MIN_LOG_INV_RATE, MIN_LOG_N, MIN_LOG_N_HIDING, SECURITY_BITS,
};
pub use query::Stratum;
pub use verify::WhirError;

pub(crate) use commit::{BaseCommitment, commit, receive_commitment, send_record_binding, verify_record_binding};
pub(crate) use config::RANDOM_LANES;
pub(crate) use prove::prove;
pub(crate) use query::sample_queries;
pub(crate) use sumcheck::{DenseWeight, INITIAL_BASIS_CHUNK, InitialWeight};
pub(crate) use verify::{WeightAt, check_config_shape, verify};

#[cfg(test)]
mod tests {
    use super::*;
    use crate::merkle::{Hash, PrunedMerklePaths};
    use crate::ntt::{NovelBasis, basis_values};
    use crate::verifier::OpeningVerifier;
    use crate::whir::config::tests::test_config_for;
    use crate::whir::config::{QUERY_GRINDING_BITS, RANDOM_LANES};
    use crate::whir::query::{Padding, QueryBatch};
    use fiat_shamir::{Hints, ProofTranscript, ProverState, SessionId, TranscriptError, VerifierState};
    use primitives::field::{F64, F192};
    use primitives::multilinear::{eq_eval, eq_table, inner_product, inner_product_base};
    use primitives::test_util::Rng;
    use std::panic::AssertUnwindSafe;

    struct Instance {
        vc: Config,
        log_n: usize,
        /// The eq-point behind `b_initial` (for the closed-form weight).
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
        let mut commit_ps = ProverState::new(&SessionId::new(b"whir-commit"), &0u64);
        let (record, pd) = commit(&mut commit_ps, &witness, log_n, pc.initial_k(), pc.log_inv_rates()[0]);
        let point: Vec<F192> = (0..log_n).map(|_| rng.ext()).collect();
        let b_initial = eq_table(&point);
        let target = inner_product_base(&witness, &b_initial);
        let mut ps = ProverState::new(&SessionId::new(b"whir-test"), &0u64);
        ps.prover_message(&record.root());
        let weight = DenseWeight {
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
            root: record.root(),
            fs: ps.into_proof(),
        }
    }

    /// The multilinear extension of `table` at `point`, from the whole table.
    fn dense_mle(table: &[F192], point: &[F192]) -> F192 {
        inner_product(table, &eq_table(point))
    }

    struct EqWeight<'a>(&'a [F192]);

    impl<V: crate::verifier::OpeningVerifier<E = F192>> WeightAt<V> for EqWeight<'_> {
        fn call(self, _: &mut V, point: &[F192]) -> F192 {
            eq_eval(self.0, point)
        }
    }

    struct DenseWeightAt<'a>(&'a [F192]);

    impl<V: crate::verifier::OpeningVerifier<E = F192>> WeightAt<V> for DenseWeightAt<'_> {
        fn call(self, _: &mut V, point: &[F192]) -> F192 {
            dense_mle(self.0, point)
        }
    }

    fn verify_with(
        inst: &Instance,
        fs: &ProofTranscript,
        weight_at: impl for<'v> WeightAt<VerifierState<'v>>,
    ) -> Result<(), WhirError> {
        let mut vs = VerifierState::new(&SessionId::new(b"whir-test"), &0u64, fs);
        let root = vs.next_root()?;
        if root != inst.root {
            return Err(WhirError::CommitmentMismatch);
        }
        verify(
            &mut vs,
            &inst.vc,
            inst.log_n,
            1 << inst.vc.initial_k(),
            inst.target,
            inst.root,
            weight_at,
        )
    }

    /// The weight evaluated in closed form at the terminal fold point.
    fn verify_closed_form(inst: &Instance, fs: &ProofTranscript) -> bool {
        verify_with(inst, fs, EqWeight(&inst.point)).is_ok()
    }

    /// The weight evaluated from its whole table at the terminal fold point.
    fn verify_dense_weight(inst: &Instance, fs: &ProofTranscript) -> bool {
        verify_with(inst, fs, DenseWeightAt(&inst.b_initial)).is_ok()
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
        let pc = Config::for_rate(16, LOG_INV_RATE_0).expect("Johnson profile feasible at log_n = 16");
        assert_eq!(pc.initial_k(), 6);
        assert!(pc.level_steps() >= 1);
        assert_eq!(pc.ood_samples()[0], 0);
        assert!(pc.ood_samples().iter().skip(1).all(|&s| s >= 1));
        assert!(pc.grinding_bits().iter().all(|&b| b == QUERY_GRINDING_BITS));
        // And log_n = 12 is below the production ladder's feasibility floor, so
        // the tests there use the default_config fallback.
        assert!(Config::for_rate(12, LOG_INV_RATE_0).is_err());
    }

    #[test]
    fn roundtrip_log_n_18_sparse_induce() {
        // Invariant: at log_n = 18 the L0 induce takes the sparse transposed NTT, and the proof still verifies.
        //
        // Fixture state: L0 has 2^12 message columns, enough queries to trip the dispatch; at log_n = 16 it stays dense.
        let takes_transposed = |log_n: usize| {
            let pc = Config::for_rate(log_n, LOG_INV_RATE_0).unwrap();
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

    /// Where each hint's bytes start in the framed hints, past its four-byte length.
    fn hint_starts(hints: &[u8]) -> Vec<usize> {
        let mut walk = Hints::new(hints);
        let mut starts = Vec::new();
        loop {
            // A hint's bytes start four bytes past the unread tail's start.
            let at = hints.len() - walk.as_slice().len() + 4;
            if walk.next().is_none() {
                return starts;
            }
            starts.push(at);
        }
    }

    #[test]
    fn tampered_messages_reject_without_panicking() {
        // Invariant: every message byte is the prover's, so a tampered one is refused, never a panic.
        let inst = prove_instance(12, 11);
        let mut short = inst.fs.clone();
        short.narg.truncate(1);
        assert_eq!(
            verify_with(&inst, &short, EqWeight(&inst.point)),
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
        // Kernel invariant: dropping the witness's zero tail preserves its root and
        // recursive proof. The immutable public record additionally binds n_lanes,
        // so complete commitment/opening transcripts deliberately differ by shape.
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
                let target = inner_product_base(&witness, &b_initial);

                let prove_with = |msg: &[F64], b: &[F192]| {
                    let mut commit_ps = ProverState::new(&SessionId::new(b"whir-commit"), &0u64);
                    let (record, pd) = commit(&mut commit_ps, msg, log_n, pc.initial_k(), pc.log_inv_rates()[0]);
                    let mut ps = ProverState::new(&SessionId::new(b"whir-test"), &0u64);
                    ps.prover_message(&record.root());
                    let weight = DenseWeight {
                        weight: b.to_vec(),
                        block: lane_block,
                    };
                    prove(&pc, log_n, msg, &weight, target, &pd, &mut ps);
                    (record.root(), ps.into_proof())
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
                let (thin, full) = (
                    fs_trunc.iter_hints().next().unwrap(),
                    fs_full.iter_hints().next().unwrap(),
                );
                let distinct = (full.len() - thin.len()) / (8 * (leaf_words - n_lanes).max(1));
                let thin = PrunedMerklePaths::from_hint(thin, distinct, n_lanes).unwrap();
                let full = PrunedMerklePaths::from_hint(full, distinct, leaf_words).unwrap();
                for (thin, full) in thin.rows.chunks(n_lanes).zip(full.rows.chunks(leaf_words)) {
                    assert_eq!(thin[..], full[leaf_words - n_lanes..], "stored row is the image tail");
                    assert!(
                        full[..leaf_words - n_lanes].iter().all(|w| *w == F64::ZERO),
                        "the words the proof drops are the padding at n_lanes = {n_lanes}"
                    );
                }

                // The verifier evaluates the weight over the whole `2^log_n` cube.
                let verify = |fs: &ProofTranscript| {
                    let mut vs = VerifierState::new(&SessionId::new(b"whir-test"), &0u64, fs);
                    let root = vs.next_root()?;
                    if root != root_trunc {
                        return Err(WhirError::CommitmentMismatch);
                    }
                    verify(
                        &mut vs,
                        &pc,
                        log_n,
                        n_lanes,
                        target,
                        root_trunc,
                        DenseWeightAt(&b_initial),
                    )
                };
                assert_eq!(verify(&fs_trunc), Ok(()), "verify failed at n_lanes = {n_lanes}");

                // The image the octopus was built over is pinned by the announced widths,
                // so a row of any other width is rejected rather than zero-extended to
                // something that happens to hash.
                if n_lanes < leaf_words {
                    // One more word in the first hint: 8 zero bytes inserted after the first row.
                    let mut hints: Vec<Vec<u8>> = fs_trunc.iter_hints().map(<[u8]>::to_vec).collect();
                    hints[0].splice(8 * n_lanes..8 * n_lanes, [0; 8]);
                    let mut bad_fs = ProofTranscript {
                        narg: fs_trunc.narg.clone(),
                        hints: Vec::new(),
                    };
                    for hint in &hints {
                        bad_fs.push_hint(hint);
                    }
                    assert!(
                        verify(&bad_fs).is_err(),
                        "a wrong-width row was accepted at n_lanes = {n_lanes}"
                    );
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
            let pc = Config::for_rate(log_n, log_inv_rate).expect("a supported rate");
            let lane_block = 1usize << (log_n - pc.initial_k());
            for n_lanes in [1, (1 << pc.initial_k()) / 2 + 1, 1 << pc.initial_k()] {
                let mut rng = Rng::new((log_inv_rate * 1000 + n_lanes) as u64);
                let used = n_lanes * lane_block;
                let witness: Vec<F64> = (0..used).map(|_| F64(rng.next_u64())).collect();
                let mut weight = vec![F192::ZERO; 1 << log_n];
                weight[..used].copy_from_slice(&rng.ext_vec(used));
                let target = inner_product_base(&witness, &weight[..used]);

                let mut ps = ProverState::new(&SessionId::new(b"whir-test"), &0u64);
                let (record, pd) = commit(&mut ps, &witness, log_n, pc.initial_k(), log_inv_rate);
                let table = DenseWeight {
                    weight: weight[..used].to_vec(),
                    block: lane_block,
                };
                prove(&pc, log_n, &witness, &table, target, &pd, &mut ps);
                let fs = ps.into_proof();

                let check = |target: F192| {
                    let mut vs = VerifierState::new(&SessionId::new(b"whir-test"), &0u64, &fs);
                    receive_commitment(&mut vs, log_n, pc.initial_k(), log_inv_rate, n_lanes)?;
                    verify(
                        &mut vs,
                        &pc,
                        log_n,
                        n_lanes,
                        target,
                        record.root(),
                        DenseWeightAt(&weight),
                    )
                };
                let label = format!("rate={log_inv_rate}, n_lanes={n_lanes}");
                assert_eq!(check(target), Ok(()), "{label}");
                assert!(check(target + F192::ONE).is_err(), "{label}");
            }
        }
    }

    /// The novel basis at codeword position `p`, the field element `F64(p)`: `X_j(p)` for `j < 2^m`, then `W_m(p)`.
    fn novel_basis_at(p: usize, m: usize) -> (Vec<F64>, F64) {
        let mut w = vec![F64::ZERO; m + 1];
        NovelBasis::new(m).normalized_at(F64(p as u64), &mut w);
        (basis_values(&w[..m]), w[m])
    }

    #[test]
    fn a_hiding_commitment_encodes_the_padded_lanes() {
        // Invariant: every lane of a hiding commitment is its `2^m + k` coefficients at every domain point.
        //
        //     lane(x) = sum_j msg_j X_j(x) + W_m(x + s) sum_j pad_j X_j(x),   s = F64(2^(m + r))
        //
        // Fixture state: the encode's plans, replicas copied before a deep pass and a gathered first pass at the rate layer.
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
            let pd = BaseCommitment::new(&msg, log_n, log_batch_size, log_inv_rate, &pads);
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
                        pd.row(p)[n_lanes - 1 - u],
                        want,
                        "lane {u}, position {p}, m={m}, rate={log_inv_rate}, n_lanes={n_lanes}, k={k}"
                    );
                }
            }
        }
    }

    #[test]
    fn a_hiding_commitment_pads_every_point() {
        // Invariant: no domain point escapes the padding, so a zero message padded by the constant one is nonzero everywhere.
        //
        // Padded by `W_m` alone, the first `2^m` points would show the message unmasked to any query landing there.
        for (m, log_inv_rate) in [(3usize, 1usize), (6, 2), (10, 1), (8, 4)] {
            let pd = BaseCommitment::new(&vec![F64::ZERO; 1 << m], m + 1, 1, log_inv_rate, &[F64::ONE]);
            assert!(
                (0..pd.num_positions()).all(|p| pd.row(p).iter().all(|&w| w != F64::ZERO)),
                "an unpadded point at m={m}, rate={log_inv_rate}"
            );
        }
    }

    /// The rank over `K` of elements of `E`, each its three coordinates over `K`.
    fn k_rank(elements: &[F192]) -> usize {
        let mut rows: Vec<[F64; 3]> = elements.iter().map(|x| [F64(x.c0), F64(x.c1), F64(x.c2)]).collect();
        let mut rank = 0;
        for col in 0..3 {
            // Find a row with a nonzero entry in this column, below the rows already used.
            let Some(pivot) = (rank..rows.len()).find(|&i| rows[i][col] != F64::ZERO) else {
                continue;
            };
            rows.swap(rank, pivot);
            let inv = rows[rank][col].inv();
            let pivot_row = rows[rank];
            // Clear the column in every other row.
            for (i, row) in rows.iter_mut().enumerate() {
                if i != rank && row[col] != F64::ZERO {
                    let f = row[col] * inv;
                    for c in 0..3 {
                        row[c] += f * pivot_row[c];
                    }
                }
            }
            rank += 1;
        }
        rank
    }

    /// What a verifier computes at each level-0 query of a hiding opening: the folded row, the padding's share taken off.
    ///
    /// The data is fixed and the lane challenges `r` too, so only the prover's randomness moves the values.
    /// With `random`, the uniform lanes the prover draws; the other lanes of the random group stay zero.
    fn corrected_values(data: &[F64], r: &[F192], queries: &[usize], random: &[usize], seed: u64) -> Vec<F192> {
        let config = Config::hiding(MIN_LOG_N_HIDING, 1).unwrap();
        let (initial_k, k) = (config.initial_k(), config.padding());
        let lane = 1usize << (MIN_LOG_N_HIDING - initial_k);
        let data_lanes = data.len() / lane;
        let n_lanes = Config::hiding_lanes(data_lanes);
        let mut rng = Rng::new(seed);

        // The stack: the data, zero lanes, and only the chosen lanes of the random group drawn.
        let mut stack = data.to_vec();
        stack.resize(n_lanes * lane, F64::ZERO);
        for &u in random {
            stack[u * lane..(u + 1) * lane]
                .iter_mut()
                .for_each(|w| *w = F64(rng.next_u64()));
        }
        let pads: Vec<F64> = (0..n_lanes * k).map(|_| F64(rng.next_u64())).collect();
        let pd = BaseCommitment::new(&stack, MIN_LOG_N_HIDING, initial_k, 1, &pads);

        // The padding's lane fold, as the prover sends it.
        let eq = eq_table(r);
        let g1: Vec<F192> = (0..k)
            .map(|j| (0..n_lanes).fold(F192::ZERO, |acc, u| acc + eq[u].mul_base(pads[u * k + j])))
            .collect();

        // Each query's folded row, lane-ascending, plus the padding's share.
        queries
            .iter()
            .map(|&q| {
                let mut row = vec![F64::ZERO; 1 << initial_k];
                for (t, &w) in pd.row(q).iter().enumerate() {
                    row[n_lanes - 1 - t] = w;
                }
                let (pos, one) = ([q], [F192::ONE]);
                let batch = QueryBatch::new(&pos, &one);
                batch.claimed_sum(&[row], r)
                    + batch.padding_correction(&Padding::new(lane.trailing_zeros() as usize, 1), &g1)
            })
            .collect()
    }

    #[test]
    fn the_random_group_hides_every_coordinate_of_the_folded_witness() {
        // A corrected level-0 value is the folded witness's codeword at the query, a functional with coefficients in `K`.
        //
        // Invariant: across fresh prover randomness, its differences must span all of `E` over `K`.
        //
        //     rank 3: uniform in E, nothing of the data shows
        //     rank 1: only the line eq(r, u) * K moves, and the two other K coordinates are the data's
        let config = Config::hiding(MIN_LOG_N_HIDING, 1).unwrap();
        let lane = 1usize << (MIN_LOG_N_HIDING - config.initial_k());
        let mut rng = Rng::new(0xF01D);
        let data: Vec<F64> = (0..5 * lane).map(|_| F64(rng.next_u64())).collect();
        let r = rng.ext_vec(config.initial_k());
        let queries: Vec<usize> = (0..8).map(|_| rng.next_u64() as usize % (2 * lane)).collect();
        let group = Config::hiding_lanes(5) - RANDOM_LANES..Config::hiding_lanes(5);

        // The rank of each query's differences over four draws of the prover's randomness.
        let ranks = |random: &[usize]| -> Vec<usize> {
            let draws: Vec<Vec<F192>> = (0..4)
                .map(|s| corrected_values(&data, &r, &queries, random, s))
                .collect();
            (0..queries.len())
                .map(|i| k_rank(&(1..4).map(|t| draws[t][i] + draws[0][i]).collect::<Vec<_>>()))
                .collect()
        };

        // The whole random group: every query's value moves in all three coordinates.
        let all: Vec<usize> = group.clone().collect();
        assert!(
            ranks(&all).iter().all(|&rank| rank == 3),
            "the random group hides every coordinate"
        );

        // Negative control: one uniform lane leaves two coordinates fixed by the data.
        assert!(
            ranks(&[group.start]).iter().all(|&rank| rank == 1),
            "one lane masks one coordinate"
        );
    }
}
