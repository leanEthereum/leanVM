use super::*;
use crate::merkle::Hash;
use crate::ring_switch::inner_product_ext;
use crate::whir_config::test_config_for;
use fiat_shamir::transcript::TranscriptError;
use primitives::field::powers;
use primitives::multilinear::{eq_eval, eq_table};
use primitives::test_rng::Rng;

struct Instance {
    vc: VerifierConfig,
    log_n: usize,
    /// The eq-point behind `b_initial` (for the succinct closure).
    point: Vec<F192>,
    b_initial: Vec<F192>,
    target: F192,
    root: Hash,
    /// The transcript: every scalar WHIR transmitted, plus its opening phases.
    fs: fiat_shamir::transcript::Proof,
}

fn prove_instance(log_n: usize, seed: u64) -> Instance {
    let pc = test_config_for(log_n);
    let mut rng = Rng::new(seed);
    let witness: Vec<F64> = (0..1usize << log_n).map(|_| F64(rng.next_u64())).collect();
    let (cm, pd) = commit(&witness, log_n, pc.initial_k(), pc.log_inv_rates()[0]);
    let point: Vec<F192> = (0..log_n).map(|_| rng.ext()).collect();
    let b_initial = eq_table(&point);
    let target = inner_product_base_ext(&witness, &b_initial);
    let mut ps = fiat_shamir::transcript::ProverState::from_label(b"whir-test");
    recursive_prover_with_basis(
        &pc,
        log_n,
        &witness,
        b_initial.to_vec(),
        target,
        &pd.codeword,
        &pd.merkle_tree,
        &mut ps,
    );
    Instance {
        vc: pc,
        log_n,
        point,
        b_initial,
        target,
        root: cm.root,
        fs: ps.into_proof(),
    }
}

/// The multilinear extension of `table` at `point`, from the whole table.
fn dense_mle(table: &[F192], point: &[F192]) -> F192 {
    inner_product_ext(table, &eq_table(point))
}

fn verify_with(
    inst: &Instance,
    fs: &fiat_shamir::transcript::Proof,
    eval_b_at: impl Fn(&[F192]) -> F192,
) -> Result<(), WhirError> {
    let mut vs = fiat_shamir::transcript::VerifierState::from_label(b"whir-test", fs);
    recursive_verifier_with_basis_succinct(
        &inst.vc,
        inst.log_n,
        1 << inst.vc.initial_k(),
        inst.target,
        &inst.root,
        eval_b_at,
        &mut vs,
    )
}

/// The weight evaluated in closed form at the terminal fold point.
fn verify_closed_form(inst: &Instance, fs: &fiat_shamir::transcript::Proof) -> bool {
    verify_with(inst, fs, |fold_point| eq_eval(&inst.point, fold_point)).is_ok()
}

/// The weight evaluated from its whole table at the terminal fold point.
fn verify_dense_weight(inst: &Instance, fs: &fiat_shamir::transcript::Proof) -> bool {
    verify_with(inst, fs, |fold_point| dense_mle(&inst.b_initial, fold_point)).is_ok()
}

/// Both weight evaluations on the same proof, asserting they agree; returns the
/// shared verdict.
fn verify_both_agree(inst: &Instance, fs: &fiat_shamir::transcript::Proof, what: &str) -> bool {
    let closed_form = verify_closed_form(inst, fs);
    let dense = verify_dense_weight(inst, fs);
    assert_eq!(closed_form, dense, "closed-form/dense verdict split on {what}");
    closed_form
}

/// Pin the production 128-bit Johnson/OOD profile rather than the small-
/// size test fallback.
#[test]
fn configs_johnson_profile_shape() {
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

/// At log_n = 18 the production profile's L0 has log_msg_cols = 12 and
/// enough queries to trip the sparse transposed-NTT dispatch in the prover;
/// pin the heuristic, then roundtrip.
#[test]
fn roundtrip_log_n_18_sparse_induce() {
    let pc = config_for_rate(18, LOG_INV_RATE_0).expect("Johnson profile feasible at log_n = 18");
    assert!(
        induce_use_ntt_heuristic(18 - pc.initial_k(), pc.log_inv_rates()[0], pc.queries()[0]),
        "shape must select the sparse transposed-NTT induce at L0"
    );
    // And the smaller roundtrips stay on the dense path (cols < 12).
    let pc16 = config_for_rate(16, LOG_INV_RATE_0).unwrap();
    assert!(!induce_use_ntt_heuristic(
        16 - pc16.initial_k(),
        pc16.log_inv_rates()[0],
        pc16.queries()[0]
    ));
    let inst = prove_instance(18, 8);
    assert!(verify_dense_weight(&inst, &inst.fs), "honest proof rejected");
    assert!(
        verify_closed_form(&inst, &inst.fs),
        "closed-form weight rejected an honest proof at log_n=18"
    );
}

/// Honest proofs are accepted and a spread of randomized single-bit tampers
/// rejected, with the weight evaluated in closed form and from its table, at
/// both a fallback-config shape (log_n = 12) and the Johnson/OOD production
/// shape (log_n = 16).
#[test]
fn tampered_proofs_are_rejected() {
    for (log_n, seed) in [(12usize, 11u64), (16, 12)] {
        let inst = prove_instance(log_n, seed);
        assert!(verify_both_agree(&inst, &inst.fs, "honest proof"));

        let mut rng = Rng::new(seed ^ 0xABCD);
        // One Merkle phase per level, in level order: phase 0 opens L0, the
        // last phase opens the final level.
        type Tamper = fn(&mut fiat_shamir::transcript::Proof, u64);
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

/// Every stream word is prover-chosen, including the limbs of a level root
/// and of every digest half. A tampered word must be REJECTED, never panic
/// the verifier: `next_root` rejects a non-canonical half rather than
/// handing it to a decoder that asserts.
#[test]
fn tampered_stream_words_reject_without_panicking() {
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
            let verdict = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| verify_closed_form(&inst, &bad)));
            match verdict {
                Ok(accepted) => assert!(!accepted, "tampered stream word {idx} accepted"),
                Err(_) => panic!("verifier panicked on tampered stream word {idx}"),
            }
        }
    }
}

/// Committing only the lanes that carry data must be indistinguishable from
/// committing the whole `2^log_n` witness with an explicit zero tail: same
/// root, byte-identical transcript, and the verifier accepts against the full
/// `2^log_n` weight. That indistinguishability is what lets the verifier stay
/// unaware of the lane count.
#[test]
fn truncated_lanes_match_an_explicit_zero_tail() {
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

            let prove = |msg: &[F64], b: &[F192]| {
                let (cm, pd) = commit(msg, log_n, pc.initial_k(), pc.log_inv_rates()[0]);
                let mut ps = fiat_shamir::transcript::ProverState::from_label(b"whir-test");
                recursive_prover_with_basis(
                    &pc,
                    log_n,
                    msg,
                    b.to_vec(),
                    target,
                    &pd.codeword,
                    &pd.merkle_tree,
                    &mut ps,
                );
                (cm.root, ps.into_proof())
            };
            let (root_trunc, fs_trunc) = prove(&witness[..used], &b_initial[..used]);
            let (root_full, fs_full) = prove(&witness, &b_initial);
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
            let verify = |fs: &fiat_shamir::transcript::Proof| {
                let mut vs = fiat_shamir::transcript::VerifierState::from_label(b"whir-test", fs);
                recursive_verifier_with_basis_succinct(
                    &pc,
                    log_n,
                    n_lanes,
                    target,
                    &root_trunc,
                    |point| dense_mle(&b_initial, point),
                    &mut vs,
                )
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

/// The sparse transposed-NTT induce must be byte-identical to the dense
/// LCH-expansion induce (same guarantee the original pins). Covers both
/// the windowed sparse-prefix path (log_block >= 12, k = 8) and the
/// scatter + full-dense-transpose path (log_block < 12, k = 0).
#[test]
fn induce_via_ntt_matches_dense() {
    let mut rng = Rng::new(9);
    for (log_msg_cols, log_inv_rate, lanes_log, n_queries) in [(12usize, 1usize, 5usize, 130usize), (6, 2, 3, 40)] {
        let block_len = 1usize << (log_msg_cols + log_inv_rate);
        let lanes = 1usize << lanes_log;
        // Distinct sorted query positions plus one aligned random row each.
        let mut qs: Vec<usize> = Vec::new();
        let mut seen = std::collections::HashSet::new();
        while qs.len() < n_queries {
            let q = (rng.next_u64() as usize) % block_len;
            if seen.insert(q) {
                qs.push(q);
            }
        }
        qs.sort_unstable();
        let rows: Vec<Vec<F64>> = (0..n_queries)
            .map(|_| (0..lanes).map(|_| F64(rng.next_u64())).collect())
            .collect();
        let v_challenges: Vec<F192> = (0..lanes_log).map(|_| rng.ext()).collect();
        let weights = powers(rng.ext(), n_queries);

        let sks_vks = eval_sk_at_vks(log_msg_cols);
        let dense = induce_sumcheck_poly(log_msg_cols, &sks_vks, &rows, &v_challenges, &qs, &weights);
        let via_ntt =
            induce_sumcheck_poly_via_ntt_base(log_msg_cols, log_inv_rate, &rows, &v_challenges, &qs, &weights);
        assert_eq!(dense.1, via_ntt.1, "enforced_sum mismatch");
        assert_eq!(&*dense.0, &*via_ntt.0, "basis_poly mismatch");
    }
}

#[test]
fn the_residual_closed_form_is_the_induced_basis() {
    // Invariant: the closed form at `prefix ++ y` is the induced basis's multilinear extension there, for every
    // Boolean `y`.
    let mut rng = Rng::new(0x5E51);
    let (log_msg_cols, log_inv_rate, lanes_log, n_queries) = (7usize, 2usize, 2usize, 37usize);
    let block_len = 1usize << (log_msg_cols + log_inv_rate);
    // Fixture state: queries in transcript order, repeats allowed, as the verifier samples them.
    let queries: Vec<usize> = (0..n_queries).map(|_| rng.next_u64() as usize % block_len).collect();
    let rows: Vec<Vec<F192>> = (0..n_queries).map(|_| rng.ext_vec(1 << lanes_log)).collect();
    let v_challenges = rng.ext_vec(lanes_log);
    let weights = powers(rng.ext(), n_queries);
    let sks_vks = eval_sk_at_vks(log_msg_cols);
    let (basis, _) = induce_sumcheck_poly(log_msg_cols, &sks_vks, &rows, &v_challenges, &queries, &weights);

    // The whole point (the verifier's terminal check), a partial one, and the Boolean cube (the prover's last level).
    for yr_log_n in [0, 3, log_msg_cols] {
        let prefix = rng.ext_vec(log_msg_cols - yr_log_n);
        let at = induce_sumcheck_evaluate_at_residual(log_msg_cols, &sks_vks, &queries, &weights, &prefix, yr_log_n);
        assert_eq!(at.len(), 1 << yr_log_n);
        for (y, &got) in at.iter().enumerate() {
            let mut point = prefix.clone();
            point.extend((0..yr_log_n).map(|j| F192::from(F64(((y >> j) & 1) as u64))));
            assert_eq!(got, dense_mle(&basis, &point), "yr_log_n={yr_log_n}, y={y}");
        }
    }
}
