// Credits: whir-p3 (https://github.com/tcoratger/whir-p3) (MIT and Apache-2.0 licenses).

use std::time::Instant;

use fiat_shamir::{ProverState, VerifierState};
use field::{Field, TwoAdicField};
use koala_bear::{KoalaBear, QuinticExtensionFieldKB, default_koalabear_poseidon1_16};
use poly::*;
use rand::{RngExt, SeedableRng, rngs::StdRng};
use tracing_forest::{ForestLayer, util::LevelFilter};
use tracing_subscriber::{EnvFilter, Registry, layer::SubscriberExt, util::SubscriberInitExt};
use whir::*;
use zk_alloc::ArenaVec;

type F = KoalaBear;
type EF = QuinticExtensionFieldKB;

/*
WHIR_NUM_VARIABLES=25 WHIR_LOG_INV_RATE=1 cargo test --release --package whir --test run_whir -- test_run_whir --exact --nocapture
*/

#[test]
fn test_run_whir() {
    if true {
        let env_filter: EnvFilter = EnvFilter::builder()
            .with_default_directive(LevelFilter::INFO.into())
            .from_env_lossy();

        let _ = Registry::default()
            .with(env_filter)
            .with(ForestLayer::default())
            .try_init();
    }
    let poseidon16 = default_koalabear_poseidon1_16();

    let num_variables = std::env::var("WHIR_NUM_VARIABLES")
        .ok()
        .and_then(|s| s.parse::<usize>().ok())
        .unwrap_or(18);
    let starting_log_inv_rate = std::env::var("WHIR_LOG_INV_RATE")
        .ok()
        .and_then(|s| s.parse::<usize>().ok())
        .unwrap_or(2);

    let num_coeffs = 1 << num_variables;

    let params = WhirConfigBuilder {
        security_level: 124,
        max_num_variables_to_send_coeffs: 9,
        pow_bits: 18,
        folding_factor: FoldingFactor::new(7, 4),
        soundness_type: SecurityAssumption::JohnsonBound,
        starting_log_inv_rate,
        rs_domain_initial_reduction_factor: 5,
    };
    let params = WhirConfig::new(&params, num_variables);

    for (i, round) in params.round_parameters.iter().enumerate() {
        println!("round {}: {} queries", i, round.num_queries);
    }

    let mut rng = StdRng::seed_from_u64(0);
    let polynomial = (0..num_coeffs).map(|_| rng.random::<F>()).collect::<Vec<F>>();

    let random_sparse_point = |rng: &mut StdRng, num_variables: usize| {
        let selector_len = rng.random_range(0..num_variables / 2);
        let point = (0..num_variables - selector_len)
            .map(|_| rng.random())
            .collect::<Vec<EF>>();
        (selector_len, MultilinearPoint(point))
    };

    // Sample `num_points` random multilinear points in the Boolean hypercube
    let mut points = (0..7)
        .map(|_| random_sparse_point(&mut rng, num_variables))
        .collect::<Vec<_>>();
    points.push((num_variables, MultilinearPoint(vec![])));

    let mut statement = Vec::new();

    // Add constraints for each sampled point (equality constraints)
    for (selector_len, point) in &points {
        let num_selectors = rng.random_range(1..5);
        let mut selectors = vec![];
        for _ in 0..num_selectors {
            let selector = rng.random_range(0..(1 << selector_len));
            if !selectors.contains(&selector) {
                selectors.push(selector);
            }
        }
        statement.push(SparseStatement::new(
            num_variables,
            point.clone(),
            selectors
                .iter()
                .map(|selector| SparseValue {
                    selector: *selector,
                    value: polynomial.evaluate_sparse(*selector, point),
                })
                .collect(),
        ));
    }

    let mut prover_state = ProverState::new(poseidon16.clone(), Default::default());

    precompute_dft_twiddles::<F>(1 << F::TWO_ADICITY);

    let polynomial: MleOwned<EF> = MleOwned::Base(ArenaVec::from_iter(polynomial));

    let time = Instant::now();
    let witness = params.commit(&mut prover_state, &polynomial, num_coeffs);
    let commit_time = time.elapsed();

    let witness_clone = witness.clone();
    let time = Instant::now();
    params.prove(
        &mut prover_state,
        statement.clone(),
        witness_clone,
        &polynomial.by_ref(),
    );
    let pruned_proof = prover_state.into_proof();
    let opening_time_single = time.elapsed();

    let proof_size_single = pruned_proof.proof_size_fe() as f64 * F::bits() as f64 / 8.0;

    let mut verifier_state = VerifierState::<EF, _>::new(pruned_proof, poseidon16.clone(), Default::default()).unwrap();

    let parsed_commitment = params.parse_commitment::<F>(&mut verifier_state).unwrap();

    params
        .verify::<F>(&mut verifier_state, &parsed_commitment, statement.clone())
        .unwrap();

    println!(
        "\nProving time: {} ms (commit: {} ms, opening: {} ms), proof size: {:.2} KiB",
        commit_time.as_millis() + opening_time_single.as_millis(),
        commit_time.as_millis(),
        opening_time_single.as_millis(),
        proof_size_single / 1024.0
    );
}

#[test]
fn display_whir_round_info() {
    let first_folding_factor = 7;
    for n_vars in 20..31 {
        for log_inv_rate in 1..5 {
            if n_vars + log_inv_rate - first_folding_factor > F::TWO_ADICITY {
                continue;
            }
            let params = WhirConfigBuilder {
                security_level: 124,
                max_num_variables_to_send_coeffs: 8,
                pow_bits: 16,
                folding_factor: FoldingFactor::new(first_folding_factor, 5),
                soundness_type: SecurityAssumption::JohnsonBound,
                starting_log_inv_rate: log_inv_rate,
                rs_domain_initial_reduction_factor: 5,
            };
            let params = WhirConfig::<EF>::new(&params, n_vars);
            let folding_pow_bits = std::iter::once(params.starting_folding_pow_bits)
                .chain(params.round_parameters.iter().map(|r| r.folding_pow_bits))
                .collect::<Vec<_>>();
            let query_pow_bits = params
                .round_parameters
                .iter()
                .map(|r| r.query_pow_bits)
                .chain(std::iter::once(params.final_query_pow_bits))
                .collect::<Vec<_>>();
            println!(
                "n_vars: {}, log_inv_rate: {}, num_queries: {:?}, folding_pow_bits: {:?}, query_pow_bits: {:?}",
                n_vars,
                log_inv_rate,
                params
                    .round_parameters
                    .iter()
                    .map(|r| r.num_queries)
                    .collect::<Vec<_>>(),
                folding_pow_bits,
                query_pow_bits,
            );
        }
    }
}

/// h-wf T1: the lazy-once fused combine+round-0 path must produce BYTE-IDENTICAL
/// proofs to the legacy combine_statement path, across statement shapes covering
/// every lazy term arm (dual full fast-path via OOD, dense multi-selector blocks,
/// single-value blocks, lane-level overlay, is_next inner polys).
#[test]
fn test_lazy_combine_proof_equality() {
    fn set_lazy(v: &str) {
        unsafe { std::env::set_var("WHIR_LAZY_COMBINE", v) }
    }
    let poseidon16 = default_koalabear_poseidon1_16();
    precompute_dft_twiddles::<F>(1 << F::TWO_ADICITY);

    // n_vars 26 = the production stacked-PCS size; 18/22 cover small/mid shapes.
    for (seed, num_variables) in [(1u64, 18usize), (7, 22), (3, 26)] {
        // pow_grinding is a racy parallel nonce search (first valid witness wins),
        // so proof bytes are only reproducible when every grinding step is 0 bits.
        // The lazy combine path never touches grinding; zero-grinding configs make
        // the byte-equality check exact over all deterministic protocol parts.
        let params = WhirConfigBuilder {
            security_level: 40,
            max_num_variables_to_send_coeffs: 9,
            pow_bits: 0,
            folding_factor: FoldingFactor::new(7, 4),
            soundness_type: SecurityAssumption::JohnsonBound,
            starting_log_inv_rate: 1,
            rs_domain_initial_reduction_factor: 5,
        };
        let params = WhirConfig::new(&params, num_variables);
        assert_eq!(params.starting_folding_pow_bits, 0, "test needs zero grinding");
        assert_eq!(params.final_query_pow_bits, 0, "test needs zero grinding");
        for r in &params.round_parameters {
            assert_eq!(r.folding_pow_bits, 0, "test needs zero grinding");
            assert_eq!(r.query_pow_bits, 0, "test needs zero grinding");
        }
        let mut rng = StdRng::seed_from_u64(seed);
        let polynomial = (0..1usize << num_variables).map(|_| rng.random::<F>()).collect::<Vec<F>>();

        let mut statement: Vec<SparseStatement<EF>> = Vec::new();
        // full statement (selector 0, full-length point): with this config the
        // prover splices exactly ONE OOD full statement, so adding one of our own
        // makes the layout [OOD-full, this-full, ...] and engages the dual
        // fast-path arm (start_idx = 2) in both combine paths.
        {
            let point = MultilinearPoint((0..num_variables).map(|_| rng.random::<EF>()).collect::<Vec<EF>>());
            let value = polynomial.evaluate_sparse(0, &point);
            statement.push(SparseStatement::new(
                num_variables,
                point,
                vec![SparseValue { selector: 0, value }],
            ));
        }
        // dense multi-selector blocks (table-shaped)
        for (selector_len, n_sels) in [(6usize, 5usize), (8, 9), (11, 3)] {
            let point = MultilinearPoint((0..num_variables - selector_len).map(|_| rng.random::<EF>()).collect::<Vec<EF>>());
            let first = rng.random_range(0..(1usize << selector_len) - n_sels);
            statement.push(SparseStatement::new(
                num_variables,
                point.clone(),
                (0..n_sels)
                    .map(|k| SparseValue {
                        selector: first + k,
                        value: polynomial.evaluate_sparse(first + k, &point),
                    })
                    .collect(),
            ));
        }
        // single-value block (bytecode_acc-shaped)
        {
            let point = MultilinearPoint((0..num_variables - 5).map(|_| rng.random::<EF>()).collect::<Vec<EF>>());
            let sel = rng.random_range(0..32);
            statement.push(SparseStatement::new(
                num_variables,
                point.clone(),
                vec![SparseValue {
                    selector: sel,
                    value: polynomial.evaluate_sparse(sel, &point),
                }],
            ));
        }
        // lane-level: single cells (pc-shaped, inner 0) and inner 1
        for inner in [0usize, 1] {
            let point = MultilinearPoint((0..inner).map(|_| rng.random::<EF>()).collect::<Vec<EF>>());
            let sel = rng.random_range(0..(1usize << (num_variables - inner)));
            statement.push(SparseStatement::new(
                num_variables,
                point.clone(),
                vec![SparseValue {
                    selector: sel,
                    value: polynomial.evaluate_sparse(sel, &point),
                }],
            ));
        }
        // is_next statement (shift-column-shaped), 2 selectors, value = <next_mle(point,.), poly_block>
        {
            let inner = 10usize;
            let point = MultilinearPoint((0..inner).map(|_| rng.random::<EF>()).collect::<Vec<EF>>());
            let next_table = matrix_next_mle_folded(&point.0);
            let mut s = SparseStatement::new(
                num_variables,
                point.clone(),
                (0..2usize)
                    .map(|k| {
                        let sel = 3 + k;
                        let base = sel << inner;
                        let value = (0..1usize << inner)
                            .map(|i| next_table[i] * polynomial[base + i])
                            .sum::<EF>();
                        SparseValue { selector: sel, value }
                    })
                    .collect(),
            );
            s.is_next = true;
            statement.push(s);
        }

        let prove_once = |lazy: bool, delayed: bool| {
            set_lazy(if lazy { "1" } else { "0" });
            unsafe { std::env::set_var("WHIR_DELAYED_EF", if delayed { "1" } else { "0" }) }
            let mut prover_state = ProverState::new(poseidon16.clone(), Default::default());
            let poly_mle: MleOwned<EF> = MleOwned::Base(ArenaVec::from_iter(polynomial.clone()));
            let witness = params.commit(&mut prover_state, &poly_mle, 1 << num_variables);
            params.prove(&mut prover_state, statement.clone(), witness, &poly_mle.by_ref());
            prover_state.into_proof()
        };

        let proof_legacy = prove_once(false, false);
        let proof_lazy = prove_once(true, false);
        assert_eq!(
            proof_legacy, proof_lazy,
            "lazy combine produced a different proof (seed {seed}, n {num_variables})"
        );
        let proof_delayed = prove_once(true, true);
        assert_eq!(
            proof_legacy, proof_delayed,
            "delayed-EF produced a different proof (seed {seed}, n {num_variables})"
        );

        let mut verifier_state = VerifierState::<EF, _>::new(proof_delayed, poseidon16.clone(), Default::default()).unwrap();
        let parsed_commitment = params.parse_commitment::<F>(&mut verifier_state).unwrap();
        params
            .verify::<F>(&mut verifier_state, &parsed_commitment, statement.clone())
            .unwrap();
    }
    set_lazy("1");
    unsafe { std::env::set_var("WHIR_DELAYED_EF", "1") }
}
