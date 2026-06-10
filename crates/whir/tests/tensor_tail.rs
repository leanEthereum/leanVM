//! T4 (pw13 h1): tensor-tail SparseStatements — weight = eq(point) ⊗ MLE(tail)
//! on the lowest log2(tail.len()) inner variables (next variant: shift-by-one).

use fiat_shamir::{ProverState, VerifierState};
use field::{PrimeCharacteristicRing, TwoAdicField};
use koala_bear::{KoalaBear, QuinticExtensionFieldKB, default_koalabear_poseidon1_16};
use poly::*;
use rand::{RngExt, SeedableRng, rngs::StdRng};
use whir::*;
use zk_alloc::ArenaVec;

type F = KoalaBear;
type EF = QuinticExtensionFieldKB;

const NUM_VARIABLES: usize = 18;

fn whir_config() -> WhirConfig<EF> {
    let params = WhirConfigBuilder {
        security_level: 124,
        max_num_variables_to_send_coeffs: 9,
        pow_bits: 16,
        folding_factor: FoldingFactor::new(7, 4),
        soundness_type: SecurityAssumption::JohnsonBound,
        starting_log_inv_rate: 2,
        rs_domain_initial_reduction_factor: 5,
    };
    WhirConfig::new(&params, NUM_VARIABLES)
}

fn random_poly(seed: u64) -> Vec<F> {
    let mut rng = StdRng::seed_from_u64(seed);
    (0..1 << NUM_VARIABLES).map(|_| rng.random::<F>()).collect()
}

/// Full commit+open+verify roundtrip; returns Ok(()) iff the verifier accepts
/// `verify_statements` against a proof generated for `prove_statements`.
fn roundtrip(
    polynomial: &[F],
    prove_statements: Vec<SparseStatement<EF>>,
    verify_statements: Vec<SparseStatement<EF>>,
) -> Result<(), fiat_shamir::ProofError> {
    let poseidon16 = default_koalabear_poseidon1_16();
    let params = whir_config();
    precompute_dft_twiddles::<F>(1 << F::TWO_ADICITY);

    let mut prover_state = ProverState::new(poseidon16.clone(), Default::default());
    let mle: MleOwned<EF> = MleOwned::Base(ArenaVec::from_iter(polynomial.to_vec()));
    let witness = params.commit(&mut prover_state, &mle, 1 << NUM_VARIABLES);
    params.prove(&mut prover_state, prove_statements, witness, &mle.by_ref());

    let mut verifier_state =
        VerifierState::<EF, _>::new(prover_state.into_proof(), poseidon16, Default::default()).unwrap();
    let parsed_commitment = params.parse_commitment::<F>(&mut verifier_state)?;
    params
        .verify::<F>(&mut verifier_state, &parsed_commitment, verify_statements)
        .map(|_| ())
}

/// Naive reference: Σ_{hi,lo} eq(point)[hi]·tail[lo]·f[(selector << inner) | (hi << k) | lo].
fn naive_tailed_value(polynomial: &[F], selector: usize, point: &[EF], tail: &[EF]) -> EF {
    let k = tail.len().trailing_zeros() as usize;
    let inner = point.len() + k;
    let chunk = &polynomial[selector << inner..][..1 << inner];
    let eq = eval_eq(point);
    let mut sum = EF::ZERO;
    for (hi, &w_hi) in eq.iter().enumerate() {
        for (lo, &w_lo) in tail.iter().enumerate() {
            sum += w_hi * w_lo * chunk[(hi << k) | lo];
        }
    }
    sum
}

#[test]
fn test_tail_equivalent_to_point_append() {
    let polynomial = random_poly(1);
    let mut rng = StdRng::seed_from_u64(2);
    let p: Vec<EF> = (0..12).map(|_| rng.random()).collect();
    let c: Vec<EF> = (0..4).map(|_| rng.random()).collect();
    let selector = 3usize; // 2 selector variables
    let appended = MultilinearPoint([p.clone(), c.clone()].concat());
    let value = polynomial.evaluate_sparse(selector, &appended);

    let tail: Vec<EF> = eval_eq(&c).to_vec();
    assert_eq!(
        naive_tailed_value(&polynomial, selector, &p, &tail),
        value,
        "naive reference disagrees with evaluate_sparse"
    );

    let plain = SparseStatement::new(NUM_VARIABLES, appended, vec![SparseValue::new(selector, value)]);
    let tailed = SparseStatement::new_with_tail(
        NUM_VARIABLES,
        MultilinearPoint(p),
        tail,
        vec![SparseValue::new(selector, value)],
    );
    assert_eq!(plain.inner_num_variables(), tailed.inner_num_variables());
    assert_eq!(plain.selector_num_variables(), tailed.selector_num_variables());

    let statements = vec![plain, tailed];
    roundtrip(&polynomial, statements.clone(), statements).expect("equivalence roundtrip must accept");
}

#[test]
fn test_random_tail_cube_sum() {
    let polynomial = random_poly(3);
    let mut rng = StdRng::seed_from_u64(4);
    let p: Vec<EF> = (0..13).map(|_| rng.random()).collect();
    let tail: Vec<EF> = (0..8).map(|_| rng.random()).collect(); // k = 3, NOT an eq expansion
    let selector = 2usize; // 2 selector variables
    let value = naive_tailed_value(&polynomial, selector, &p, &tail);

    let make = |v: EF| {
        vec![SparseStatement::new_with_tail(
            NUM_VARIABLES,
            MultilinearPoint(p.clone()),
            tail.clone(),
            vec![SparseValue::new(selector, v)],
        )]
    };
    roundtrip(&polynomial, make(value), make(value)).expect("random-tail roundtrip must accept");
    assert!(
        roundtrip(&polynomial, make(value), make(value + EF::ONE)).is_err(),
        "corrupted tailed value must be rejected"
    );
}

#[test]
fn test_next_tail_equivalent_to_point_append() {
    let polynomial = random_poly(5);
    let mut rng = StdRng::seed_from_u64(6);
    let p: Vec<EF> = (0..12).map(|_| rng.random()).collect();
    let c: Vec<EF> = (0..4).map(|_| rng.random()).collect();
    let selector = 1usize; // 2 selector variables
    let appended = [p.clone(), c.clone()].concat();
    let inner = appended.len();

    // Reference: dot(matrix_next_mle_folded(point), chunk).
    let chunk = &polynomial[selector << inner..][..1 << inner];
    let weights = matrix_next_mle_folded(&appended);
    let value: EF = weights.iter().zip(chunk).map(|(&w, &f)| w * f).sum();

    // T1 identity cross-check on the tailed weights.
    let tail: Vec<EF> = eval_eq(&c).to_vec();
    let tailed_weights = matrix_next_mle_folded_with_tail(&p, &tail);
    let tailed_value: EF = tailed_weights.iter().zip(chunk).map(|(&w, &f)| w * f).sum();
    assert_eq!(tailed_value, value, "next-with-tail weights disagree with point-append");

    let plain = SparseStatement::new_next(
        NUM_VARIABLES,
        MultilinearPoint(appended),
        vec![SparseValue::new(selector, value)],
    );
    let tailed = SparseStatement::new_next_with_tail(
        NUM_VARIABLES,
        MultilinearPoint(p),
        tail,
        vec![SparseValue::new(selector, value)],
    );
    let statements = vec![plain, tailed];
    roundtrip(&polynomial, statements.clone(), statements).expect("next equivalence roundtrip must accept");
}

#[test]
fn test_tailed_mixed_with_ordinary_statements() {
    let polynomial = random_poly(7);
    let mut rng = StdRng::seed_from_u64(8);

    // Dense full-width statement (exercises the is_full fast path alongside tails).
    let full_point: Vec<EF> = (0..NUM_VARIABLES).map(|_| rng.random()).collect();
    let dense = SparseStatement::dense(
        MultilinearPoint(full_point.clone()),
        polynomial.evaluate(&MultilinearPoint(full_point)),
    );

    // Plain sparse statement.
    let sp: Vec<EF> = (0..15).map(|_| rng.random()).collect();
    let plain = SparseStatement::new(
        NUM_VARIABLES,
        MultilinearPoint(sp.clone()),
        vec![SparseValue::new(
            5,
            polynomial.evaluate_sparse(5, &MultilinearPoint(sp)),
        )],
    );

    // Tailed eq statement (k = 4).
    let p1: Vec<EF> = (0..10).map(|_| rng.random()).collect();
    let t1: Vec<EF> = (0..16).map(|_| rng.random()).collect();
    let tailed_eq = SparseStatement::new_with_tail(
        NUM_VARIABLES,
        MultilinearPoint(p1.clone()),
        t1.clone(),
        vec![SparseValue::new(2, naive_tailed_value(&polynomial, 2, &p1, &t1))],
    );

    // Tailed next statement (k = 3).
    let p2: Vec<EF> = (0..13).map(|_| rng.random()).collect();
    let t2: Vec<EF> = (0..8).map(|_| rng.random()).collect();
    let w2 = matrix_next_mle_folded_with_tail(&p2, &t2);
    let chunk2 = &polynomial[1 << 16..][..1 << 16];
    let v2: EF = w2.iter().zip(chunk2).map(|(&w, &f)| w * f).sum();
    let tailed_next = SparseStatement::new_next_with_tail(
        NUM_VARIABLES,
        MultilinearPoint(p2),
        t2,
        vec![SparseValue::new(1, v2)],
    );

    let statements = vec![dense, plain, tailed_eq, tailed_next];
    roundtrip(&polynomial, statements.clone(), statements).expect("mixed roundtrip must accept");
}
