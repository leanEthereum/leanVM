//! Ignored-test microbench for the WHIR round-0 combine kernel
//! ([`combine_and_compute_first_round`]): one pass writing the rounds-1+ weight buffer
//! while accumulating the round-0 quadratic.
//!
//! Part of the delayed modular reduction work tracked in
//! https://github.com/leanEthereum/leanVM/issues/260. The bench first asserts the kernel
//! output against a scalar reference computation, so the harness doubles as a regression
//! test when the kernel is rewritten.

use std::hint::black_box;
use std::time::Instant;

use field::{PackedValue, PrimeCharacteristicRing};
use koala_bear::{KoalaBear, QuinticExtensionFieldKB};
use rand::rngs::StdRng;
use rand::{RngExt, SeedableRng};

use poly::{EvaluationsList, MultilinearPoint, PFPacking, eval_eq_scaled, unpack_extension};

use crate::SparseStatement;
use crate::open::{build_lazy_combine_terms, combine_and_compute_first_round};

type F = KoalaBear;
type EF = QuinticExtensionFieldKB;

#[test]
#[ignore]
fn bench_combine_and_compute_first_round() {
    // cargo test --release --package whir --lib -- benchmark_first_round::bench_combine_and_compute_first_round --exact --nocapture --ignored

    let n_vars = 20;
    let n = 1usize << n_vars;
    let n_statements = 4;
    let mut rng = StdRng::seed_from_u64(0);
    let evals: Vec<F> = (0..n).map(|_| rng.random()).collect();
    let evals_packed: &[PFPacking<EF>] = PFPacking::<EF>::pack_slice(&evals);
    let gamma: EF = rng.random();

    // Dense equality statements, the hot path of the round-0 combine.
    let statements: Vec<SparseStatement<EF>> = (0..n_statements)
        .map(|_| {
            let point = MultilinearPoint((0..n_vars).map(|_| rng.random()).collect::<Vec<EF>>());
            let value = evals.evaluate(&point);
            SparseStatement::dense(point, value)
        })
        .collect();
    let terms = build_lazy_combine_terms::<EF>(&statements, gamma);

    // Scalar reference: materialized weights, combined sum, and round-0 coefficients.
    let mut w_ref = vec![EF::ZERO; n];
    let mut combined_sum_ref = EF::ZERO;
    let mut gamma_pow = EF::ONE;
    for statement in &statements {
        let eq = eval_eq_scaled(&statement.point.0, gamma_pow);
        for (w, e) in w_ref.iter_mut().zip(eq.iter()) {
            *w += *e;
        }
        combined_sum_ref += statement.values[0].value * gamma_pow;
        gamma_pow *= gamma;
    }
    assert_eq!(terms.combined_sum, combined_sum_ref);
    let half = n / 2;
    let c0_ref = (0..half).map(|i| w_ref[i] * evals[i]).sum::<EF>();
    let c2_ref = (0..half)
        .map(|i| (w_ref[half + i] - w_ref[i]) * (evals[half + i] - evals[i]))
        .sum::<EF>();
    let c1_ref = combined_sum_ref - c0_ref.double() - c2_ref;

    let (first_poly, weights_buf) = combine_and_compute_first_round(evals_packed, &terms);
    assert_eq!(first_poly.coeffs, vec![c0_ref, c1_ref, c2_ref]);
    let weights_unpacked: Vec<EF> = unpack_extension(&weights_buf);
    assert_eq!(weights_unpacked, w_ref);

    // warming
    for _ in 0..2 {
        black_box(combine_and_compute_first_round(evals_packed, &terms));
    }

    let n_iters = 10;
    let time = Instant::now();
    for _ in 0..n_iters {
        black_box(combine_and_compute_first_round(evals_packed, &terms));
    }
    let elapsed = time.elapsed();
    println!(
        "WHIR round-0 combine ({} vars, {} statements): {:.3} ms/call, {:.0} Melems/s",
        n_vars,
        n_statements,
        elapsed.as_secs_f64() * 1e3 / n_iters as f64,
        (n_iters * n) as f64 / elapsed.as_secs_f64() / 1e6
    );
}
