//! Ignored-test microbench for the product-sumcheck quadratic round kernel
//! ([`compute_product_sumcheck_polynomial`] over base-packed evals x extension-packed
//! weights, i.e. the [`sumcheck_quadratic`] hot loop).
//!
//! Part of the delayed modular reduction work tracked in
//! https://github.com/leanEthereum/leanVM/issues/260. The bench first asserts the kernel
//! output against a scalar reference computation, so the harness doubles as a regression
//! test when the kernel is rewritten.

use std::hint::black_box;
use std::time::Instant;

use field::{PackedValue, PrimeCharacteristicRing};
use koala_bear::{KoalaBear, QuinticExtensionFieldKB};
use poly::*;
use rand::rngs::StdRng;
use rand::{RngExt, SeedableRng};

use crate::compute_product_sumcheck_polynomial;

type F = KoalaBear;
type EF = QuinticExtensionFieldKB;

#[test]
#[ignore]
fn bench_product_sumcheck_quadratic_round() {
    // cargo test --release --package sumcheck --lib -- benchmark_product_sumcheck::bench_product_sumcheck_quadratic_round --exact --nocapture --ignored

    let n_vars = 20;
    let n = 1usize << n_vars;
    let mut rng = StdRng::seed_from_u64(0);
    let evals: Vec<F> = (0..n).map(|_| rng.random()).collect();
    let weights: Vec<EF> = (0..n).map(|_| rng.random()).collect();

    let evals_packed: &[PFPacking<EF>] = PFPacking::<EF>::pack_slice(&evals);
    let weights_packed: Vec<EFPacking<EF>> = pack_extension(&weights);

    // Scalar reference for the claimed sum and the two computed coefficients.
    let half = n / 2;
    let sum = weights.iter().zip(&evals).map(|(&w, &e)| w * e).sum::<EF>();
    let c0_ref = (0..half).map(|i| weights[i] * evals[i]).sum::<EF>();
    let c2_ref = (0..half)
        .map(|i| (weights[half + i] - weights[i]) * (evals[half + i] - evals[i]))
        .sum::<EF>();
    let c1_ref = sum - c0_ref.double() - c2_ref;

    let compute = || {
        compute_product_sumcheck_polynomial(evals_packed, &weights_packed, sum, |e| {
            unpack_extension::<EF, Vec<EF>>(&[e])
        })
    };
    assert_eq!(compute().coeffs, vec![c0_ref, c1_ref, c2_ref]);

    // warming
    for _ in 0..3 {
        black_box(compute());
    }

    let n_iters = 30;
    let time = Instant::now();
    for _ in 0..n_iters {
        black_box(compute());
    }
    let elapsed = time.elapsed();
    println!(
        "product sumcheck quadratic round ({} vars): {:.3} ms/call, {:.0} Melems/s",
        n_vars,
        elapsed.as_secs_f64() * 1e3 / n_iters as f64,
        (n_iters * n) as f64 / elapsed.as_secs_f64() / 1e6
    );
}
