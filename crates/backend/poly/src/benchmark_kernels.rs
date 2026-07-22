//! Ignored-test microbenches for hot mixed base x extension kernels of this crate:
//! [`eval_base_packed`] and [`finger_print_packed`].
//!
//! Part of the delayed modular reduction work tracked in
//! https://github.com/leanEthereum/leanVM/issues/260. Each bench first asserts the kernel
//! output against an independent reference computation, so the harness doubles as a
//! regression test when the kernels are rewritten.

use std::hint::black_box;
use std::time::Instant;

use field::{PackedValue, PrimeCharacteristicRing};
use koala_bear::{KoalaBear, QuinticExtensionFieldKB};
use rand::rngs::StdRng;
use rand::{RngExt, SeedableRng};

use crate::*;

type F = KoalaBear;
type EF = QuinticExtensionFieldKB;

#[test]
#[ignore]
fn bench_eval_base_packed() {
    // cargo test --release --package poly --lib -- benchmark_kernels::bench_eval_base_packed --exact --nocapture --ignored

    let n_vars = 22;
    let mut rng = StdRng::seed_from_u64(0);
    let evals: Vec<F> = (0..1usize << n_vars).map(|_| rng.random()).collect();
    let point: Vec<EF> = (0..n_vars).map(|_| rng.random()).collect();

    // Reference: the recursive strategy is an independent code path.
    let expected = evals.evaluate_sequential(&MultilinearPoint(point.clone()));
    assert_eq!(eval_base_packed::<EF, true>(&evals, &point), expected);

    // warming
    for _ in 0..3 {
        let _ = black_box(eval_base_packed::<EF, true>(&evals, &point));
    }

    let n_iters = 30;
    let time = Instant::now();
    let mut acc = EF::ZERO;
    for _ in 0..n_iters {
        acc += eval_base_packed::<EF, true>(&evals, &point);
    }
    let elapsed = time.elapsed();
    let _ = black_box(acc);
    println!(
        "eval_base_packed ({} vars): {:.3} ms/call, {:.0} Melems/s",
        n_vars,
        elapsed.as_secs_f64() * 1e3 / n_iters as f64,
        (n_iters as u64 * (1u64 << n_vars)) as f64 / elapsed.as_secs_f64() / 1e6
    );
}

#[test]
#[ignore]
fn bench_finger_print_packed() {
    // cargo test --release --package poly --lib -- benchmark_kernels::bench_finger_print_packed --exact --nocapture --ignored

    let mut rng = StdRng::seed_from_u64(0);
    // Memory-style tuples (address, value) and bytecode-style tuples (12 instruction
    // columns + index), the narrowest and widest logup uses.
    run_finger_print_packed::<2>("memory-style", &mut rng);
    run_finger_print_packed::<13>("bytecode-style", &mut rng);
}

fn run_finger_print_packed<const N_DATA: usize>(label: &str, rng: &mut StdRng) {
    const N_ALPHAS: usize = 16;
    assert!(N_ALPHAS > N_DATA);
    let n_rows = 1usize << 17; // packed rows
    let width = packing_width::<EF>();

    let alphas: Vec<EF> = (0..N_ALPHAS).map(|_| rng.random()).collect();
    let alphas_packed: Vec<EFPacking<EF>> = alphas.iter().map(|a| EFPacking::<EF>::from(*a)).collect();
    let domainsep: F = rng.random();
    let domainsep_packed = PFPacking::<EF>::from(domainsep);
    let rows: Vec<[PFPacking<EF>; N_DATA]> = (0..n_rows)
        .map(|_| core::array::from_fn(|_| PFPacking::<EF>::from_fn(|_| rng.random())))
        .collect();

    // Reference: scalar finger_print on every lane; the packed kernel must match in total.
    let mut total_ref = EF::ZERO;
    for row in &rows {
        for lane in 0..width {
            let data: Vec<EF> = row.iter().map(|d| EF::from(d.as_slice()[lane])).collect();
            total_ref += finger_print(EF::from(domainsep), &data, &alphas);
        }
    }
    let total = rows.iter().fold(EFPacking::<EF>::ZERO, |acc, row| {
        acc + finger_print_packed::<EF>(domainsep_packed, row, &alphas_packed)
    });
    assert_eq!(
        unpack_extension::<EF, Vec<EF>>(&[total]).iter().copied().sum::<EF>(),
        total_ref
    );

    // warming
    let mut acc = EFPacking::<EF>::ZERO;
    for row in &rows {
        acc += finger_print_packed::<EF>(domainsep_packed, row, &alphas_packed);
    }

    let n_passes = 20;
    let time = Instant::now();
    for _ in 0..n_passes {
        for row in &rows {
            acc += finger_print_packed::<EF>(domainsep_packed, row, &alphas_packed);
        }
    }
    let elapsed = time.elapsed();
    let _ = black_box(acc);
    let calls = (n_passes * n_rows) as f64;
    println!(
        "finger_print_packed ({label}, {N_DATA} data, {N_ALPHAS} alphas): {:.1} ns/call, {:.0}M scalar rows/s",
        elapsed.as_secs_f64() * 1e9 / calls,
        calls * width as f64 / elapsed.as_secs_f64() / 1e6
    );
}
