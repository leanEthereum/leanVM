//! Single-thread cost of every field kernel, in nanoseconds per operation.
//!
//! `cargo test --release -p primitives --test field_bench -- --ignored --nocapture`

use std::hint::black_box;
use std::time::Instant;

use primitives::field::{F64, F192, F192Unreduced, mul_unreduced4, mul2, mul4};
use primitives::test_rng::Rng;

/// Operands per pass: 1024 extension elements are 24 KiB, so every pass runs from L1.
const N: usize = 1 << 10;

/// Timed passes per kernel; the fastest one is reported.
const PASSES: usize = 200;

/// The fastest of `PASSES` runs of `pass`, divided by the `ops` it performs.
///
/// The minimum filters out interrupts and frequency ramps, which only ever add time.
fn ns_per_op(ops: usize, mut pass: impl FnMut()) -> f64 {
    // Warm the caches and the branch predictor before timing.
    for _ in 0..PASSES / 10 {
        pass();
    }
    (0..PASSES)
        .map(|_| {
            let start = Instant::now();
            pass();
            start.elapsed().as_secs_f64() * 1e9 / ops as f64
        })
        .fold(f64::INFINITY, f64::min)
}

fn report(kernel: &str, ns: f64) {
    println!("{kernel:<40} {ns:>8.3} ns");
}

#[test]
#[ignore = "manual measurement"]
fn field_arithmetic() {
    // Independent random operands, so no pass can be constant-folded.
    let mut rng = Rng::new(0);
    let (k, l): (Vec<F64>, Vec<F64>) = (0..N).map(|_| (F64(rng.next_u64()), F64(rng.next_u64()))).unzip();
    let (a, b) = (rng.ext_vec(N), rng.ext_vec(N));
    let r = rng.ext();
    let mut out_k = vec![F64::ZERO; N];
    let mut out = vec![F192::ZERO; N];

    // Base field.
    //
    //     throughput: N independent products per pass
    //     latency:    one chain of N dependent products
    report(
        "F64 mul, throughput",
        ns_per_op(N, || {
            for ((o, &x), &y) in out_k.iter_mut().zip(black_box(&k)).zip(black_box(&l)) {
                *o = x * y;
            }
            black_box(&mut out_k);
        }),
    );
    report(
        "F64 mul, latency",
        ns_per_op(N, || {
            let x = black_box(&l).iter().fold(black_box(k[0]), |x, &y| x * y);
            black_box(x);
        }),
    );
    report(
        "F64 square, latency",
        ns_per_op(N, || {
            let x = (0..N).fold(black_box(k[0]), |x, _| x.square());
            black_box(x);
        }),
    );
    report(
        "F64 inv",
        ns_per_op(N / 16, || {
            for &x in &black_box(&k)[..N / 16] {
                black_box(x.inv());
            }
        }),
    );

    // Extension field, one product at a time.
    report(
        "F192 mul, throughput",
        ns_per_op(N, || {
            for ((o, &x), &y) in out.iter_mut().zip(black_box(&a)).zip(black_box(&b)) {
                *o = x * y;
            }
            black_box(&mut out);
        }),
    );
    report(
        "F192 mul, latency",
        ns_per_op(N, || {
            let x = black_box(&b).iter().fold(black_box(a[0]), |x, &y| x * y);
            black_box(x);
        }),
    );
    // The sumcheck fold `lo + r * (hi - lo)`, which is `lo + r * (hi + lo)` in characteristic 2.
    report(
        "F192 fold lo + r(hi + lo)",
        ns_per_op(N, || {
            let r = black_box(r);
            for ((o, &lo), &hi) in out.iter_mut().zip(black_box(&a)).zip(black_box(&b)) {
                *o = lo + r * (hi + lo);
            }
            black_box(&mut out);
        }),
    );
    report(
        "F192 square, throughput",
        ns_per_op(N, || {
            for (o, &x) in out.iter_mut().zip(black_box(&a)) {
                *o = x.square();
            }
            black_box(&mut out);
        }),
    );
    report(
        "F192 mul_base, throughput",
        ns_per_op(N, || {
            for ((o, &x), &y) in out.iter_mut().zip(black_box(&a)).zip(black_box(&k)) {
                *o = x.mul_base(y);
            }
            black_box(&mut out);
        }),
    );
    report(
        "F192 inv",
        ns_per_op(N / 16, || {
            for &x in &black_box(&a)[..N / 16] {
                black_box(x.inv());
            }
        }),
    );

    // Batched products, reported per product.
    report(
        "mul2, per product",
        ns_per_op(N, || {
            let (out, _) = out.as_chunks_mut::<2>();
            let (x, _) = black_box(&a).as_chunks::<2>();
            let (y, _) = black_box(&b).as_chunks::<2>();
            for ((o, &x), &y) in out.iter_mut().zip(x).zip(y) {
                *o = mul2(x, y);
            }
            black_box(&mut *out);
        }),
    );
    report(
        "mul4, per product",
        ns_per_op(N, || {
            let (out, _) = out.as_chunks_mut::<4>();
            let (x, _) = black_box(&a).as_chunks::<4>();
            let (y, _) = black_box(&b).as_chunks::<4>();
            for ((o, &x), &y) in out.iter_mut().zip(x).zip(y) {
                *o = mul4(x, y);
            }
            black_box(&mut *out);
        }),
    );

    // Inner products: accumulate unreduced, reduce once per pass.
    report(
        "inner product, mul_unreduced",
        ns_per_op(N, || {
            let acc = black_box(&a)
                .iter()
                .zip(black_box(&b))
                .fold(F192Unreduced::ZERO, |acc, (&x, &y)| acc ^ x.mul_unreduced(y));
            black_box(acc.reduce());
        }),
    );
    report(
        "inner product, mul_unreduced4",
        ns_per_op(N, || {
            let (x, _) = black_box(&a).as_chunks::<4>();
            let (y, _) = black_box(&b).as_chunks::<4>();
            // Four independent accumulators, one per lane, merged at the end.
            let mut acc = [F192Unreduced::ZERO; 4];
            for (&x, &y) in x.iter().zip(y) {
                for (acc, p) in acc.iter_mut().zip(mul_unreduced4(x, y)) {
                    *acc ^= p;
                }
            }
            black_box(acc.into_iter().fold(F192Unreduced::ZERO, |s, x| s ^ x).reduce());
        }),
    );
    report(
        "mixed inner product, mul_base_unreduced",
        ns_per_op(N, || {
            let acc = black_box(&a)
                .iter()
                .zip(black_box(&k))
                .fold(F192Unreduced::ZERO, |acc, (&x, &y)| acc ^ x.mul_base_unreduced(y));
            black_box(acc.reduce());
        }),
    );
}
