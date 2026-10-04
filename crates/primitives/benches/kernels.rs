//! The field and bit kernels the prover leans on, each timed alone on one thread: the `F64` and
//! `F192` products, squares and inverses, and the bit transposes. A throughput kernel sweeps
//! independent operands held in L1; a latency kernel (`-latency`) feeds each result into the next
//! call. One operation is one call: a `mul4` is four products, a transpose one block. The passes
//! follow [`bench::Plan::from_env`] (`BENCH_REPEAT`, `BENCH_COOLDOWN`).
//!
//! ```text
//! BENCH_REPEAT=5 cargo bench -p primitives --bench kernels
//! ```
//!
//! With `-- --json` it prints, in place of the report, each kernel's time per operation as
//! Bencher Metric Format JSON (measure `per-op`), for CI.
//!
//! ```text
//! cargo bench -p primitives --bench kernels -- --json
//! ```

use std::hint::black_box;

use bench::{Metric, Plan, Timing, bencher_json};
use primitives::bits::{bit_transpose_64bytes, transpose_64x64};
use primitives::field::{F64, F192, mul4};
use primitives::test_util::Rng;

/// Operands per array, few enough that a sweep's inputs and outputs stay in L1.
const N: usize = 256;

fn main() {
    let plan = Plan::from_env();
    let mut rng = Rng::new(0x006B_6572_6E65_6C73);
    let k: Vec<F64> = (0..2 * N).map(|_| F64(rng.next_u64())).collect();
    let e: Vec<F192> = rng.ext_vec(2 * N);
    let (ka, kb) = k.split_at(N);
    let (ea, eb) = e.split_at(N);
    let (ea4, eb4) = (ea.as_chunks::<4>().0, eb.as_chunks::<4>().0);
    let bytes: Vec<[u8; 64]> = (0..N).map(|_| std::array::from_fn(|_| rng.next_u8())).collect();
    let mut words: Vec<[u64; 64]> = (0..N / 4).map(|_| std::array::from_fn(|_| rng.next_u64())).collect();
    let mut k_out = vec![F64::ZERO; N];
    let mut e_out = vec![F192::ZERO; N];
    let mut e4_out = vec![[F192::ZERO; 4]; N / 4];
    let mut bytes_out = vec![[0u8; 64]; N];

    let rows = [
        (
            "f64-mul",
            time(plan, 1 << 25, |ops| sweep2(ka, kb, &mut k_out, ops, |x, y| x * y)),
        ),
        (
            "f64-square",
            time(plan, 1 << 25, |ops| sweep(ka, &mut k_out, ops, F64::square)),
        ),
        (
            "f64-inv",
            time(plan, 1 << 18, |ops| sweep(ka, &mut k_out, ops, F64::inv)),
        ),
        (
            "f192-mul-throughput",
            time(plan, 1 << 23, |ops| sweep2(ea, eb, &mut e_out, ops, |x, y| x * y)),
        ),
        (
            "f192-mul-latency",
            time(plan, 1 << 23, |ops| chain(ea[0], eb[0], ops, |x, y| x * y)),
        ),
        (
            "f192-mul4-throughput",
            time(plan, 1 << 22, |ops| sweep2(ea4, eb4, &mut e4_out, ops, mul4)),
        ),
        (
            "f192-mul4-latency",
            time(plan, 1 << 22, |ops| chain(ea4[0], eb4[0], ops, mul4)),
        ),
        (
            "f192-square",
            time(plan, 1 << 23, |ops| sweep(ea, &mut e_out, ops, F192::square)),
        ),
        (
            "f192-inv",
            time(plan, 1 << 18, |ops| sweep(ea, &mut e_out, ops, F192::inv)),
        ),
        (
            "transpose-64bytes",
            time(plan, 1 << 25, |ops| {
                for _ in 0..ops / N {
                    for (i, o) in black_box(&bytes).iter().zip(&mut bytes_out) {
                        bit_transpose_64bytes(i, o);
                    }
                    black_box(&mut bytes_out);
                }
            }),
        ),
        (
            "transpose-64x64",
            time(plan, 1 << 20, |ops| {
                for _ in 0..ops / words.len() {
                    black_box(&mut words).iter_mut().for_each(transpose_64x64);
                }
            }),
        ),
    ];

    if std::env::args().any(|arg| arg == "--json") {
        let report =
            rows.map(|(name, (ops, t))| (name.to_string(), vec![("per-op", Metric::nanoseconds_per_op(&t, ops))]));
        println!("{}", bencher_json(&report));
        return;
    }
    println!("\nKernels, one thread, time per call");
    for (name, (ops, t)) in &rows {
        println!("  {name:<22}: {:>10.3} ns{}", t.mean() * 1e9 / *ops as f64, t.spread());
    }
}

/// A warmup and the plan's measured passes of `kernel`, each doing `ops` operations.
fn time(plan: Plan, ops: usize, mut kernel: impl FnMut(usize)) -> (usize, Timing) {
    (ops, plan.warm_then_measure(|_| kernel(ops)).1)
}

/// `ops` calls `out[i] = f(a[i])`, in sweeps over the arrays, each reading operands the optimizer cannot see.
fn sweep<T: Copy, U>(a: &[T], out: &mut [U], ops: usize, f: impl Fn(T) -> U) {
    for _ in 0..ops / a.len() {
        for (o, &x) in out.iter_mut().zip(black_box(a)) {
            *o = f(x);
        }
        black_box(&mut *out);
    }
}

/// `ops` calls `out[i] = f(a[i], b[i])`, in sweeps as [`sweep`].
fn sweep2<T: Copy, U>(a: &[T], b: &[T], out: &mut [U], ops: usize, f: impl Fn(T, T) -> U) {
    for _ in 0..ops / a.len() {
        let (a, b) = black_box((a, b));
        for ((o, &x), &y) in out.iter_mut().zip(a).zip(b) {
            *o = f(x, y);
        }
        black_box(&mut *out);
    }
}

/// `ops` dependent calls `x = f(x, y)`.
fn chain<T: Copy>(x: T, y: T, ops: usize, f: impl Fn(T, T) -> T) {
    let (mut x, y) = black_box((x, y));
    for _ in 0..ops {
        x = f(x, y);
    }
    black_box(x);
}
