//! Fibonacci mod 2^64: the demo benchmark. Two registers hold `F(k)` and `F(k+1)`, and
//! one `add` onto either of them is one step of the recurrence.

use leanvm::asm::*;
use leanvm::{Program, TEXT_BASE, prove, verify};
use primitives::{bench::Plan, pretty_f64, pretty_integer};

/// Prove and verify `n` steps of Fibonacci, binding `F(n) mod 2^64` as the output. Prints the benchmark report. Proving runs one discarded warmup pass
/// followed by `plan.repeat` measured passes (see [`primitives::bench`]).
pub fn run_fibonacci(n: usize, log_inv_rate: usize, plan: Plan) {
    let trace_span = tracing::info_span!("Fibonacci", n, log_inv_rate).entered();

    let (program, expected) = fibonacci_program(n);

    // Only the final measured pass of each stage is traced.
    let ((proof, output, stats), prove_time) = plan.warm_then_measure(|last| {
        let _quiet = (!last).then(primitives::suppress_tracing);
        prove(&program, [0; 4], &[], log_inv_rate).expect("the run halts")
    });
    assert_eq!(output, expected);
    let (_, verify_time) = Plan::new(plan.repeat, 0).measure_quiet(|last| {
        let _quiet = (!last).then(primitives::suppress_tracing);
        verify(&program, &[0; 4], &output, &proof).unwrap()
    });

    // tracing-forest renders its tree only when the root span closes, so the
    // complete trace has to be flushed above the report.
    drop(trace_span);

    println!("Fibonacci (modulo 2^64), N = {}", pretty_integer(n));
    println!("  cycles (VM steps)           : {}", pretty_integer(stats.cycles));
    println!("    details                   : {}", stats.details());
    let proof_bytes = bincode::serialized_size(&proof).expect("proof is serializable");
    println!("  proof size                  : {:.1} KiB", proof_bytes as f64 / 1024.0);
    let cycles_per_second = (stats.cycles as f64 / prove_time.mean()).round() as u64;
    println!(
        "  proving                     : {} s{}   {} cycles/s      peak memory {} GiB",
        pretty_f64(prove_time.mean()),
        prove_time.spread(),
        pretty_integer(cycles_per_second),
        pretty_f64(primitives::bench::peak_rss_bytes() as f64 / (1u64 << 30) as f64)
    );
    println!(
        "  verifying                   : {} ms",
        pretty_f64(verify_time.mean() * 1000.0)
    );
}

/// The demo program and its output `[F(n) mod 2^64, 0, 0, 0]`: a loop whose body is
/// `UNROLL` recurrence steps in place, `a <- a + b` then `b <- a + b`, so that a step is
/// one instruction and the loop's own two are paid once per `UNROLL`.
fn fibonacci_program(fib_n: usize) -> (Program, [u64; 4]) {
    const UNROLL: usize = 1000;
    assert!(
        fib_n >= UNROLL && fib_n.is_multiple_of(UNROLL),
        "fib_n must be a positive multiple of {UNROLL}"
    );
    let mut text = Asm::new();
    text.li(A0, 0).li(A1, 1).li(T0, (fib_n / UNROLL) as u64).label("loop");
    for _ in 0..UNROLL / 2 {
        text.r("add", A0, A0, A1).r("add", A1, A0, A1);
    }
    text.i("addi", T0, T0, -1)
        .branch("bne", T0, ZERO, "loop")
        .li(A1, 0)
        .exit();

    let (mut a, mut b) = (0u64, 1u64);
    for _ in 0..fib_n / 2 {
        a = a.wrapping_add(b);
        b = b.wrapping_add(a);
    }
    (Program::new(&text.finish(), TEXT_BASE, vec![], 2, 0), [a, 0, 0, 0])
}

#[cfg(test)]
mod tests {
    #[test]
    fn fibonacci() {
        super::run_fibonacci(
            200_000,
            lean_vm::pcs::TEST_LOG_INV_RATE,
            primitives::bench::Plan::default(),
        );
    }
}
