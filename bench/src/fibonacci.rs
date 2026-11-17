//! Fibonacci in the exponent: the demo benchmark (`buff[g^k] = g^{F(k)}`,
//! recurrence `buff[i·g²] = buff[i·g] · buff[i]`).

use bench_harness::Plan;
use isa::{Prover, pretty_f64, pretty_integer};
use verifier::{E, K};

/// The program (`crates/zkdsl_compiler/tests/programs/fibonacci_bench.py`) as the Lean back end compiled it
/// (`lake exe guest-backend export programs`): `UNROLL` Fibonacci steps a block, the block count read from the second
/// public word.
const PROGRAM: &str = include_str!("../../../crates/zkdsl_compiler/tests/suite/lean_backend/fibonacci_bench.txt");

/// Steps a block of the program.
const UNROLL: usize = 1000;

/// The most blocks the program runs (its `assert log(end) < 16385`).
const MAX_BLOCKS: usize = 16384;

/// Prove and verify Fibonacci-in-the-exponent over a `HeapBuf` (an unrolled
/// `mul_range` recurrence), binding `g^{F(n)}` as the public input. Prints the
/// benchmark report. Proving runs one discarded warmup pass followed by
/// `plan.repeat` measured passes (see [`bench_harness`]).
pub fn run_fibonacci<P: Prover>(n: usize, log_inv_rate: usize, plan: Plan) {
    let trace_span = tracing::info_span!("Fibonacci", n, log_inv_rate).entered();

    let pi = public_input(n);
    let program = isa::Program::__from_text(PROGRAM).expect("the compiled Fibonacci program loads");
    let public_input = verifier::Digest::from_halves(pi[0], pi[1]).0;

    // Only the final measured pass of each stage is traced (see `run_aggregation`).
    let ((proof, stats), prove_time) = plan.warm_then_measure(|last| {
        let _quiet = (!last).then(bench_harness::suppress_tracing);
        P::prove(&program, &[], pi, log_inv_rate).expect("the Fibonacci program proves")
    });
    let (_, verify_time) = Plan::new(plan.repeat, 0).measure_quiet(|last| {
        let _quiet = (!last).then(bench_harness::suppress_tracing);
        verifier::verify_execution(program.bytecode(), &public_input, &proof).unwrap()
    });

    drop(trace_span);

    println!(
        "Fibonacci (in the exponent, i.e. modulo 2^64 - 1), N = {}",
        pretty_integer(n)
    );
    println!("  cycles (VM steps)           : {}", pretty_integer(stats.cycles));
    println!(
        "    details                   : {}",
        crate::report::details(&stats, program.code_len())
    );
    crate::report::print_proof_size(proof.to_bytes().len());
    let cycles_per_second = (stats.cycles as f64 / prove_time.mean()).round() as u64;
    println!(
        "  proving                     : {} s{}   {} cycles/s      peak memory {} GiB",
        pretty_f64(prove_time.mean()),
        prove_time.spread(),
        pretty_integer(cycles_per_second),
        crate::report::peak_gib()
    );
    println!(
        "  verifying                   : {} ms",
        pretty_f64(verify_time.mean() * 1000.0)
    );
}

/// The public input of `fib_n` steps: the result `g^{F(N)}` the program publishes into `m[0]`, and the block count
/// `g^{N / UNROLL}` it reads from `m[1]`.
fn public_input(fib_n: usize) -> [E; 2] {
    assert!(
        fib_n >= UNROLL && fib_n.is_multiple_of(UNROLL) && fib_n / UNROLL <= MAX_BLOCKS,
        "fib_n must be a positive multiple of {UNROLL}, at most {}",
        UNROLL * MAX_BLOCKS
    );
    let (mut previous, mut current) = (K(1), K(2));
    for _ in 1..=fib_n {
        let next = previous * current;
        previous = current;
        current = next;
    }
    [E::from(previous), E::from(K(2)).pow((fib_n / UNROLL) as u64)]
}

#[cfg(test)]
mod tests {
    #[test]
    fn fibonacci() {
        super::run_fibonacci::<stable_lean_vm_core::StableProver>(
            200_000,
            stable_lean_vm_core::pcs::TEST_LOG_INV_RATE,
            bench_harness::Plan::default(),
        );
    }
}
