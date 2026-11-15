//! Fibonacci in the exponent: the demo benchmark (`buff[g^k] = g^{F(k)}`,
//! recurrence `buff[i·g²] = buff[i·g] · buff[i]`).

use crate::report::{pretty_f64, pretty_integer};
use bench::Plan;
use isa::Prover;
use lean_compiler::{compile, parse};
use rec_aggregation::vm;
use verifier::{E, K};

/// Prove and verify Fibonacci-in-the-exponent over a `HeapBuf` (an unrolled
/// `mul_range` recurrence), binding `g^{F(n)}` as the public input. Prints the
/// benchmark report. Proving runs one discarded warmup pass followed by
/// `plan.repeat` measured passes (see [`bench`]).
pub fn run_fibonacci<P: Prover>(n: usize, log_inv_rate: usize, plan: Plan) {
    let trace_span = tracing::info_span!("Fibonacci", n, log_inv_rate).entered();

    let (src, pi) = fibonacci_program(n);
    let compiled = compile(&parse(&src).unwrap());
    let bytecode = verifier::Bytecode::new(&vm::bytecode_table(&compiled.prog));
    let program = P::assemble(compiled);
    let public_input = verifier::Digest::from_halves(pi[0], pi[1]).0;

    // Only the final measured pass of each stage is traced (see `run_aggregation`).
    let ((proof, stats), prove_time) = plan.warm_then_measure(|last| {
        let _quiet = (!last).then(bench::suppress_tracing);
        P::prove(&program, pi, log_inv_rate).expect("the Fibonacci program proves")
    });
    let (_, verify_time) = Plan::new(plan.repeat, 0).measure_quiet(|last| {
        let _quiet = (!last).then(bench::suppress_tracing);
        verifier::verify_execution(&bytecode, &public_input, &proof).unwrap()
    });

    drop(trace_span);

    println!(
        "Fibonacci (in the exponent, i.e. modulo 2^64 - 1), N = {}",
        pretty_integer(n)
    );
    println!("  cycles (VM steps)           : {}", pretty_integer(stats.cycles));
    println!("    details                   : {}", crate::report::details(&stats));
    crate::report::print_proof_size(vm::to_bytes(&proof).len());
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

/// Build the demo program: Fibonacci in the exponent over `fib_n` steps (an
/// unrolled `mul_range` loop over a `HeapBuf`), with the result `g^{F(N)}`
/// published into cell `m[0]`. Returns the zkDSL source and the public input
/// `[g^{F(N)}, 0]`.
fn fibonacci_program(fib_n: usize) -> (String, [E; 2]) {
    const UNROLL: usize = 1000;
    assert!(
        fib_n >= UNROLL && fib_n.is_multiple_of(UNROLL),
        "fib_n must be a positive multiple of {UNROLL}"
    );
    let blocks = fib_n / UNROLL;

    let (mut previous, mut current) = (K(1), K(2));
    for _ in 1..=fib_n {
        let next = previous * current;
        previous = current;
        current = next;
    }
    let public_input = [E::from(previous), E::new(0, 0)];

    // `K` blocks: each reads its boundary pair into locals, runs `UNROLL`
    // Fibonacci `MUL`s in registers, and writes the next pair (4 DEREFs per
    // block). The loop counter `x = gʲ` is the block index (×g each iteration);
    // block `j`'s boundary pair lives at cells `g^{2j}, g^{2j+1}`, so its base is
    // `b = x·x = g^{2j}`.
    let mut body = String::from("        b = x * x\n        f0 = buff[b]\n        f1 = buff[b * GEN]\n");
    for j in 2..=UNROLL + 1 {
        body.push_str(&format!("        f{j} = f{} * f{}\n", j - 2, j - 1));
    }
    body.push_str(&format!("        buff[b * GEN ** 2] = f{UNROLL}\n"));
    body.push_str(&format!("        buff[b * GEN ** 3] = f{}\n", UNROLL + 1));

    // Publish the result g^{F(N)} = buff[GEN ** {2K}] into cell m[0]: a pointer
    // whose value is g^0 (`p = 1`) addresses m[0] (`p[1] = m[1·g^0] = m[g^0]`),
    // and write-once forces m[0] to equal the seeded public input pi[0].
    let publish = format!("    p = 1\n    p[1] = buff[GEN ** {}]\n", 2 * blocks);

    let src = format!(
        "def main():\n\
        \x20   buff = HeapBuf({size})\n\
        \x20   buff[1] = 1\n\
        \x20   buff[GEN] = GEN\n\
        \x20   for x in mul_range(1, GEN ** {blocks}):\n\
        {body}\
        {publish}\
        \x20   return\n",
        size = 2 * blocks + 2,
    );
    (src, public_input)
}

#[cfg(test)]
mod tests {
    #[test]
    fn fibonacci() {
        <stable_leanvm_core::StableProver as isa::Prover>::init();
        super::run_fibonacci::<stable_leanvm_core::StableProver>(
            200_000,
            stable_leanvm_core::pcs::TEST_LOG_INV_RATE,
            bench::Plan::default(),
        );
    }
}
