//! A Keccak hash chain: the benchmark of the `SHA3` opcode through the whole proof.

use bench::Plan;
use lean_compiler::{compile, parse};
use leanvm_core::cpu::{prove, verify};
use leanvm_core::vmhash::compress;
use primitives::{
    field::{F64, F192},
    pretty_f64, pretty_integer,
};

/// Prove and verify a chain of `n` steps, `unroll` of them per loop iteration, binding the last
/// digest as the public input. Prints the benchmark report. Proving runs one discarded warmup
/// pass followed by `plan.repeat` measured passes (see [`bench`]).
pub fn run_hash(n: usize, unroll: usize, log_inv_rate: usize, plan: Plan) {
    assert!(
        unroll >= 1 && n.is_multiple_of(unroll),
        "--n must be a positive multiple of --unroll"
    );
    let trace_span = tracing::info_span!("Hash chain", n, log_inv_rate).entered();

    let mut digest = [F64::ZERO; 4];
    for _ in 0..n {
        digest = compress(digest, digest);
    }
    let pi = [
        F192::new(digest[0].0, digest[1].0, 0),
        F192::new(digest[2].0, digest[3].0, 0),
    ];
    let program = compile(&parse(&chain_program(n, unroll)).unwrap());

    let ((proof, stats), prove_time) = plan.warm_then_measure(|last| {
        let _quiet = (!last).then(bench::suppress_tracing);
        prove(&program, pi, log_inv_rate).expect("the hash chain proves")
    });
    let (_, verify_time) = Plan::new(plan.repeat, 0).measure_quiet(|last| {
        let _quiet = (!last).then(bench::suppress_tracing);
        verify(&program, &pi, &proof).unwrap()
    });

    drop(trace_span);

    println!("Keccak hash chain, N = {}", pretty_integer(n));
    println!("  cycles (VM steps)           : {}", pretty_integer(stats.cycles));
    println!("    details                   : {}", stats.details());
    crate::report::print_proof_size(&proof);
    let hashes_per_second = (n as f64 / prove_time.mean()).round() as u64;
    println!(
        "  proving                     : {} s{}   {} hashes/s      peak memory {} GiB",
        pretty_f64(prove_time.mean()),
        prove_time.spread(),
        pretty_integer(hashes_per_second),
        crate::report::peak_gib()
    );
    println!(
        "  verifying                   : {} ms",
        pretty_f64(verify_time.mean() * 1000.0)
    );
}

/// Each iteration reads a digest off the heap, hashes it with itself `unroll` times in frame
/// cells, and writes the result for the next one.
fn chain_program(steps: usize, unroll: usize) -> String {
    let blocks = steps / unroll;
    let mut body = String::from(
        "        b = i * i\n        h0 = StackBuf(2)\n        h0[0] = buff[b]\n        h0[1] = buff[b * GEN]\n",
    );
    for step in 1..=unroll {
        body.push_str(&format!(
            "        h{step} = StackBuf(13)\n        sha3(h{previous}[0:2], h{previous}[0:2], h{step})\n",
            previous = step - 1
        ));
    }
    for word in 0..2 {
        body.push_str(&format!("        buff[b * GEN ** {}] = h{unroll}[{word}]\n", 2 + word));
    }
    format!(
        "def main():\n    buff = HeapBuf({size})\n    buff[1] = 0\n    buff[GEN] = 0\n    for i in mul_range(1, GEN ** {blocks}):\n{body}    output = 1\n    output[1] = buff[GEN ** {result}]\n    output[GEN] = buff[GEN ** {next}]\n    return\n",
        size = 2 * blocks + 2,
        result = 2 * blocks,
        next = 2 * blocks + 1,
    )
}

#[cfg(test)]
mod tests {
    #[test]
    fn hash_chain() {
        super::run_hash(1024, 16, leanvm_core::pcs::TEST_LOG_INV_RATE, bench::Plan::default());
    }
}
