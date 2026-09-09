//! End-to-end proof of an unrolled zkDSL BLAKE2s hash chain.

use std::time::Instant;

use lean_compiler::{compile, compile_without_filler, parse};
use lean_vm::cpu::{prove, verify};
use lean_vm::vmhash::compress;
use primitives::{
    field::{F64, F192},
    pretty_f64, pretty_integer,
};

fn instruction_counts(source: &str, public_input: [F192; 2]) -> [usize; lean_vm::cpu::Stats::TABLES.len()] {
    compile_without_filler(&parse(source).expect("parse"))
        .execute(public_input)
        .base_counts
}

fn chain_source(steps: usize, unroll: usize) -> String {
    assert!(
        unroll >= 1 && steps.is_multiple_of(unroll),
        "N must be a positive multiple of UNROLL"
    );
    let blocks = steps / unroll;
    let result_cell = 2 * blocks;

    let mut body = String::new();
    body.push_str("        b = i * i\n");
    body.push_str("        h0 = StackBuf(2)\n");
    body.push_str("        h0[0] = buff[b]\n");
    body.push_str("        h0[1] = buff[b * GEN]\n");
    for step in 1..=unroll {
        body.push_str(&format!("        h{step} = StackBuf(2)\n"));
        body.push_str(&format!(
            "        blake2s(h{previous}, h{previous}, h{step})\n",
            previous = step - 1
        ));
    }
    for word in 0..2 {
        body.push_str(&format!("        buff[b * GEN ** {}] = h{unroll}[{word}]\n", 2 + word));
    }

    format!(
        "def main():\n\
        \x20   buff = HeapBuf({size})\n\
        \x20   buff[1] = 0\n\
        \x20   buff[GEN] = 0\n\
        \x20   for i in mul_range(1, GEN ** {blocks}):\n\
        {body}\
        \x20   output = 1\n\
        \x20   output[1] = buff[GEN ** {result_cell}]\n\
        \x20   output[GEN] = buff[GEN ** {next_cell}]\n\
        \x20   return\n",
        size = result_cell + 2,
        next_cell = result_cell + 1,
    )
}

#[test]
fn blake2s_hash_chain() {
    let env_usize = |key: &str, default: usize| {
        std::env::var(key)
            .ok()
            .and_then(|value| value.parse().ok())
            .unwrap_or(default)
    };
    let unroll = env_usize("LEANVM_HASH_UNROLL", 4);
    let steps = env_usize("LEANVM_HASH_N", 8);
    assert!(
        steps.is_multiple_of(unroll),
        "LEANVM_HASH_N must be a multiple of LEANVM_HASH_UNROLL"
    );

    let mut digest = [F64::ZERO; 4];
    for _ in 0..steps {
        digest = compress(digest, digest);
    }
    let public_input = [
        F192::new(digest[0].0, digest[1].0, 0),
        F192::new(digest[2].0, digest[3].0, 0),
    ];

    let source = chain_source(steps, unroll);
    let program = compile(&parse(&source).expect("parse"));

    let started = Instant::now();
    let (proof, stats) = prove(&program, public_input, lean_vm::pcs::TEST_LOG_INV_RATE);
    let prove_time = started.elapsed();
    let started = Instant::now();
    verify(&program, &public_input, &proof).expect("hash-chain proof verifies");
    let verify_time = started.elapsed();

    assert_eq!(instruction_counts(&source, public_input)[5], steps);

    println!(
        "\nBLAKE2s hash chain, N = {}, unroll = {}",
        pretty_integer(steps),
        pretty_integer(unroll)
    );
    println!("  cycles (VM steps)           : {}", pretty_integer(stats.cycles));
    for (name, &c) in ["XOR", "MUL", "SET", "DEREF", "JUMP", "BLAKE2S"]
        .iter()
        .zip(&stats.counts)
    {
        let pow = if c == 0 {
            "0".to_string()
        } else {
            format!("2^{}", pretty_f64((c as f64).log2()))
        };
        println!("    {name:<6} instructions       : {pow}");
    }
    println!(
        "  committed witness size      : 2^{:.3}",
        (stats.committed as f64).log2()
    );
    let proof_bytes = bincode::serialized_size(&proof).expect("proof is serializable");
    println!("  proof size                  : {:.1} KiB", proof_bytes as f64 / 1024.0);
    println!("  proving                     : {prove_time:?}");
    println!("  verifying                   : {verify_time:?}");
    let hashes_per_second = (steps as f64 / prove_time.as_secs_f64()).round() as u64;
    println!(
        "  throughput                  : {} hashes/s",
        pretty_integer(hashes_per_second)
    );

    let mut wrong_input = public_input;
    wrong_input[0] += F192::ONE;
    assert!(verify(&program, &wrong_input, &proof).is_err());
}
