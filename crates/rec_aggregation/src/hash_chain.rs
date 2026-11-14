//! End-to-end proof of an unrolled zkDSL Keccak hash chain, on the stable prover.

extern crate stable_leanvm_core as leanvm_core;

use crate::aggregation::public_input_bytes;
use crate::protocol::bytecode_table;
use isa::{Prover, Stats};
use lean_compiler::{compile, parse};
use leanvm_core::Stable;
use leanvm_core::cpu::{from_scalar, scalar_proof};
use std::time::Instant;
use verifier::E;

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
            "        keccak(h{previous}[0:2], h{previous}[0:2], h{step})\n",
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
fn keccak_hash_chain() {
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

    // Each step is one `KECCAK` of the previous digest twice: Keccak-256 of its two copies, little-endian.
    let mut digest = [0; 32];
    for _ in 0..steps {
        digest = keccak256::hash(&[digest, digest].concat());
    }
    let word = |i: usize| u64::from_le_bytes(digest[8 * i..8 * i + 8].try_into().unwrap());
    let public_input = [E::new(word(0), word(1)), E::new(word(2), word(3))];

    let compiled = compile(&parse(&chain_source(steps, unroll)).expect("parse"));
    let bytecode = verifier::Bytecode::new(&bytecode_table(&compiled.prog));
    Stable::init();
    let program = Stable::assemble(compiled);

    let started = Instant::now();
    let (tree_proof, stats) = leanvm_core::cpu::prove(
        &program,
        public_input.map(from_scalar),
        leanvm_core::pcs::TEST_LOG_INV_RATE,
    )
    .expect("proves");
    let prove_time = started.elapsed();
    // The shared wire format is the prover's, both ways.
    let proof = scalar_proof(&tree_proof);
    let bytes = tree_proof.to_bytes();
    assert_eq!(crate::wire::to_bytes(&proof), bytes);
    assert_eq!(crate::wire::from_bytes(&bytes), Some(proof.clone()));
    let started = Instant::now();
    verifier::verify_execution(&bytecode, &public_input_bytes(&public_input), &proof)
        .expect("hash-chain proof verifies");
    let verify_time = started.elapsed();

    assert_eq!(stats.rows[5], steps);

    println!("\nKeccak hash chain, N = {steps}, unroll = {unroll}");
    println!("  cycles (VM steps)           : {}", stats.cycles);
    for (name, &c) in Stats::TABLES.iter().zip(&stats.rows) {
        let pow = if c == 0 {
            "0".to_string()
        } else {
            format!("2^{:.3}", (c as f64).log2())
        };
        println!("    {name:<6} instructions       : {pow}");
    }
    println!(
        "  committed witness size      : 2^{:.3}",
        (stats.committed as f64).log2()
    );
    let proof_bytes = bytes.len();
    println!("  proof size                  : {:.1} KiB", proof_bytes as f64 / 1024.0);
    println!("  proving                     : {prove_time:?}");
    println!(
        "  verifying                   : {:.3} ms",
        verify_time.as_secs_f64() * 1000.0
    );
    let hashes_per_second = (steps as f64 / prove_time.as_secs_f64()).round() as u64;
    println!("  throughput                  : {hashes_per_second} hashes/s");
}
