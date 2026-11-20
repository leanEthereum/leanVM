//! Proof-level properties of the VM: that its channels carry everything, and that a malformed input is an error rather than a panic.

use crate::common::compiled;
use crate::py_source::lean_compiled;
use fiat_shamir_prover::merkle::hash_to_scalars;
use lean_vm_core::cpu::{Proof, ProveError, prove, verify};
use primitives::field::F128;

/// `hash_slices.py` as the Lean back end compiled it, with a proof of its run: its proof carries the Keccak reduction
/// over real compressions.
fn hashing_proof() -> (isa::Program, [F128; 2], Proof) {
    let (program, streams, pi) = lean_compiled("hash_slices");
    let (proof, _) = prove(&program, &streams, pi, lean_vm_core::pcs::TEST_LOG_INV_RATE).unwrap();
    verify(&program, &pi, &proof).expect("honest proof verifies");
    (program, pi, proof)
}

/// Out-of-process verification: everything travels in the two channels, so a proof
/// serializes, crosses a process boundary and verifies.
#[test]
fn a_proof_roundtrips_through_bytes() {
    let (program, pi, proof) = hashing_proof();
    let decoded = Proof::from_bytes(&proof.to_bytes()).expect("proof deserializes");
    assert_eq!(decoded, proof);
    verify(&program, &pi, &decoded).expect("a deserialized proof verifies");
}

/// An unsupported rate is an error, not a panic.
#[test]
fn an_unsupported_rate_is_an_error() {
    let (program, streams, pi) = lean_compiled("hash_slices");
    let rate = lean_vm_core::pcs::MAX_LOG_INV_RATE + 1;
    assert_eq!(
        prove(&program, &streams, pi, rate).err(),
        Some(ProveError::InvalidRate { log_inv_rate: rate })
    );
}

/// The cells `[5, 7]` after `n` steps of `keccak(h, h, h)`: the public input of `n` chained hashes.
fn chained_digest(n: usize) -> [F128; 2] {
    let mut h = [0; 32];
    (h[0], h[16]) = (5, 7);
    for _ in 0..n {
        h = keccak256::hash_pair(&h, &h);
    }
    hash_to_scalars(&h)
}

/// A KECCAK table of any height proves and verifies: below the Keccak reduction's
/// block of 512 steps, where padding fills the floor, at it, and one step past it.
/// `tests/vm/keccak_steps.py` at each count, as the Lean back end compiled it.
#[test]
fn any_number_of_steps_proves() {
    for n in [0usize, 1, 3, 512, 513] {
        let pi = chained_digest(n);
        let program = compiled(&format!("keccak_steps{n}"));
        let (proof, stats) = prove(&program, &[], pi, lean_vm_core::pcs::TEST_LOG_INV_RATE).unwrap();
        assert_eq!(stats.table_heights[5], n, "{n} steps");
        verify(&program, &pi, &proof).unwrap_or_else(|e| panic!("{n} steps: {e:?}"));
    }
}

/// The memory announced is the least power of two covering the cells a run touches,
/// with no floor but the protocol's: the empty program proves on a memory of a few
/// cells, smaller than a line of the memory columns' fill.
#[test]
fn a_tiny_memory_proves() {
    let program = compiled("empty");
    let pi = [F128::ZERO; 2];
    let (proof, stats) = prove(&program, &[], pi, lean_vm_core::pcs::TEST_LOG_INV_RATE).unwrap();
    assert!(stats.memory_used <= 4, "{} cells used", stats.memory_used);
    verify(&program, &pi, &proof).expect("honest proof verifies");
}
