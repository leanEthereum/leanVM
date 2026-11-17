//! Proof-level properties of the VM: that its channels carry everything, and that a malformed input is an error rather than a panic.

use crate::py_source::lean_compiled;
use lean_vm_core::cpu::{Proof, ProveError, prove, verify};

/// `hash_slices.py` as the Lean back end compiled it, with a proof of its run: its proof carries the Keccak reduction
/// over real compressions.
fn hashing_proof() -> (isa::Program, [primitives::field::F128; 2], Proof) {
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
