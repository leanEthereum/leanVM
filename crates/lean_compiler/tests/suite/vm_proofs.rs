//! Proof-level properties of the VM: that its channels carry everything, and that a malformed input is an error rather than a panic.

use lean_compiler::{compile, parse};
use leanvm_core::cpu::{CpuError, Proof, ProveError, prove, verify};
use leanvm_core::vmhash::compress;
use primitives::field::{F64, F192};

/// A program that hashes one block and publishes the digest, so its proof carries
/// the Keccak reduction over a real compression.
const HASHING: &str = "\
def main():
    a = StackBuf(2)
    a[0] = 5
    a[1] = 7
    c = StackBuf(2)
    sha3(a, a, c)
    p = 1
    p[1] = c[0]
    p[GEN] = c[1]
    return
";

/// The public input `HASHING` publishes.
fn hashing_pi() -> [F192; 2] {
    let h = [F64(5), F64(0), F64(7), F64(0)];
    let d = compress(h, h);
    [F192::new(d[0].0, d[1].0, 0), F192::new(d[2].0, d[3].0, 0)]
}

fn hashing_proof() -> (leanvm_core::cpu::Program, [F192; 2], Proof) {
    let program = compile(&parse(HASHING).expect("parse"));
    let pi = hashing_pi();
    let (proof, _) = prove(&program, pi, leanvm_core::pcs::TEST_LOG_INV_RATE).unwrap();
    verify(&program, &pi, &proof).expect("honest proof verifies");
    (program, pi, proof)
}

/// A program whose bytecode is not a power of two long is an error, not a panic.
#[test]
fn a_bytecode_that_is_not_a_power_of_two_is_an_error() {
    let (mut program, pi, proof) = hashing_proof();
    program.prog.pop();
    assert!(matches!(verify(&program, &pi, &proof), Err(CpuError::PublicInput)));
}

/// Out-of-process verification: everything travels in the two channels, so a proof
/// serializes, crosses a process boundary and verifies.
#[test]
fn a_proof_roundtrips_through_bytes() {
    let (program, pi, proof) = hashing_proof();
    let bytes = bincode::serialize(&proof).expect("proof serializes");
    let decoded: Proof = bincode::deserialize(&bytes).expect("proof deserializes");
    verify(&program, &pi, &decoded).expect("a deserialized proof verifies");
}

/// An unsupported rate is an error, not a panic.
#[test]
fn an_unsupported_rate_is_an_error() {
    let program = compile(&parse(HASHING).expect("parse"));
    let rate = leanvm_core::pcs::MAX_LOG_INV_RATE + 1;
    assert_eq!(
        prove(&program, hashing_pi(), rate).err(),
        Some(ProveError::InvalidRate { log_inv_rate: rate })
    );
}
