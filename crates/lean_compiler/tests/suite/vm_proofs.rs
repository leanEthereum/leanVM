//! Proof-level properties of the VM: what a proof is bound to, that its channels
//! carry everything, and that tampering with either channel is rejected.
//!
//! These live here rather than beside the prover because a provable program's tables
//! must all be powers of two, which is the compiler's fill blocks' job
//! (`lean_compiler::filler`). A hand-written bytecode program would have to fill itself,
//! duplicating their knowledge of what a dummy row looks like.

use lean_compiler::{compile, parse};
use lean_vm::cpu::{CpuError, Proof, prove, verify};
use lean_vm::vmhash::compress;
use primitives::field::{F64, F192};

/// A program that hashes one block and publishes the digest, so its proof carries
/// flock's sub-proof over a real compression.
const HASHING: &str = "\
def main():
    a = StackBuf(2)
    a[0] = 5
    a[1] = 7
    c = StackBuf(2)
    blake2s(a, a, c)
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

fn hashing_proof() -> (lean_vm::cpu::Program, [F192; 2], Proof) {
    let program = compile(&parse(HASHING).expect("parse"));
    let pi = hashing_pi();
    let (proof, _) = prove(&program, pi, lean_vm::pcs::TEST_LOG_INV_RATE);
    verify(&program, &pi, &proof).expect("honest proof verifies");
    (program, pi, proof)
}

/// The stacked WHIR opening rides the proof's Merkle phases. Nothing there is
/// bound by the transcript (only by the Merkle structure), so tampering an opened
/// row must still be rejected.
#[test]
fn a_tampered_opening_is_rejected() {
    let (program, pi, mut proof) = hashing_proof();
    let phase = proof.merkle.first_mut().expect("stacked WHIR opening");
    phase.leaf_data[0][0].0 ^= 1;
    assert!(
        verify(&program, &pi, &proof).is_err(),
        "a tampered validity proof must be rejected"
    );
}

/// flock's reduction sub-proof (zerocheck, lincheck, ring switch) rides the scalar
/// stream as raw transport, but its values re-enter the transcript through the verifier's
/// replay, so a flipped transport word diverges the recovered flock claim.
#[test]
fn a_tampered_reduction_word_is_rejected() {
    let (program, pi, proof) = hashing_proof();
    let mut tampered = proof;
    let n = tampered.stream.len();
    // The second-to-last word is always meaningful bytes; only the final one may be
    // zero-padded.
    tampered.stream[n - 2] += F192::ONE;
    assert!(
        verify(&program, &pi, &tampered).is_err(),
        "a tampered reduction transport word must be rejected"
    );
}

/// A proof is bound to its exact program. The two programs here have the same shape,
/// so the same layout and announced sizes, and differ in one constant; the program
/// digest seeds the transcript, so it diverges at the first squeeze. This is
/// the adaptive-statement forgery that the bytecode bus's single-point check does not,
/// on its own, prevent.
#[test]
fn a_proof_does_not_verify_against_another_program() {
    // The differing constant has to reach the bytecode: an unused one folds away at
    // compile time and the two programs come out byte-identical. Hashing it does the
    // job, and publishing nothing keeps the public input the same for both.
    let src = |k: u32| {
        format!(
            "def main():\n    a = StackBuf(2)\n    a[0] = {k}\n    a[1] = 7\n    \
             c = StackBuf(2)\n    blake2s(a, a, c)\n    return\n"
        )
    };
    let program = compile(&parse(&src(5)).expect("parse"));
    let other = compile(&parse(&src(6)).expect("parse"));
    let pi = [F192::ZERO, F192::ZERO];
    let (proof, _) = prove(&program, pi, lean_vm::pcs::TEST_LOG_INV_RATE);
    verify(&program, &pi, &proof).expect("honest proof verifies");
    assert!(
        verify(&other, &pi, &proof).is_err(),
        "a proof must not verify against a different program"
    );
}

/// Out-of-process verification: everything travels in the two channels, so a proof
/// serializes, crosses a process boundary and verifies, and a flipped announced size
/// is caught before any reduction runs.
#[test]
fn a_proof_roundtrips_through_bytes() {
    let (program, pi, proof) = hashing_proof();
    let bytes = bincode::serialize(&proof).expect("proof serializes");
    let decoded: Proof = bincode::deserialize(&bytes).expect("proof deserializes");
    verify(&program, &pi, &decoded).expect("a deserialized proof verifies");

    // The announced sizes lead the stream: memory log, the table log heights, then
    // the PCS rate.
    let mut bad_rate = decoded.clone();
    bad_rate.stream[1 + lean_vm::cpu::Stats::TABLES.len()] = F192::new(5, 0, 0);
    assert!(
        matches!(verify(&program, &pi, &bad_rate), Err(CpuError::PublicInput)),
        "the announced PCS rate must be in 1..=4"
    );

    // A BLAKE2s height below flock's instance floor describes a layout the
    // arithmetization cannot express, and all three verifiers reject it there.
    let blake2s = lean_vm::cpu::Stats::TABLES
        .iter()
        .position(|&t| t == "BLAKE2S")
        .unwrap();
    let mut sub_floor = decoded;
    sub_floor.stream[1 + blake2s] = F192::new(2, 0, 0);
    assert!(
        matches!(verify(&program, &pi, &sub_floor), Err(CpuError::PublicInput)),
        "the announced BLAKE2s height must reach flock's instance floor"
    );
}
