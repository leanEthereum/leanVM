//! Adversarial binding test for deferred-claim bus denominators: every transcript
//! scalar in the logup/deferred-claim region must be binding — flipping any one
//! byte must make verification reject.

use backend::*;
use lean_compiler::*;
use lean_prover::{default_whir_config, prove_execution::prove_execution, verify_execution::verify_execution};
use lean_vm::*;

const PROGRAM: &str = r#"
def main():
    x: Mut = 0
    y: Mut = 1
    for i in unroll(0, 200):
        z = x + y
        x = y
        y = z
    assert y != 0
    return
"#;

fn build_proof() -> (Bytecode, [F; PUBLIC_INPUT_LEN], Proof<F>) {
    let bytecode = compile_program_with_flags(&ProgramSource::Raw(PROGRAM.to_string()), CompilationFlags::default());
    let public_input = [F::ZERO; PUBLIC_INPUT_LEN];
    let witness = ExecutionWitness::default();
    let proof = prove_execution(&bytecode, &public_input, &witness, &default_whir_config(1), false).unwrap();
    (bytecode, public_input, proof.proof)
}

#[test]
fn deferred_claims_are_binding() {
    let (bytecode, public_input, proof) = build_proof();

    // Honest proof verifies.
    verify_execution(&bytecode, &public_input, proof.clone()).expect("honest proof must verify");

    let bytes = postcard::to_allocvec(&proof).expect("serialize");

    // The transcript Vec<F> begins after its varint length header; each scalar is
    // 8 bytes LE. Locate the header length by decoding the varint at offset 0.
    let mut varint_len = 0usize;
    let mut n_scalars = 0u64;
    for (i, b) in bytes.iter().enumerate() {
        n_scalars |= u64::from(b & 0x7f) << (7 * i);
        varint_len += 1;
        if b & 0x80 == 0 {
            break;
        }
    }
    let n_scalars = n_scalars as usize;
    assert!(n_scalars > 256, "transcript unexpectedly short: {n_scalars}");

    // Sweep the early transcript region (dims, commitment root, OOD, GKR rounds,
    // logup claims incl. the deferred D̂_i, AIR rounds) plus a tail sample.
    let mut tested = 0usize;
    let mut rejected = 0usize;
    let sweep: Vec<usize> = (0..n_scalars.min(1200))
        .step_by(13)
        .chain([n_scalars - 1, n_scalars / 2])
        .collect();
    for scalar_idx in sweep {
        let byte_idx = varint_len + scalar_idx * 8 + 3; // mid-limb byte: always value-changing
        let mut tampered = bytes.clone();
        tampered[byte_idx] ^= 0x5a;
        tested += 1;
        match postcard::from_bytes::<Proof<F>>(&tampered) {
            Err(_) => rejected += 1, // deserialization caught it
            Ok(p) => {
                if verify_execution(&bytecode, &public_input, p).is_err() {
                    rejected += 1;
                } else {
                    panic!("tampered transcript scalar {scalar_idx} ACCEPTED — binding failure");
                }
            }
        }
    }
    assert_eq!(tested, rejected);
    println!("h9 adversarial sweep: {rejected}/{tested} tampered transcripts rejected");
}
