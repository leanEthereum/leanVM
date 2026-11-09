//! Pins the portable `verifier` crate against `cpu::prove` on the shared fixture: it accepts the honest proof at every
//! rate, replays it to the summary `cpu::verify` leaves, and rejects tampered scalars at the expected check. The Lean
//! transcription (`formal/Statement/LeanVmVerifier.lean`) is pinned against this crate by `formal/`'s differential tests.

use crate::fixture::fixture;
use leanvm_core::cpu::{prove, scalar_proof};
use leanvm_core::tables::N_TABLES;
use verifier::{E, VerifierError, replay_unchecked, verify_execution};

/// The replay reads out of an honest proof what verifying it leaves.
#[test]
fn replay_reads_the_summary_unchecked() {
    let fixture = fixture();
    assert_eq!(
        replay_unchecked(
            &fixture.bytecode,
            &fixture.public_input_bytes,
            &scalar_proof(&fixture.proof)
        )
        .as_ref(),
        Ok(&fixture.summary)
    );
}

/// The proof verifies at every rate: each walks other rows of the tabulated query counts and another ladder of level
/// rates.
#[test]
fn verifies_at_every_rate() {
    let fixture = fixture();
    for log_inv_rate in 1..=4 {
        let proof = match log_inv_rate {
            1 => scalar_proof(&fixture.proof),
            _ => scalar_proof(&prove(&fixture.program, fixture.public_input, log_inv_rate).unwrap().0),
        };
        assert_eq!(
            verify_execution(&fixture.bytecode, &fixture.public_input_bytes, &proof).map(|_| ()),
            Ok(()),
            "rate {log_inv_rate}"
        );
    }
}

/// A tampered scalar fails the check that reads it: a high limb on an announced size and on the commitment root, and
/// each check of the Keccak reduction tripped by the scalar it reads last.
#[test]
fn tampers_fail_their_check() {
    let fixture = fixture();
    // The reduction's stream: the committed outputs' claim, then each layer opening on its product polynomial and
    // ending on three evaluations. The output opening follows (a slot sumcheck, then the word), then the input opening
    // (a sumcheck over a pack's instances, one over the slot, then the slices). A degree-3 sumcheck sends two
    // scalars a round.
    const PRODUCT_COEFFICIENTS: usize = 47; // a product of two degree-23 embeddings
    const PACK_BITS: usize = 4; // sixteen instances a pack
    const SLOT_BITS: usize = 6; // 25 lanes of the 2 segments' states
    const SLICES: usize = 64;
    let keccak = fixture.summary.keccak_scalars.clone();
    let input_opening = 2 * (PACK_BITS + SLOT_BITS) + SLICES;
    let output_opening = 2 * SLOT_BITS + 1;
    let cases = [
        (0, VerifierError::AnnouncedHighLimb),
        (N_TABLES + 2, VerifierError::DigestHalf),
        (keccak.start + PRODUCT_COEFFICIENTS, VerifierError::KeccakProduct),
        (
            keccak.end - input_opening - output_opening - 1,
            VerifierError::KeccakLayer,
        ),
        (keccak.end - input_opening - 1, VerifierError::KeccakOutputOpening),
        (keccak.end - 1, VerifierError::KeccakInputOpening),
    ];
    for (position, error) in cases {
        let mut proof = scalar_proof(&fixture.proof);
        proof.stream[position] += E::new(0, 0, 1);
        assert_eq!(
            verify_execution(&fixture.bytecode, &fixture.public_input_bytes, &proof),
            Err(error),
            "scalar {position}"
        );
    }
}
