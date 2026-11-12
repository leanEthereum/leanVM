//! Pins the portable `verifier` crate against `cpu::prove` on the shared fixture: it accepts the honest proof at every
//! rate, replays it to the summary `cpu::verify` leaves, and rejects tampered scalars at the expected check. The Lean
//! transcription (`formal/Statement/LeanVmVerifier.lean`) is pinned against this crate by `formal/`'s differential tests.

use crate::fixture::fixture;
use fiat_shamir::grinding_bits;
use leanvm_core::cpu::{prove, scalar_proof};
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

/// A tampered scalar fails the check that reads it: a high limb on an announced size, an OOD sample value at the first
/// grind after it (a wrong value sent honestly fails the opening, `keccak_gkr`'s OOD test), the bus's bytecode share
/// and the evaluation its sumcheck ends on at that sumcheck's terminal check, each check of the Keccak reduction
/// tripped by the scalar it reads last, and in the WHIR opening a fold-table scalar, a high-part scalar and a grinding
/// nonce, each caught by the grind that follows it, and the last tail scalar by the terminal check.
#[test]
fn tampers_fail_their_check() {
    let fixture = fixture();
    // A grind sends its nonce after the scalars it follows, none at zero bits; a sumcheck round of degree `d` grinds
    // for it, a degree-3 one sending two scalars.
    let nonce = |numerator: u128| usize::from(grinding_bits(numerator) > 0);
    let round = 2 + nonce(2);
    // The reduction's stream: a grind and the committed outputs' claim, then each layer opening on its product
    // polynomial and ending on three evaluations and the grind before beta. The output opening follows (a slot
    // sumcheck, then the word), then the input opening (a sumcheck over a pack's instances, one over the slot, then the
    // slices).
    const SEGMENT_AND_LANE_BITS: u128 = 1 + 5; // two segments, 25 lanes
    const PRODUCT_COEFFICIENTS: usize = 47; // a product of two degree-23 embeddings
    const PACK_BITS: usize = 4; // sixteen instances a pack
    const SLOT_BITS: usize = 6; // 25 lanes of the 2 segments' states
    const SLICES: usize = 64;
    let keccak = fixture.summary.keccak_scalars.clone();
    let input_opening = round * (PACK_BITS + SLOT_BITS) + SLICES;
    let output_opening = round * SLOT_BITS + 1;
    let last_layer = keccak.end - input_opening - output_opening - nonce(2);
    // The WHIR opening ends the stream. Its final level, after its `k` rounds of four scalars and a nonce: the
    // `2^mu + k` coefficients of the folded lane, the query nonce, then the tail rounds. The level before ends on its
    // high part, the OOD nonce, the OOD value and the query nonce.
    let rows: Vec<usize> = fixture.summary.table_rows.iter().map(|&rows| rows as usize).collect();
    let stack_log = leanvm_core::cpu::layout::layout(
        fixture.program.prog(),
        fixture.summary.log_memory,
        rows.try_into().expect("one row count a table"),
        fixture.public_input,
    )
    .shape
    .mu;
    let (mut mu, mut k) = (stack_log - 6, 6); // the ladder: 6 lane variables, then 4 a level while over 5 remain
    while mu > 5 {
        k = mu.min(4);
        mu -= k;
    }
    let stream = scalar_proof(&fixture.proof).stream;
    let end = stream.len();
    let tail = round * mu;
    let final_coefficients = (1 << mu) + k;
    let final_level = 5 * k + final_coefficients + 1 + tail;
    // After the announced sizes (the memory, six tables and the rate), the root and the OOD sample's nonce: its value,
    // which the transcript binds, so the first grind after it, the bus's, already fails.
    let ood_value = 1 + 6 + 1 + 2 + 1;
    // The bytecode sumcheck ends on the stacked bytecode at the summary's point, the scalar the stream holds; its
    // degree-two rounds over the four slot bits follow the share.
    let bytecode_value = fixture.bytecode.evaluate(&fixture.summary.bytecode_point).unwrap();
    let bytecode_value = stream.iter().position(|&s| s == bytecode_value).unwrap();
    let bytecode_share = bytecode_value - 4 * round - 1;
    let cases = [
        (0, VerifierError::AnnouncedHighLimb),
        (ood_value, VerifierError::GrindingNonce),
        (bytecode_share, VerifierError::BytecodeShare),
        (bytecode_value, VerifierError::BytecodeShare),
        (end - tail - final_coefficients - 3, VerifierError::GrindingNonce),
        (end - final_level - 4, VerifierError::GrindingNonce),
        (end - tail - 1, VerifierError::GrindingNonce),
        (end - nonce(2) - 1, VerifierError::WhirTerminal),
        (
            keccak.start + nonce(SEGMENT_AND_LANE_BITS) + PRODUCT_COEFFICIENTS,
            VerifierError::KeccakProduct,
        ),
        (last_layer - 1, VerifierError::KeccakLayer),
        (keccak.end - input_opening - 1, VerifierError::KeccakOutputOpening),
        (keccak.end - 1, VerifierError::KeccakInputOpening),
    ];
    for (position, error) in cases {
        // A tamper that a few-bit grind after it lets through moves every later challenge and fails elsewhere: each
        // case takes the first tamper that reaches its check.
        let found = (1..=64).any(|delta| {
            let mut proof = scalar_proof(&fixture.proof);
            proof.stream[position] += E::new(0, delta);
            verify_execution(&fixture.bytecode, &fixture.public_input_bytes, &proof) == Err(error)
        });
        assert!(found, "no tamper of scalar {position} fails with {error}");
    }
}
