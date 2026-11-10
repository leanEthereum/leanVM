//! Pins the portable `verifier` crate against `cpu::prove` on the shared fixture: it accepts the honest proof at every
//! rate, replays it to the summary `cpu::verify` leaves, and rejects tampered scalars, and under Canopy tampered
//! openings, at the expected check. The Lean transcription (`formal/Statement/LeanVmVerifier.lean`) is pinned against
//! this crate by `formal/`'s differential tests.

use crate::fixture::{bytecode, chain, fixture};
use leanvm_core::cpu::{Program, prove, public_input_bytes, scalar_proof};
use leanvm_core::tables::N_TABLES;
use primitives::field::F192;
use verifier::{E, Proof, Summary, VerifierError, replay_unchecked, verify_execution};

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

/// The stacked size a proof's summary announces.
fn stack_log(program: &Program, public_input: [F192; 2], summary: &Summary) -> usize {
    let rows = std::array::from_fn(|t| summary.table_rows[t] as usize);
    program.layout(summary.log_memory, rows, public_input).shape.mu
}

/// Under Canopy, at rates 1/2 and 1/4, a proof verifies and replays to the summary verifying it leaves, at the
/// fixture's size and at a smaller one. (The Keccak batch tests reach the smallest stack, where L1 is the last level.)
#[test]
fn canopy_round_trips_at_every_enabled_rate() {
    let fixture = fixture();
    let small = chain(64);
    for (program, public_input) in [(&fixture.program, fixture.public_input), (&small.0, small.1)] {
        let (bytecode, statement) = (bytecode(program), public_input_bytes(&public_input));
        for log_inv_rate in [1, 2] {
            let proof = scalar_proof(&prove(program, public_input, log_inv_rate).unwrap().0);
            let summary = verify_execution(&bytecode, &statement, &proof).expect("an honest proof verifies");
            assert_eq!(replay_unchecked(&bytecode, &statement, &proof), Ok(summary));
        }
    }
}

/// Stream scalars after the Canopy cross polynomial: each WHIR level past L0, its fold rounds, then its commitment
/// with its OOD claim or the residual, the grinding nonce and the query intro, and after the residual the rounds but
/// the last.
fn whir_tail_after_cross(log_n: usize, log_inv_rate: usize) -> usize {
    let levels = verifier::whir_queries(log_n, log_inv_rate).unwrap().len();
    let mut message_log = log_n - 6;
    let mut tail = 0;
    for level in 1..levels {
        let fold = message_log.min(4);
        message_log -= fold;
        tail += 2 * fold;
        tail += if level + 1 == levels {
            (1 << message_log) + 3 + 2 * (message_log - 1)
        } else {
            8
        };
    }
    tail
}

/// Under Canopy, each tamper of the forest, the Canopy codeword or the Canopy scalars fails the check that first meets
/// it. The forest's rows and siblings reach the transcript through the roots they climb to, and the scalars directly,
/// so the next check drawn after them fails: the outer protocol's for the OOD value and the root, the next grinding
/// nonce for the rest. A forest path one level too high has the wrong shape, the Canopy codeword's rows answer to its
/// root, and without the Canopy codeword's phase L1 reads the next level's.
#[test]
fn canopy_tampers_fail_their_check() {
    let fixture = fixture();
    let honest = scalar_proof(&fixture.proof);
    let log_n = stack_log(&fixture.program, fixture.public_input, &fixture.summary);
    let cross = honest.stream.len() - whir_tail_after_cross(log_n, 1) - 3;
    let ood_value = N_TABLES + 4;
    let other_root = scalar_proof(&prove(&fixture.program, fixture.public_input, 2).unwrap().0).stream
        [N_TABLES + 2..N_TABLES + 4]
        .to_vec();
    type Tamper = Box<dyn Fn(&mut Proof)>;
    let cases: [(&str, Tamper, VerifierError); 8] = [
        (
            "an L0 row word",
            Box::new(|proof| proof.merkle_openings[0][3].leaf[63].0 ^= 1),
            VerifierError::GrindingNonce,
        ),
        (
            "a forest sibling",
            Box::new(|proof| proof.merkle_openings[0][5].siblings[1][0] ^= 1),
            VerifierError::GrindingNonce,
        ),
        (
            "a forest path one level higher",
            Box::new(|proof| {
                proof.merkle_openings[0]
                    .iter_mut()
                    .for_each(|path| path.siblings.push([0; 32]))
            }),
            VerifierError::MerkleOpeningShape,
        ),
        (
            "a Canopy codeword row word",
            Box::new(|proof| proof.merkle_openings[2][0].leaf[0].0 ^= 1),
            VerifierError::MerkleRootMismatch,
        ),
        (
            "the OOD value",
            Box::new(move |proof| proof.stream[ood_value] += E::new(1, 0, 0)),
            VerifierError::GkrLayer(22),
        ),
        (
            "a cross coefficient",
            Box::new(move |proof| proof.stream[cross] += E::new(1, 0, 0)),
            VerifierError::GrindingNonce,
        ),
        (
            "the root of another commitment",
            Box::new(move |proof| proof.stream[N_TABLES + 2..N_TABLES + 4].copy_from_slice(&other_root)),
            VerifierError::GkrLayer(22),
        ),
        (
            "the Canopy codeword's phase",
            Box::new(|proof| drop(proof.merkle_openings.remove(2))),
            VerifierError::MerkleOpeningShape,
        ),
    ];
    for (tamper, change, error) in cases {
        let mut proof = honest.clone();
        change(&mut proof);
        assert_eq!(
            verify_execution(&fixture.bytecode, &fixture.public_input_bytes, &proof).map(|_| ()),
            Err(error),
            "{tamper}"
        );
    }
}
