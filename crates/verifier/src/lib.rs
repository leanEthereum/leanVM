//! A self-contained verifier for leanVM execution proofs: single threaded, std only, plain integer arithmetic.
//!
//! Kept close enough to the Lean transcription (`formal/Statement/Verifier/`, a file per file of this crate, its constants in `formal/Statement/LeanVmVerifier.lean`) to read side by side: the same functions, in the same order, with the same constants.
//!
//! What the transcription has no counterpart for sits in modules of its own: the prepared [`Bytecode`], the proof's byte encoding ([`Proof::to_bytes`]) and what the statement of an aggregate adds, [`da`].
//!
//! One walk of the protocol serves two entry points. [`verify_execution`] checks the proof. [`replay_unchecked`] reads the same [`Summary`] out of it and checks nothing: every check it leaves out is behind `Transcript::checked`.

#![forbid(unsafe_code)]

mod bytecode;
pub mod da;
mod field;
mod hash;
pub mod keccak;
pub mod layout;
mod link;
mod merkle;
mod multilinear;
mod ring_switch;
mod transcript;
mod whir;
mod wire;

pub use bytecode::Bytecode;
pub use field::{E, K};
pub use layout::{
    MAX_LOG_BYTECODE, MAX_LOG_MEMORY, MAX_STACKED_LOG, MAX_TABLE_LOG, MIN_LOG_MEMORY, MIN_STACKED_LOG, TAG,
    min_execution_stacked_log,
};
pub use merkle::MerklePath;
pub use transcript::{DS_OBSERVE, DS_POW_NONCE, Proof, RATE_SCALARS, SECURITY_BITS, grinding_bits};
pub use whir::{
    BATCH_GRINDING_BITS, FOLD_GRINDING_BITS, INITIAL_FOLDING_FACTOR, MAX_LOG_INV_RATE, MIN_LOG_INV_RATE,
    OOD_GRINDING_BITS, QUERY_GRINDING_BITS, RESIDUAL_MAX_LOG, RS_DOMAIN_INITIAL_REDUCTION_FACTOR,
    RS_DOMAIN_SUBSEQUENT_REDUCTION_FACTOR, SUBSEQUENT_FOLDING_FACTOR, whir_queries,
};
pub use wire::{MAX_HEIGHT, MAX_LEAF_WORDS, MAX_PHASES, MAX_QUERIES};

// What the provers and the aggregation's guest constants and witness read of the protocol.
pub use hash::Digest;
pub use link::{
    Chunks, MAX_WIDTH as MAX_POINTER_WIDTH, WINDOW_BITS, link_grind_bits, packed_challenges, pc_slots, pointer_width,
};
pub use multilinear::{Placement, stack_offsets};
pub use whir::{Subspace, WhirConfig, derive_config, subspace_roots};
// For `fiat_shamir_prover`'s test that the prover's transcript and this one agree.
#[doc(hidden)]
pub use transcript::Transcript as __Transcript;

use field::{ONE, ZERO, powers};
use hash::{ROUNDS, STATE_LANES};
use keccak::{KeccakShape, verify_keccak};
use layout::{GLOBAL_COLUMN_BASES, KECCAK_OUT, Layout, MEMORY_0, MEMORY_1, N_TABLES, OP_KECCAK, QKECCAK, build_layout};
use link::verify_link;
use multilinear::{dot, eq_eval, multilinear_eval};
use ring_switch::{RingClaim, RingPiece, ring_switch};
use std::ops::Range;
use transcript::Transcript;
use whir::verify_whir;

/// Why a proof was rejected.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum VerifierError {
    MultilinearSize,
    NotPowerOfTwo,
    StreamExhausted,
    GrindingNonce,
    MerkleOpeningMissing,
    MerkleOpeningShape,
    MerkleOpeningPosition,
    MerkleRootMismatch,
    StreamNotConsumed,
    MerkleNotConsumed,
    /// The link sum-check's last round does not match the summand at its point.
    LinkTerminal,
    AnnouncedTableSizes,
    WhirShape,
    QueryCountLadder,
    InducedBasisDimensions,
    WhirFinalQuery,
    WhirTerminal,
    WhirNoTerminalLevel,
    KeccakProduct,
    KeccakLayer,
    KeccakOutputOpening,
    KeccakInputOpening,
    AnnouncedHighLimb,
    PcsInverseRate,
    CommittedSize,
    StackedClaims,
    BytecodeShape,
}

impl std::fmt::Display for VerifierError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let message = match self {
            Self::MultilinearSize => "multilinear table has the wrong size",
            Self::NotPowerOfTwo => "expected a power of two",
            Self::StreamExhausted => "proof stream exhausted",
            Self::GrindingNonce => "invalid grinding nonce",
            Self::MerkleOpeningMissing => "Merkle opening missing",
            Self::MerkleOpeningShape => "Merkle opening has the wrong shape",
            Self::MerkleOpeningPosition => "Merkle opening at the wrong position",
            Self::MerkleRootMismatch => "Merkle root mismatch",
            Self::StreamNotConsumed => "proof stream not fully consumed",
            Self::MerkleNotConsumed => "Merkle openings not fully consumed",
            Self::LinkTerminal => "link sum-check terminal mismatch",
            Self::AnnouncedTableSizes => "invalid announced table sizes",
            Self::WhirShape => "invalid WHIR shape",
            Self::QueryCountLadder => "tabulated query count does not match the ladder",
            Self::InducedBasisDimensions => "bad induced-basis dimensions",
            Self::WhirFinalQuery => "WHIR final query does not match the final polynomial",
            Self::WhirTerminal => "WHIR terminal check failed",
            Self::WhirNoTerminalLevel => "WHIR verification ended without a terminal level",
            Self::KeccakProduct => "Keccak product polynomial does not carry the claim",
            Self::KeccakLayer => "Keccak layer evaluations do not match the sumcheck",
            Self::KeccakOutputOpening => "Keccak output opening ends on the wrong value",
            Self::KeccakInputOpening => "Keccak input opening ends on the wrong value",
            Self::AnnouncedHighLimb => "announced size has a nonzero high limb",
            Self::PcsInverseRate => "invalid PCS inverse rate",
            Self::CommittedSize => "committed size outside the PCS window",
            Self::StackedClaims => "too many stacked claims",
            Self::BytecodeShape => "bytecode is not the encoding of a program",
        };
        f.write_str(message)
    }
}

impl std::error::Error for VerifierError {}

fn require(condition: bool, error: VerifierError) -> Result<(), VerifierError> {
    if condition { Ok(()) } else { Err(error) }
}

/// The stacked opening's batching is accounted for up to this many claims, the ring-switched ones included. The count
/// follows from the announced shape, so a replay checks it too, like the committed size.
pub const MAX_STACKED_CLAIMS: usize = 512;

/// The weight a claim puts on the stack, and the value it claims for it.
type StackClaim<'a> = (Box<dyn Fn(&[E]) -> E + 'a>, E);

/// Discharge every claim on the committed stack in one opening: the same powers of one challenge
/// batch the values into the target, and the weights into the basis WHIR evaluates at its terminal point.
///
/// The challenge is the ring switch's last, one verifier message with its map challenges under their one grind
/// (`BATCH_GRINDING_BITS`).
fn verify_stacked_opening(
    transcript: &mut Transcript,
    root: Digest,
    stack_log: usize,
    log_inv_rate: usize,
    claims: &[StackClaim],
    batching: E,
) -> Result<(), VerifierError> {
    let values: Vec<E> = claims.iter().map(|(_, value)| *value).collect();
    require(claims.len() <= MAX_STACKED_CLAIMS, VerifierError::StackedClaims)?;
    let scales = powers(batching, claims.len());
    let evaluate_basis = |point: &[E]| {
        let weights: Vec<E> = claims.iter().map(|(weight, _)| weight(point)).collect();
        dot(&scales, &weights)
    };
    let target = dot(&scales, &values);
    verify_whir(transcript, stack_log, log_inv_rate, target, root, &evaluate_basis)
}

/// An OOD sample, read right after its commitment: a grind of `bits`, a point `z` of the committed variables, then the
/// committed multilinear at `z`. Level 0's claim follows every other stacked claim.
fn read_ood(transcript: &mut Transcript, vars: usize, bits: u32) -> Result<StackClaim<'static>, VerifierError> {
    transcript.grind_check(bits)?;
    let z = transcript.samples(vars);
    let value = transcript.next_scalar()?;
    Ok((Box::new(move |x| eq_eval(&z, x)), value))
}

/// A claim that a column's multilinear takes `value` at `point`.
struct ColumnClaim {
    column: usize,
    point: Vec<E>,
    value: E,
}

impl ColumnClaim {
    /// `None` for a column nothing commits, whose claim never reaches the stack.
    fn on_stack(&self, layout: &Layout) -> Option<StackClaim<'static>> {
        let point = layout.placements[self.column]?.stack_point(&self.point, layout.stack_log);
        Some((Box::new(move |x| eq_eval(&point, x)), self.value))
    }
}

/// What a walk of the proof leaves behind, for a prover that proves this verification in turn.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Summary {
    /// The announced sizes: the memory's log size and each table's row count.
    pub log_memory: usize,
    pub table_rows: Vec<u64>,
    pub log_inv_rate: usize,
    /// The stack's log size, the stacked opening's variables.
    pub stack_log: usize,
    /// Where the link splits the program, the index point's program coordinates `r[..log_bytecode]`: the split
    /// program there is the claim a child raises, which an aggregate's batching defers.
    pub bytecode_point: Vec<E>,
    /// The stream positions the Keccak reduction reads.
    pub keccak_scalars: Range<usize>,
    /// The stream positions of the link's index-side value at `r` (the memory term) and of the pointer columns'
    /// bit-slices.
    pub values_at_r: Range<usize>,
    pub bit_slices: Range<usize>,
}

/// Verify that `proof` shows an execution of `bytecode` (the stacked bytecode multilinear) on the 256-bit `public_input`.
pub fn verify_execution(bytecode: &Bytecode, public_input: &[u8; 32], proof: &Proof) -> Result<Summary, VerifierError> {
    walk(bytecode, public_input, proof, true)
}

/// NOT a verification: the [`Summary`] of `proof`, read out without checking it. An invalid proof is accepted.
///
/// For a prover that reads its guest's witness out of a proof the guest then verifies in full. It walks the same transcript as [`verify_execution`] and leaves out every check: the sumcheck, link, Keccak and WHIR terminal identities, the proof of work, the bytecode evaluation and the Merkle roots. It still fails on a proof it cannot walk: announced sizes out of range, a stream or openings of the wrong length or shape, a Merkle path at a position the protocol did not open.
pub fn replay_unchecked(bytecode: &Bytecode, public_input: &[u8; 32], proof: &Proof) -> Result<Summary, VerifierError> {
    walk(bytecode, public_input, proof, false)
}

/// Exposed for the Keccak reduction's benchmark and tests: a batch of `2^log_steps` permutations proved alone, a state
/// committed every `depth` rounds, the committed states the whole stack.
///
/// The proof is the commitment root and its OOD sample, the output lanes claimed at a challenge point, the reduction, then the ring
/// switch and its opening, as in an execution proof. Its public input is the shape, the words `log_steps`, `depth`,
/// `log_inv_rate` and zero, so a proof of one shape verifies for no other.
pub fn verify_keccak_batch(
    fiat_shamir_iv: &[u8; 32],
    log_steps: usize,
    depth: usize,
    log_inv_rate: usize,
    proof: &Proof,
) -> Result<(), VerifierError> {
    require(
        log_steps >= layout::KECCAK_MIN_STEPS_LOG && depth > 0 && ROUNDS.is_multiple_of(depth),
        VerifierError::CommittedSize,
    )?;
    let shape = KeccakShape { log_steps, depth };
    let Some(stack_log) = log_steps.checked_add(shape.slot_bits()) else {
        return Err(VerifierError::CommittedSize);
    };
    require(
        (MIN_STACKED_LOG..=MAX_STACKED_LOG).contains(&stack_log),
        VerifierError::CommittedSize,
    )?;
    let mut statement = [0u8; 32];
    for (bytes, word) in statement
        .as_chunks_mut::<8>()
        .0
        .iter_mut()
        .zip([log_steps, depth, log_inv_rate])
    {
        *bytes = (word as u64).to_le_bytes();
    }
    let mut transcript = Transcript::new(proof, Digest(*fiat_shamir_iv), Digest(statement), true);
    let halves = transcript.next_scalars(2)?;
    let root = Digest::from_halves(halves[0], halves[1]);
    let ood = read_ood(&mut transcript, stack_log, OOD_GRINDING_BITS)?;
    // The instance pins the committed middle states, a multilinear identity of degree `log_steps` in it.
    transcript.grind_check(grinding_bits(log_steps as u128))?;
    let instance = transcript.samples(log_steps);
    let output = transcript.next_scalars(STATE_LANES)?;
    let openings = verify_keccak(&mut transcript, shape, &instance, &output)?;
    let (point, slices) = openings.inputs;
    let piece = RingPiece {
        placement: None,
        point,
        scale: ONE,
    };
    let (ring, batching) = ring_switch(
        vec![RingClaim {
            pieces: vec![piece],
            slices,
        }],
        &mut transcript,
    )?;
    let mut claims: Vec<StackClaim> = vec![ring];
    if let Some((point, word)) = openings.outputs {
        claims.push((Box::new(move |x| eq_eval(&point, x)), word));
    }
    claims.push(ood);
    verify_stacked_opening(&mut transcript, root, stack_log, log_inv_rate, &claims, batching)?;
    transcript.finish()?;
    Ok(())
}

/// The protocol, in the order of `doc/leanvm` §sec:e2e-unrolled.
fn walk(bytecode: &Bytecode, public_input: &[u8; 32], proof: &Proof, checked: bool) -> Result<Summary, VerifierError> {
    let public_input = Digest(*public_input);
    let mut transcript = Transcript::new(proof, bytecode.fiat_shamir_iv, public_input, checked);

    // 1] memory log-size, table row counts, and log-inv-rate in WHIR
    let announced = transcript.next_scalars(2 + N_TABLES)?;
    require(
        announced.iter().all(|value| value.c1 == 0),
        VerifierError::AnnouncedHighLimb,
    )?;
    let log_memory = announced[0].c0;
    let table_rows: Vec<u64> = announced[1..1 + N_TABLES].iter().map(|value| value.c0).collect();
    let log_inverse_rate = announced[1 + N_TABLES].c0;
    require(
        (MIN_LOG_INV_RATE as u64..=MAX_LOG_INV_RATE as u64).contains(&log_inverse_rate),
        VerifierError::PcsInverseRate,
    )?;
    let layout = build_layout(bytecode, log_memory, &table_rows)?;
    require(
        (MIN_STACKED_LOG..=MAX_STACKED_LOG).contains(&layout.stack_log),
        VerifierError::CommittedSize,
    )?;

    // 2] parse WHIR commitment: one Merkle root (its OOD sample follows, outside the PCS).
    let halves = transcript.next_scalars(2)?;
    let root = Digest::from_halves(halves[0], halves[1]);
    let ood = read_ood(&mut transcript, layout.stack_log, OOD_GRINDING_BITS)?;

    // 3] The links: two chained sum-checks, over the index, then over the rows and the pointer columns. They leave each
    // table's other columns at its row point, a claim on the memory and the pointer columns' bit-slices.
    let link = verify_link(&layout, &mut transcript)?;
    let mut claims: Vec<ColumnClaim> = Vec::new();
    for (base, (point, values)) in GLOBAL_COLUMN_BASES.into_iter().zip(&link.columns) {
        claims.extend(values.iter().map(|&(local, value)| ColumnClaim {
            column: base + local,
            point: point.clone(),
            value,
        }));
    }

    // 4] binding the public input: each memory limb's claim is that limb's public line at the challenge, which the verifier
    // evaluates itself, so the prover sends nothing. A line: numerator one, no grind.
    let public_challenge = transcript.sample();
    let (first, second) = public_input.halves();
    let mut public_point = vec![ZERO; layout.placements[MEMORY_0].expect("memory is committed").variables];
    public_point[0] = public_challenge;
    let public_pairs = [(first.c0, second.c0), (first.c1, second.c1)];
    for (column, (low, high)) in [MEMORY_0, MEMORY_1].into_iter().zip(public_pairs) {
        claims.push(ColumnClaim {
            column,
            point: public_point.clone(),
            value: multilinear_eval(&[K(low), K(high)], &[public_challenge])?,
        });
    }

    // 5] KECCAK validity, by GKR over the rounds. The table's values on its output lanes are the reduction's claim on
    // the permutation's output: they leave the batch, their columns having no placement.
    let (point, values) = &link.columns[OP_KECCAK];
    let lanes: Vec<E> = (KECCAK_OUT..KECCAK_OUT + STATE_LANES)
        .map(|lane| {
            values
                .iter()
                .find(|&&(local, _)| local == lane)
                .map(|&(_, value)| value)
        })
        .collect::<Option<_>>()
        .expect("the output lanes are no pointers");
    let keccak_start = transcript.stream_offset();
    let openings = verify_keccak(&mut transcript, layout.keccak, point, &lanes)?;
    let keccak_scalars = keccak_start..transcript.stream_offset();
    if let Some((point, value)) = openings.outputs {
        claims.push(ColumnClaim {
            column: QKECCAK,
            point,
            value,
        });
    }

    // 6] Ring switching: the Keccak reduction's input slices on q_keccak, then the pointer columns' slices, as one
    // claim that leads the batch, then the memory term and the point claims.
    let (point, slices) = openings.inputs;
    let keccak_ring = RingClaim {
        pieces: vec![RingPiece {
            placement: Some(layout.placements[QKECCAK].expect("q_keccak is committed")),
            point,
            scale: ONE,
        }],
        slices,
    };
    let (ring, batching) = ring_switch(vec![keccak_ring, link.ring], &mut transcript)?;
    let mut stack_claims: Vec<StackClaim<'static>> = vec![ring];
    let (memory_point, memory_scales, memory_value) = link.memory;
    let memory_points: Vec<(Vec<E>, E)> = [MEMORY_0, MEMORY_1]
        .into_iter()
        .zip(memory_scales)
        .map(|(column, scale)| {
            let placement = layout.placements[column].expect("memory is committed");
            (placement.stack_point(&memory_point, layout.stack_log), scale)
        })
        .collect();
    stack_claims.push((
        Box::new(move |x| E::sum(memory_points.iter().map(|(point, scale)| *scale * eq_eval(point, x)))),
        memory_value,
    ));
    stack_claims.extend(claims.iter().filter_map(|claim| claim.on_stack(&layout)));
    stack_claims.push(ood);
    verify_stacked_opening(
        &mut transcript,
        root,
        layout.stack_log,
        log_inverse_rate as usize,
        &stack_claims,
        batching,
    )?;
    transcript.finish()?;
    Ok(Summary {
        log_memory: layout.log_memory,
        table_rows,
        log_inv_rate: log_inverse_rate as usize,
        stack_log: layout.stack_log,
        bytecode_point: link.bytecode_point,
        keccak_scalars,
        values_at_r: link.values_at_r,
        bit_slices: link.bit_slices,
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn grinding_bits_is_the_ceiling_log() {
        assert_eq!(
            [0, 1, 2, 8, 9, 31, 46, 64, 65, 1 << 20].map(grinding_bits),
            [0, 0, 0, 0, 1, 2, 3, 3, 4, 17]
        );
    }

    /// What lets all three verifiers check a plain range instead of re-deriving the ladder: every size in the window
    /// is configurable at every rate.
    #[test]
    fn supported_window_is_configurable() {
        for rate in MIN_LOG_INV_RATE..=MAX_LOG_INV_RATE {
            for mu in MIN_STACKED_LOG..=MAX_STACKED_LOG {
                assert!(derive_config(mu, rate).is_ok(), "mu={mu} rate={rate}");
            }
        }
    }

    #[test]
    fn verify_keccak_batch_rejects_overflowing_log_steps() {
        let proof = Proof::from_bytes(&[0u8; 8]).expect("empty proof decodes");
        assert_eq!(
            verify_keccak_batch(&[0; 32], usize::MAX, 12, MIN_LOG_INV_RATE, &proof),
            Err(VerifierError::CommittedSize)
        );
    }
}
