//! A self-contained verifier for leanVM execution proofs: single threaded, std only, plain integer arithmetic.
//!
//! A port of `python-verifier/verifier.py`, kept close enough to read side by side: the same functions, in the same order, with the same constants.
//!
//! What the Python has no counterpart for sits in modules of its own: the prepared [`Bytecode`], the pruned Merkle openings a proof travels with (`merkle`), what the statement of an aggregate adds, [`deferred`] and [`da`], and [`binary_spartan`], a standalone proof of Clean GF(2) circuits built on the same flock reduction and PCS.
//!
//! One walk of the protocol serves two entry points. [`verify_execution`] checks the proof. [`replay_unchecked`] reads the same [`Summary`] out of it and checks nothing: every check it leaves out is behind `Transcript::checked`.

#![forbid(unsafe_code)]

pub mod binary_spartan;
mod bus;
mod bytecode;
pub mod da;
pub mod deferred;
mod field;
mod flock;
mod hash;
mod layout;
mod merkle;
mod multilinear;
mod transcript;
mod whir;

pub use bytecode::Bytecode;
pub use field::{E, K};
pub use flock::FlockClaims;
pub use layout::gpow;
pub use merkle::{MerkleOpenings, MerklePath, PrunedMerklePaths};
pub use transcript::Proof;

use bus::{ColumnClaim, table_sumcheck, verify_bus_balance};
use field::{ZERO, powers};
use flock::{ring_switch, verify_flock};
use hash::Digest;
use layout::{
    BLAKE2S_R1CS_LOG_SIZE, FLOCK_K_SKIP, MAX_STACKED_LOG, MEMORY_0, MEMORY_1, MEMORY_2, MIN_STACKED_LOG, N_TABLES,
    OP_BLAKE2S, QFLOCK, build_layout,
};
use multilinear::{dot, multilinear_eval};
use transcript::Transcript;
use whir::verify_whir;

/// Why a proof was rejected.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum VerifierError {
    FieldElementLength,
    DigestHalf,
    MultilinearSize,
    NotPowerOfTwo,
    StreamNotWholeElements,
    StreamExhausted,
    GrindingNonce,
    MerkleOpeningMissing,
    MerkleOpeningShape,
    MerkleRootMismatch,
    StreamNotConsumed,
    MerkleNotConsumed,
    /// The GKR layer whose children do not match its sumcheck.
    GkrLayer(usize),
    BusCountZero,
    TableSumcheckTerminal,
    AnnouncedTableSizes,
    WhirShape,
    QueryCountLadder,
    InducedBasisDimensions,
    WhirTerminal,
    WhirNoTerminalLevel,
    FlockLincheckTerminal,
    AnnouncedHighLimb,
    PcsInverseRate,
    CommittedSize,
    /// Binary Spartan's public words are malformed: no instance, a partial instance, an unset constant or a set padding bit.
    PublicWords,
    SparkSumcheck,
    SparkMemoryCheck,
}

impl std::fmt::Display for VerifierError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let message = match self {
            Self::FieldElementLength => "a field element must contain exactly 24 bytes",
            Self::DigestHalf => "a digest half is 128-bit",
            Self::MultilinearSize => "multilinear table has the wrong size",
            Self::NotPowerOfTwo => "expected a power of two",
            Self::StreamNotWholeElements => "the stream is not a whole number of field elements",
            Self::StreamExhausted => "proof stream exhausted",
            Self::GrindingNonce => "invalid grinding nonce",
            Self::MerkleOpeningMissing => "Merkle opening missing",
            Self::MerkleOpeningShape => "Merkle opening has the wrong shape",
            Self::MerkleRootMismatch => "Merkle root mismatch",
            Self::StreamNotConsumed => "proof stream not fully consumed",
            Self::MerkleNotConsumed => "Merkle openings not fully consumed",
            Self::GkrLayer(layer) => return write!(f, "GKR layer {layer}: children do not match the sumcheck"),
            Self::BusCountZero => "a bus count is zero",
            Self::TableSumcheckTerminal => "table sumcheck terminal mismatch",
            Self::AnnouncedTableSizes => "invalid announced table sizes",
            Self::WhirShape => "invalid WHIR shape",
            Self::QueryCountLadder => "tabulated query count does not match the ladder",
            Self::InducedBasisDimensions => "bad induced-basis dimensions",
            Self::WhirTerminal => "WHIR terminal check failed",
            Self::WhirNoTerminalLevel => "WHIR verification ended without a terminal level",
            Self::FlockLincheckTerminal => "Flock lincheck terminal mismatch",
            Self::AnnouncedHighLimb => "announced size has a nonzero high limb",
            Self::PcsInverseRate => "invalid PCS inverse rate",
            Self::CommittedSize => "committed size outside the PCS window",
            Self::PublicWords => "malformed public words",
            Self::SparkSumcheck => "SPARK sumcheck terminal mismatch",
            Self::SparkMemoryCheck => "SPARK memory-checking leaf mismatch",
        };
        f.write_str(message)
    }
}

impl std::error::Error for VerifierError {}

fn require(condition: bool, error: VerifierError) -> Result<(), VerifierError> {
    if condition { Ok(()) } else { Err(error) }
}

/// The weight a claim puts on the stack, and the value it claims for it.
type StackClaim<'a> = (Box<dyn Fn(&[E]) -> E + 'a>, E);

/// Discharge every claim on the committed stack in one opening: the same powers of one challenge
/// batch the values into the target, and the weights into the basis WHIR evaluates at its terminal point.
fn verify_stacked_opening(
    transcript: &mut Transcript,
    root: Digest,
    stack_log: usize,
    placed: u64,
    log_inv_rate: usize,
    claims: &[StackClaim],
) -> Result<(), VerifierError> {
    let values: Vec<E> = claims.iter().map(|(_, value)| *value).collect();
    let scales = powers(transcript.sample(), claims.len());
    let evaluate_basis = |point: &[E]| {
        let weights: Vec<E> = claims.iter().map(|(weight, _)| weight(point)).collect();
        dot(&scales, &weights)
    };
    let target = dot(&scales, &values);
    verify_whir(
        transcript,
        stack_log,
        placed,
        log_inv_rate,
        target,
        root,
        &evaluate_basis,
    )
}

/// What a walk of the proof leaves behind, for a prover that proves this verification in turn.
///
/// With the proof's own stream, which the walk reads whole, it is the proof in the form the recursion guest and the Python verifier consume.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Summary {
    pub log_inv_rate: usize,
    /// Where the bus reads the stacked bytecode. Its value there is the claim an aggregate defers.
    pub bytecode_point: Vec<E>,
    pub flock: FlockClaims,
    /// The stream cursor just after flock's reduction, where the stacked opening's own scalars start.
    pub flock_stream_end: usize,
    /// One opening per query, in the order the walk read them.
    pub merkle_paths: Vec<MerklePath>,
}

/// Verify that `proof` shows an execution of `bytecode` (the stacked bytecode multilinear) on the 256-bit `public_input`.
pub fn verify_execution(bytecode: &Bytecode, public_input: &[u8; 32], proof: &Proof) -> Result<Summary, VerifierError> {
    walk(bytecode, public_input, proof, true)
}

/// NOT a verification: the [`Summary`] of `proof`, read out without checking it. An invalid proof is accepted.
///
/// For a prover that reads its guest's witness out of a proof the guest then verifies in full. It walks the same transcript as [`verify_execution`] and leaves out every check: the sumcheck, GKR, constraint, flock lincheck and WHIR terminal identities, the bus count's nonzero check, the proof of work, the bytecode evaluation and the Merkle roots. It still fails on a proof it cannot walk: announced sizes out of range, a stream or openings of the wrong length or shape.
pub fn replay_unchecked(bytecode: &Bytecode, public_input: &[u8; 32], proof: &Proof) -> Result<Summary, VerifierError> {
    walk(bytecode, public_input, proof, false)
}

/// Exposed for flock's benchmark: a batch of BLAKE2s compressions proved alone, the packed witness the whole committed stack.
///
/// The proof is the commitment root, flock's reduction, then the ring switch and its opening, as in an execution proof.
pub fn verify_flock_batch(
    fiat_shamir_iv: &[u8; 32],
    public_input: &[u8; 32],
    log_n: usize,
    log_inv_rate: usize,
    proof: &Proof,
) -> Result<FlockClaims, VerifierError> {
    let stack_log = log_n.checked_sub(FLOCK_K_SKIP).ok_or(VerifierError::CommittedSize)?;
    require(
        log_n >= BLAKE2S_R1CS_LOG_SIZE && (MIN_STACKED_LOG..=MAX_STACKED_LOG).contains(&stack_log),
        VerifierError::CommittedSize,
    )?;
    let mut transcript = Transcript::new(proof, Digest(*fiat_shamir_iv), Digest(*public_input), true);
    let halves = transcript.next_scalars(2)?;
    let root = Digest::from_halves(halves[0], halves[1])?;
    let claims = verify_flock(log_n, &mut transcript)?;
    let (target, weight) = ring_switch(claims.point(), &claims.s, &mut transcript);
    let ringswitch: StackClaim = (Box::new(weight), target);
    verify_stacked_opening(
        &mut transcript,
        root,
        stack_log,
        1 << stack_log,
        log_inv_rate,
        &[ringswitch],
    )?;
    transcript.finish()?;
    Ok(claims)
}

fn walk(bytecode: &Bytecode, public_input: &[u8; 32], proof: &Proof, checked: bool) -> Result<Summary, VerifierError> {
    let public_input = Digest(*public_input);
    let mut transcript = Transcript::new(proof, bytecode.fiat_shamir_iv, public_input, checked);

    // 1] memory log-size, table log-size, and log-inv-rate in WHIR
    let announced = transcript.next_scalars(2 + N_TABLES)?;
    require(
        announced.iter().all(|value| value.c1 == 0 && value.c2 == 0),
        VerifierError::AnnouncedHighLimb,
    )?;
    let log_memory = announced[0].c0;
    let table_logs: Vec<u64> = announced[1..1 + N_TABLES].iter().map(|value| value.c0).collect();
    let log_inverse_rate = announced[1 + N_TABLES].c0;
    require((1..=4).contains(&log_inverse_rate), VerifierError::PcsInverseRate)?;
    let layout = build_layout(bytecode, log_memory, &table_logs)?;
    require(
        (MIN_STACKED_LOG..=MAX_STACKED_LOG).contains(&layout.stack_log),
        VerifierError::CommittedSize,
    )?;

    // 2] parse WHIR commitment: one Merkle root (No OOD, our PCS is only List-binding).
    let halves = transcript.next_scalars(2)?;
    let root = Digest::from_halves(halves[0], halves[1])?;

    // 3] Bus: one batched GKR over the push, pull and count trees, then the leaf decomposition, which leaves each table a degree-2 claim.
    let bus = verify_bus_balance(&layout, &mut transcript)?;

    // 4] One batched (back-loaded) "table sumcheck" over all six tables, at the bus point, proving the target the three
    // leaf claims derive and that constraints vanish. Every table takes a disjoint range of xi powers for its constraints
    let xi = transcript.sample();
    let n_constraints: usize = layout.tables.iter().map(|table| table.n_constraints()).sum();
    let xi_powers = powers(xi, n_constraints + 3); // one power per constraint, then one per bus side, shared by every table
    let (constraint_powers, form_powers) = xi_powers.split_at(n_constraints);
    let target = dot(form_powers, &bus.totals);
    let table_sumcheck_claims = table_sumcheck(
        &layout.tables,
        &layout.table_log_heights,
        &bus.forms,
        constraint_powers,
        form_powers,
        &bus.point,
        target,
        &mut transcript,
    )?;
    let mut claims = bus.claims;
    claims.extend(table_sumcheck_claims);

    // 5] binding the public input: each memory limb's claim is that limb's public line at the challenge, which the verifier
    // evaluates itself, so the prover sends nothing. Both public words are 128-bit, so the top limb's claim is zero.
    let public_challenge = transcript.sample();
    let (first, second) = public_input.halves();
    let mut public_point = vec![ZERO; layout.placements[MEMORY_0].variables];
    public_point[0] = public_challenge;
    let public_pairs = [(first.c0, second.c0), (first.c1, second.c1), (first.c2, second.c2)];
    for (column, (low, high)) in [MEMORY_0, MEMORY_1, MEMORY_2].into_iter().zip(public_pairs) {
        claims.push(ColumnClaim {
            column,
            point: public_point.clone(),
            value: multilinear_eval(&[K(low), K(high)], &[public_challenge])?,
        });
    }

    // 6] BLAKE2s validity via Flock
    let flock_log_n = BLAKE2S_R1CS_LOG_SIZE + layout.table_log_heights[OP_BLAKE2S];
    let flock = verify_flock(flock_log_n, &mut transcript)?;
    let flock_stream_end = transcript.stream_offset();

    // 7] Ring-switching
    let (ringswitch_target, ringswitch_weight) = ring_switch(flock.point(), &flock.s, &mut transcript);
    // That claim is supported on q_flock's region of the stack, so its weight carries the
    // placement's selector, and it leads the batch, taking the first power.
    let qflock = layout.placements[QFLOCK];
    let ringswitch: StackClaim = (
        Box::new(|x| qflock.eq_above(x) * ringswitch_weight(&x[..qflock.variables])),
        ringswitch_target,
    );
    let mut stack_claims = vec![ringswitch];
    stack_claims.extend(claims.iter().map(|claim| claim.on_stack(&layout)));
    verify_stacked_opening(
        &mut transcript,
        root,
        layout.stack_log,
        layout.placed,
        log_inverse_rate as usize,
        &stack_claims,
    )?;
    Ok(Summary {
        log_inv_rate: log_inverse_rate as usize,
        bytecode_point: bus.bytecode_point,
        flock,
        flock_stream_end,
        merkle_paths: transcript.finish()?,
    })
}
