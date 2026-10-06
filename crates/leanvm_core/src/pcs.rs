//! Witness commitment: an inner-product PCS committing over `K = F_{2^64}` and
//! opening over `E = F_{2^192}` (doc §sec:stacking, §annex:pcs), reusing flock's **WHIR**. An
//! opening proves `Σ_x q(x)·W(x) = C` against any verifier-evaluable `E`-valued
//! weight `W` (a point evaluation `q̂(r)` is `W = eq(r,·)`). A batch of claims
//! `q̂(point_j) = value_j` folds with random `γ`s into one weight and target,
//! opened in a single WHIR run: the verifier evaluates the weight itself,
//! so it never travels. flock's ring-switched `q_flock` claims join the same batch
//! ([`::pcs::stack_open`]).
//!
//! The stacked witness is `2^μ` words, but its tail past the placed columns is
//! zero, and the L0 interleaving makes that tail whole lanes: lane `l` is the
//! contiguous block `q[l·2^(μ-LOG_BATCH) ..)`, so only
//! [`crate::witness::StackShape::n_lanes`] of them are ever encoded, and the
//! opening's dense weight, its first `LOG_BATCH` rounds and the stack allocation
//! shrink with them. A leaf image is still `2^LOG_BATCH` words, the absent lanes
//! contributing the zeros their codeword would have been, but they LEAD the image:
//! their whole 64-byte blocks are one chaining value every leaf shares, so the
//! committer hashes them once rather than once per leaf, and only the image's tail
//! rides the proof. Both sides derive the lane count from the announced layout.
//!
//! Security: Johnson list decoding at every supported rate, `2^-1` to `2^-4`, with 128-bit round-by-round soundness.
//!
//! - L0 takes no OOD sample, so the commitment binds only to a list of polynomials (§annex:pcs).
//! - Every challenge drawn after the root and before the opening must hold against each of them, its error multiplied by the list size (§sec:e2e-ledger).
//! - Each deeper commitment takes one explicit OOD sample, which binds it to one codeword.
//! - The base-field commitment only shrinks the level-0 symbols to 8 bytes; every random ingredient is sampled from `E`.

use crate::witness::StackShape;
use ::pcs::stack_open::{open_batch_mixed_whir_stacked, verify_opening_batch_mixed_whir_stacked};
use ::pcs::whir::{self, ProverConfig, ProverData, WhirError, config_for_rate};
use fiat_shamir::transcript::{ProverState, Receiver, TranscriptError, Transmitter, VerifierState};
use primitives::field::F64;
use thiserror::Error;

pub use ::pcs::stack_open::{RingSwitch, SliceClaim, StackClaim};

/// Row-batch lanes `2^LOG_BATCH`: the Merkle leaf width (`2^LOG_BATCH` F64
/// = 512 bytes/leaf) IS WHIR's INITIAL folding factor: the L0 commit is
/// reused, so the two are one knob ([`::pcs::whir::INITIAL_FOLDING_FACTOR`]).
/// Larger ⇒ far fewer Merkle nodes to hash at the cost of fatter query openings.
pub(crate) const LOG_BATCH: usize = ::pcs::whir::INITIAL_FOLDING_FACTOR;

/// The commitment's rate, as the base-two logarithm of its inverse.
///
/// A larger value, a lower rate, makes a smaller proof and a slower prover.
///
/// Only a rate the commitment supports can be built, so the prover never checks one.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct Rate(u8);

const _: () = assert!(::pcs::whir::MAX_LOG_INV_RATE <= u8::MAX as usize);

impl Rate {
    /// The fastest prover, and the largest proof.
    pub const MIN: Self = Self(::pcs::whir::MIN_LOG_INV_RATE as u8);

    /// The smallest proof, and the slowest prover.
    pub const MAX: Self = Self(::pcs::whir::MAX_LOG_INV_RATE as u8);

    /// The rate `2^-log_inv_rate`.
    ///
    /// # Errors
    ///
    /// A rate the commitment does not support.
    pub const fn new(log_inv_rate: u8) -> Result<Self, InvalidRate> {
        if Self::MIN.0 <= log_inv_rate && log_inv_rate <= Self::MAX.0 {
            Ok(Self(log_inv_rate))
        } else {
            Err(InvalidRate { log_inv_rate })
        }
    }

    /// The base-two logarithm of the inverse rate.
    #[must_use]
    pub const fn log_inv_rate(self) -> u8 {
        self.0
    }
}

/// A rate the commitment does not support.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Error)]
#[error("log_inv_rate {log_inv_rate} is not in {min}..={max}", min = Rate::MIN.0, max = Rate::MAX.0)]
pub struct InvalidRate {
    /// The rejected value.
    pub log_inv_rate: u8,
}
// The PCS and the unground F192 bus argument both target `SECURITY_BITS`.
const _: () = assert!(::pcs::whir::SECURITY_BITS == crate::SECURITY_BITS as usize);
/// Minimum committed-witness log-size, the smallest the WHIR table configures.
pub const MIN_MU: usize = ::pcs::whir::MIN_LOG_N;
/// Largest committed size accepted by all verifiers, the largest the WHIR table configures.
pub const MAX_MU: usize = ::pcs::whir::MAX_LOG_N;

/// The shared WHIR config for a `2^μ`-word witness.
fn whir_config(mu: usize, log_inv_rate: usize) -> ProverConfig {
    config_for_rate(mu, log_inv_rate)
        .unwrap_or_else(|e| panic!("whir config for mu={mu}, log_inv_rate={log_inv_rate}: {e}"))
}

/// A committed `K`-valued witness plus the data needed to open it. The witness
/// itself is not retained (the caller still owns it and passes it back to
/// [`open`]), so committing costs no extra full-trace copy.
pub struct Committed {
    /// Codeword + Merkle tree retained for opening. Public so the single stacked
    /// WHIR opening (which also discharges flock's claim over
    /// this same commitment, §hash_flock) can reuse it.
    pub prover_data: ProverData,
    /// `log2` of the witness length in F64 words.
    pub mu: usize,
    /// L0 inverse-rate logarithm bound into the transcript before this commitment.
    pub log_inv_rate: usize,
}

/// Commit a `K`-valued witness of `2^μ` words (`μ ≥ MIN_MU`, from
/// [`crate::witness::placements_of`]) and bind its root into the transcript,
/// before any challenge is sampled. The verifier reads it with
/// [`read_commitment`].
///
/// `witness` is the stack truncated to the lane blocks that carry data
/// ([`crate::witness::StackShape::committed_len`]); the zero tail past them is
/// neither encoded nor hashed, and the resulting commitment is the same one the
/// full `2^μ` witness would have produced.
pub fn commit(ps: &mut ProverState, witness: &[F64], shape: StackShape, log_inv_rate: usize) -> Committed {
    let mu = shape.mu;
    assert!(
        mu >= MIN_MU,
        "witness must be ≥ 2^{MIN_MU} elements (padded by placements_of)"
    );
    assert_eq!(
        witness.len(),
        shape.committed_len(),
        "witness must be the committed lanes"
    );
    let (commitment, prover_data) = whir::commit(witness, mu, LOG_BATCH, log_inv_rate);
    ps.add_root(&commitment.root);
    Committed {
        prover_data,
        mu,
        log_inv_rate,
    }
}

// The batching challenges are just `sample()`d inside the stacked opener: every
// claim they combine is already bound: the values rode the stream
// (`add_scalar`) during the bus / constraint sub-protocols or, for the exit
// claims, are the seeded statement, the points are prior challenges or Boolean
// constants, and the offsets are public (reconstructed identically from the
// announced layout).

/// Verifier counterpart of [`commit`]'s root binding: read the committed root
/// from the stream at the start of verification, before sampling any challenge.
pub fn read_commitment(vs: &mut VerifierState) -> Result<[u8; 32], TranscriptError> {
    vs.next_root()
}

/// Open the committed witness: discharge the `points` (leanVM's bus / constraint /
/// exit claims, as block-sparse slot evaluations) AND flock's ring-switched
/// validity claims (`rings`, one per class) in ONE stacked WHIR.
/// The points become the opener's `point_claims`; the opening's Merkle data
/// rides the transcript's phase list, not the scalar stream. The commitment root
/// was already bound by [`commit`], and the point *values* either rode the
/// stream or are the statement, so nothing extra is bound here.
///
/// There is no plain (non-ring-switch) path: the witness ALWAYS carries a `q_flock`
/// sub-block (≥ 1 padding instance, §cpu), so every opening is stacked.
pub fn open(ps: &mut ProverState, c: &Committed, q: &[F64], points: &[StackClaim], rings: &[RingSwitch]) {
    let lane_block = 1usize << (c.mu - LOG_BATCH);
    assert_eq!(q.len() % lane_block, 0, "witness must be whole committed lanes");
    assert!(q.len() <= 1usize << c.mu, "witness must fit the announced size");
    let cfg = whir_config(c.mu, c.log_inv_rate);
    open_batch_mixed_whir_stacked(ps, c.mu, q, &c.prover_data, &cfg, points, rings);
}

/// Verify the opening (mirror of [`open`]): flock's ring-switched claim
/// and every `points` slot evaluation are checked together in the ONE stacked
/// WHIR against `root`, pulling its Merkle phases off the transcript.
pub fn verify(
    vs: &mut VerifierState,
    points: &[StackClaim],
    rings: &[RingSwitch],
    shape: StackShape,
    log_inv_rate: usize,
    root: &[u8; 32],
) -> Result<(), WhirError> {
    let cfg = whir_config(shape.mu, log_inv_rate);
    verify_opening_batch_mixed_whir_stacked(vs, &cfg, shape.mu, shape.n_lanes, root, points, rings)
}
