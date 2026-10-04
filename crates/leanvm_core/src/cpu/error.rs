//! Why a run has no proof, why proof bytes decode to none, and why a proof does not verify.

use super::deferred::MalformedClaim;
use crate::constraints::ConstraintError;
use crate::leaf::BusError;
use crate::pcs;
use crate::pcs::Rate;
use crate::rv::Trap;
use crate::tables::Part;
use ::pcs::whir::WhirError;
use fiat_shamir::transcript::TranscriptError;
use flock::verifier::FlockError;
use thiserror::Error;

/// Why a run has no proof.
///
/// Every variant is a limit of the prover or a mistake of its caller, except a trap, which is the run's.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Error)]
pub enum ProveError {
    /// The run trapped.
    #[error(transparent)]
    Trap(#[from] Trap),
    /// The run is longer than one proof holds, in cycles or in committed words.
    #[error("the run is longer than one proof holds (continuations are not implemented)")]
    TooLong,
    /// More advice words than the program's region holds.
    #[error("the advice has {got} words, and the program's region holds {max}")]
    AdviceTooLong {
        /// The words the region holds.
        max: usize,
        /// The words supplied.
        got: usize,
    },
}

/// Why a proof does not verify, by the stage that refuses it.
#[derive(Clone, Debug, PartialEq, Eq, Error)]
#[non_exhaustive]
pub enum CpuError {
    /// An announced size is not a canonical integer.
    #[error("an announced size is not a canonical integer")]
    NonCanonicalSize,
    /// A table's announced height is outside what the arithmetization expresses.
    #[error("the {table} table announces 2^{log_rows} rows, outside 2^{min}..=2^{max}")]
    TableHeight {
        /// The table.
        table: &'static str,
        /// The announced base-two logarithm of rows.
        log_rows: usize,
        /// The least height the table can have.
        min: usize,
        /// The greatest height any table can have.
        max: usize,
    },
    /// The announced rate is one the commitment does not support.
    #[error("the announced log_inv_rate {log_inv_rate} is not in {min}..={max}", min = Rate::MIN.log_inv_rate(), max = Rate::MAX.log_inv_rate())]
    Rate {
        /// The announced base-two logarithm of the inverse rate.
        log_inv_rate: usize,
    },
    /// The announced final clock is not live: bit 40 alone above the cycle, and slot zero.
    #[error("the announced final clock is not a live clock")]
    FinalClock,
    /// The announced heights stack to a witness the commitment does not take.
    #[error("the witness has 2^{mu} words, outside 2^{min}..=2^{max}", min = pcs::MIN_MU, max = pcs::MAX_MU)]
    WitnessSize {
        /// The stack's base-two logarithm of words.
        mu: usize,
    },
    /// The proof stream is malformed.
    #[error(transparent)]
    Transcript(#[from] TranscriptError),
    /// The memory and lookup bus does not balance.
    #[error("the bus: {0}")]
    Bus(BusError),
    /// The table constraints do not hold.
    #[error("the table constraints: {0}")]
    Constraint(ConstraintError),
    /// One of a table's circuit proofs is rejected.
    #[error("the {table} table's {part:?} circuit: {error}")]
    Flock {
        /// The table.
        table: &'static str,
        /// Which of its two circuits.
        part: Part,
        /// Why flock rejects it.
        error: FlockError,
    },
    /// The commitment opening is rejected.
    #[error("the opening: {0}")]
    Open(WhirError),
    /// A deferred claim has no shape a proof of the program gives.
    #[error("the deferred claims: {0}")]
    MalformedClaim(MalformedClaim),
}

/// Why bytes decode to no proof.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Error)]
#[non_exhaustive]
pub enum DecodeError {
    /// The bytes are no proof.
    ///
    /// The header is foreign or cut short, or the body is not exactly one proof.
    #[error("the bytes are no proof")]
    Malformed,

    /// A proof of another protocol version.
    #[error("a proof of protocol version {found}, and this verifier reads version {expected}")]
    UnsupportedVersion {
        /// The version the bytes announce.
        found: u16,
        /// The version this build reads.
        expected: u16,
    },
}

/// Why a proof does not verify.
///
/// The message names the verifier's stage that refused it, for a human to read.
///
/// A caller only needs to know that the proof is refused.
#[derive(Clone, Debug, PartialEq, Eq, Error)]
#[error("the proof does not verify: {0}")]
pub struct VerifyError(#[from] pub(crate) CpuError);
