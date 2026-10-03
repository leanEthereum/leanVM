//! Why a run has no proof, and why a proof does not verify.

use crate::constraints;
use crate::leaf;
use crate::pcs;
use crate::rv;

/// Why a run has no proof.
///
/// Every variant is a limit of the prover or a mistake of its caller, except a trap, which is the run's.
#[derive(Clone, Copy, Debug, PartialEq, Eq, thiserror::Error)]
pub enum ProveError {
    /// The run trapped.
    #[error(transparent)]
    Trap(#[from] rv::Trap),
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
#[derive(Clone, Debug, PartialEq, Eq, thiserror::Error)]
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
    #[error("the announced log_inv_rate {log_inv_rate} is not in {min}..={max}", min = pcs::Rate::MIN.log_inv_rate(), max = pcs::Rate::MAX.log_inv_rate())]
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
    Transcript(#[from] fiat_shamir::transcript::Error),
    /// The memory and lookup bus does not balance.
    #[error("the bus: {0}")]
    Bus(leaf::Error),
    /// The table constraints do not hold.
    #[error("the table constraints: {0}")]
    Constraint(constraints::Error),
    /// The circuits' batched proof is rejected.
    #[error("the circuits' reductions: {0}")]
    Flock(flock::verifier::VerifyError),
    /// The commitment opening is rejected.
    #[error("the opening: {0}")]
    Open(::pcs::whir::VerifyError),
}
