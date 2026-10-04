//! Why a proof of the recursion machine is refused, or cannot be made.

use super::layout::RecLayout;
use super::table::Table;
use crate::constraints;
use crate::leaf;
use crate::pcs;

/// Why a proof of the recursion machine is refused, or cannot be made.
#[derive(Clone, Debug, PartialEq, Eq, thiserror::Error)]
pub enum RecError {
    /// The statement does not have the circuit's number of words.
    #[error("the statement has {got} words, and the circuit exposes {expected}")]
    StatementLength { expected: usize, got: usize },
    /// The witness does not fit one commitment.
    #[error("the witness has 2^{mu} words, more than one commitment holds (2^{max})", max = pcs::MAX_MU)]
    TooLong { mu: usize },
    /// A table has more rows than a slot's key can name.
    #[error("table {table:?} has 2^{tau} rows, more than 2^{max}", max = RecLayout::MAX_TAU)]
    TooManyRows { table: Table, tau: usize },
    /// The proof stream is malformed.
    #[error(transparent)]
    Transcript(#[from] fiat_shamir::transcript::TranscriptError),
    /// The bus does not balance.
    #[error(transparent)]
    Bus(#[from] leaf::BusError),
    /// The table sumcheck refuses.
    #[error(transparent)]
    Constraint(#[from] constraints::ConstraintError),
    /// Flock refuses the hash rows.
    #[error(transparent)]
    Flock(#[from] flock::verifier::FlockError),
    /// The opening refuses.
    #[error(transparent)]
    Open(#[from] ::pcs::whir::WhirError),
}
