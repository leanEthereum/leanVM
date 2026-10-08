//! Why a proof of the recursion machine is refused, or cannot be made.

use super::layout::RecLayout;
use super::table::Table;
use crate::constraints::ConstraintError;
use crate::leaf::BusError;
use crate::pcs;
use ::pcs::whir::WhirError;
use fiat_shamir::transcript::TranscriptError;
use flock::FlockError;
use thiserror::Error;

/// Why a proof of the recursion machine is refused, or cannot be made.
#[derive(Clone, Debug, PartialEq, Eq, Error)]
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
    Transcript(#[from] TranscriptError),
    /// The bus does not balance.
    #[error(transparent)]
    Bus(#[from] BusError),
    /// The table sumcheck refuses.
    #[error(transparent)]
    Constraint(#[from] ConstraintError),
    /// Flock refuses the hash rows.
    #[error(transparent)]
    Flock(#[from] FlockError),
    /// The opening refuses.
    #[error(transparent)]
    Open(#[from] WhirError),
}
