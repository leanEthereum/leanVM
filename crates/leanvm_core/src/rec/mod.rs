//! The recursion machine: a circuit of rows over six tables, wired by copy cycles, and its proof (Annex E).

mod bus;
pub mod circuit;
mod clean;
mod fixed;
mod hash;
mod layout;
pub mod proof;
pub mod table;
pub mod transcript;
pub mod tree;
pub mod verifier;

pub(crate) use fixed::FixedColumn;

use crate::bus::BusError;
use crate::constraints::ConstraintError;
use fiat_shamir::TranscriptError;
use flock::FlockError;
use layout::RecLayout;
use pcs::whir::WhirError;
use table::Table;
use thiserror::Error;

/// Why a proof of the recursion machine is refused, or cannot be made.
#[derive(Clone, Debug, PartialEq, Eq, Error)]
pub enum RecError {
    /// The statement does not have the circuit's number of words.
    #[error("the statement has {got} words, and the circuit exposes {expected}")]
    StatementLength { expected: usize, got: usize },
    /// The witness does not fit one commitment.
    #[error("the witness has 2^{mu} words, more than one commitment holds (2^{max})", max = crate::commitment::MAX_MU)]
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
