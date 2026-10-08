//! Recursion on the machine itself: the verifier of a leanVM proof as a RISC-V program, and trees of such programs.
//!
//! - [`program`]: the verifier recorded and lowered to a program, and the aggregation tree of two such programs.
//! - `claims`, `reduce`, `statement`: what a tree proof states, and the reduction of the claims a node's children leave.
//! - `hash`: BLAKE2s compressions on words, as the machine's instruction computes them.

pub(crate) mod claims;
pub(crate) mod hash;
pub mod program;
pub(crate) mod reduce;
pub(crate) mod statement;

use crate::cpu::{Announcement, DecodeError, Proof, Stats};
use crate::pcs::Rate;
use crate::tables::PerTable;
use fiat_shamir::transcript::RawProof;

pub use statement::Kind;

/// What a recorded verifier reads: the proof when it has one, zeros when it is built from the shape alone.
///
/// The program never depends on what is read, so both sources give one program.
#[derive(Clone, Copy, Debug)]
pub enum ProofSource<'a> {
    /// The proof, as its native verifier read it.
    Proof(&'a RawProof),
    /// No proof: every scalar and opening is zero.
    Shape,
}

/// The shape every leaf proof of a tree shares.
///
/// It is each table's height and the commitment's rate, as a proof announces them.
///
/// A tree's programs are built from it, so they verify leaves of that shape only.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct LeafShape {
    /// Each table's base-two logarithm of rows.
    pub(crate) taus: PerTable<usize>,
    /// The commitment's rate.
    pub(crate) rate: Rate,
}

impl LeafShape {
    /// The shape a proof announces.
    ///
    /// # Errors
    ///
    /// A proof whose announcement is not valid.
    pub fn of(proof: &Proof) -> Result<Self, DecodeError> {
        let scalars = (proof.0.stream.get(..Announcement::LEN))
            .and_then(|s| s.try_into().ok())
            .ok_or(DecodeError::Malformed)?;
        let announcement = Announcement::decode(scalars).map_err(|_| DecodeError::Malformed)?;
        Ok(Self {
            taus: announcement.taus,
            rate: announcement.rate,
        })
    }

    /// The shape a proof of a run would announce, from the run's measured cost.
    ///
    /// So a tree's programs are built before any leaf is proven.
    #[must_use]
    pub fn measured(stats: &Stats, rate: Rate) -> Self {
        // Every proven table height is a power of two, so its logarithm is exact.
        Self {
            taus: stats.counts.map(|rows| rows.ilog2() as usize),
            rate,
        }
    }
}
