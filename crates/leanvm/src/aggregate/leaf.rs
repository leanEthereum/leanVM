//! A tree's leaves: the proofs it aggregates, and the shape they share.

use crate::{DecodeError, Output, Proof, ProvenRun, Rate, Stats};
use leanvm_core::rec::tree;

/// The shape every leaf proof of a tree shares.
///
/// It is each table's height and the commitment's rate, as a proof announces them.
///
/// A tree's circuits are built from it, so they verify leaves of that shape only.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct LeafShape(pub(super) tree::LeafShape);

impl LeafShape {
    /// The shape a proof announces.
    ///
    /// # Errors
    ///
    /// A proof whose announced heights or rate are not canonical.
    pub fn of(proof: &Proof) -> Result<Self, DecodeError> {
        tree::LeafShape::of(&proof.0).map(Self).ok_or(DecodeError::Malformed)
    }

    /// The shape a proof of a run would announce, from the run's measured cost.
    ///
    /// So a tree's key is built before any leaf is proven.
    #[must_use]
    pub fn measured(stats: &Stats, rate: Rate) -> Self {
        // Every proven table height is a power of two, so its logarithm is exact.
        let height_logs = stats.counts.map(|rows| rows.ilog2() as usize);
        Self(tree::LeafShape::new(height_logs, rate))
    }
}

/// One leaf of a tree: a proof, and the output it proves.
#[derive(Clone, Copy, Debug)]
pub struct Leaf<'a> {
    /// The proof of the run.
    proof: &'a Proof,
    /// The output the proof claims.
    output: Output,
}

impl<'a> Leaf<'a> {
    /// The leaf of a proof and the output it proves.
    #[must_use]
    pub const fn new(proof: &'a Proof, output: Output) -> Self {
        Self { proof, output }
    }

    /// The same leaf, as the recursion machine takes it.
    pub(super) const fn as_core(self) -> tree::Leaf<'a> {
        tree::Leaf::new(&self.proof.0, *self.output.words())
    }
}

impl<'a> From<&'a ProvenRun> for Leaf<'a> {
    fn from(run: &'a ProvenRun) -> Self {
        Self::new(&run.proof, run.output)
    }
}
