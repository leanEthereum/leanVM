//! The shapes a tree is built from: its RISC-V leaf proofs', its arities and rate, and a claim-set tree's capacities.

use super::design::SMALL;
use super::{Capacity, TreeError};
use crate::commitment::Rate;
use crate::cpu::{Announcement, DecodeError, Proof, ProofKind, Stats};
use crate::tables::{N_TABLES, PerTable};
use fiat_shamir::FromNarg;
use primitives::field::F192;

/// The shape every RISC-V leaf proof of a tree shares.
///
/// It is each table's height, the commitment's rate and whether the proofs are zero knowledge, as a proof announces
/// them.
///
/// A tree's circuits are built from it, so they verify leaves of that shape only.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct LeafShape {
    /// Each table's base-two logarithm of rows.
    taus: PerTable<usize>,
    /// The commitment's rate.
    rate: Rate,
    /// The leaf proofs' kind.
    kind: ProofKind,
}

/// How a tree is shaped; what its leaves are is its leaf family's (`Leaves`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct TreeShape {
    /// The leaf proofs a first-level node verifies, at least one.
    pub arity_0: usize,
    /// The tree proofs a higher node verifies, at least two: the only arity of a tree of outputs, the largest of a
    /// claim-set tree.
    pub arity: usize,
    /// The commitment rate of every tree proof.
    pub rate: Rate,
    /// A claim-set tree's capacities; none for a tree of outputs.
    pub claims: Option<ClaimShape>,
}

/// The capacities of a claim-set tree.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ClaimShape {
    /// The capacity of the tree's largest nodes and of a root's set: a node's children's sets together and its own set
    /// stay within it.
    pub capacity: Capacity,
    /// The small tier: nodes of at most its arity, whose sets stay within its capacity, at heights of their own. With
    /// none, every circuit is at the largest node's heights.
    pub small: Option<Tier>,
}

/// A claim-set tree's small tier: its first level, its nodes, and the wrap of its large proofs.
///
/// Its circuits have heights of their own, which its nodes' few children and small unions fix, so a proof of a small
/// set never pays for the tree's largest node. The large tier's nodes verify small proofs, and a large proof is
/// combined further once wrapped: one small proof verifying it and stating its set.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Tier {
    /// The most children its nodes verify, at least two and at most the tree's arity.
    pub arity: usize,
    /// The capacity of its nodes' unions and of its first level's, within the tree's.
    pub capacity: Capacity,
}

impl LeafShape {
    /// The shape of proofs with these table heights at this rate.
    pub(crate) const fn new(taus: PerTable<usize>, rate: Rate, kind: ProofKind) -> Self {
        Self { taus, rate, kind }
    }

    /// The same shape, of zero-knowledge proofs.
    #[must_use]
    pub const fn zero_knowledge(self) -> Self {
        Self {
            kind: ProofKind::ZeroKnowledge,
            ..self
        }
    }

    /// Each table's base-two logarithm of rows.
    pub(crate) const fn taus(&self) -> &PerTable<usize> {
        &self.taus
    }

    /// The commitment's rate.
    pub(crate) const fn rate(&self) -> Rate {
        self.rate
    }

    /// The leaf proofs' kind.
    pub(crate) const fn kind(&self) -> ProofKind {
        self.kind
    }

    /// Whether the leaf proofs are zero knowledge.
    #[must_use]
    pub fn is_zero_knowledge(&self) -> bool {
        self.kind == ProofKind::ZeroKnowledge
    }

    /// The shape a proof announces.
    ///
    /// # Errors
    ///
    /// A proof whose announcement is not valid.
    pub fn of(proof: &Proof) -> Result<Self, DecodeError> {
        Self::announced(proof).ok_or(DecodeError::Malformed)
    }

    /// The shape a proof of a run would announce, from the run's measured cost.
    ///
    /// So a tree's key is built before any leaf is proven.
    #[must_use]
    pub fn measured(stats: &Stats, rate: Rate) -> Self {
        // Every proven table height is a power of two, so its logarithm is exact.
        Self::new(stats.counts.map(|rows| rows.ilog2() as usize), rate, ProofKind::Plain)
    }

    /// The shape a proof's first scalars announce, if they are a valid announcement.
    ///
    /// A zero-knowledge proof announces its heights and rate alone: its final clock is hidden.
    pub(super) fn announced(proof: &Proof) -> Option<Self> {
        let mut narg = proof.0.narg.as_slice();
        if proof.is_zero_knowledge() {
            let scalars: [F192; N_TABLES + 1] = std::array::from_fn(|_| F192::from_narg(&mut narg).unwrap_or_default());
            let (taus, rate) = Announcement::decode_shape(&scalars).ok()?;
            return Some(Self::new(taus, rate, ProofKind::ZeroKnowledge));
        }
        let scalars: [F192; Announcement::LEN] =
            std::array::from_fn(|_| F192::from_narg(&mut narg).unwrap_or_default());
        let announcement = Announcement::decode(&scalars).ok()?;
        Some(Self::new(announcement.taus, announcement.rate, ProofKind::Plain))
    }
}

impl TreeShape {
    /// Nothing, if the shape makes a tree.
    ///
    /// # Errors
    ///
    /// - Arities that make no tree: a first level of no leaf, or nodes of fewer than two children.
    /// - A small tier past the tree's.
    pub(super) fn check(&self) -> Result<(), TreeError> {
        let Self {
            arity_0, arity, claims, ..
        } = *self;
        if arity_0 == 0 || arity < 2 {
            return Err(TreeError::Arity { arity_0, arity });
        }
        if let Some(ClaimShape {
            capacity: large,
            small: Some(Tier { arity: a, capacity }),
        }) = claims
            && (!(2..=arity).contains(&a) || capacity.claims > large.claims || capacity.groups > large.groups)
        {
            return Err(TreeError::SmallTier { arity: a, capacity });
        }
        Ok(())
    }

    /// The levels of nodes of the balanced tree over this many leaves: zero for a first-level node over `n_0`, `d` over
    /// `n_0 n^d`.
    ///
    /// # Errors
    ///
    /// A number of leaves no tree of these arities has.
    pub fn depth(&self, leaves: usize) -> Result<usize, TreeError> {
        let Self { arity_0, arity, .. } = *self;
        let count = TreeError::LeafCount { leaves, arity_0, arity };
        if leaves == 0 || arity_0 == 0 || arity < 2 || !leaves.is_multiple_of(arity_0) {
            return Err(count);
        }
        let (mut nodes, mut depth) = (leaves / arity_0, 0);
        while nodes > 1 && nodes.is_multiple_of(arity) {
            nodes /= arity;
            depth += 1;
        }
        if nodes == 1 { Ok(depth) } else { Err(count) }
    }
}

impl ClaimShape {
    /// One tier at the tree's capacity: every circuit at the largest node's heights.
    #[must_use]
    pub const fn new(capacity: Capacity) -> Self {
        Self { capacity, small: None }
    }

    /// The capacity of a tier's unions.
    pub(crate) const fn tier_capacity(&self, tier: usize) -> Capacity {
        match (tier, self.small) {
            (SMALL, Some(small)) => small.capacity,
            _ => self.capacity,
        }
    }

    /// The tiers it has.
    pub(super) const fn tiers(&self) -> usize {
        if self.small.is_some() { 2 } else { 1 }
    }
}
