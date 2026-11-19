//! The VRF tree of the consensus specifications' `pq` feature, pruned to a range of slots.
//!
//! A validator registers the tree's root, and a block reveals its slot's proof, the leaf and its
//! 31 siblings, as its RANDAO reveal.
//!
//! ```text
//!     depth        31, one leaf per slot
//!     leaf i       Keccak-256(seed | i as 8 little-endian bytes), i in the range
//!     node         Keccak-256(left | right)
//!     surrogate    Keccak-256(seed | j as 8 little-endian bytes | h as 1 byte)
//!                  for the subtree at height h and index j holding no slot of the range
//! ```
//!
//! Nobody can open a surrogate, so a slot outside the range has no proof.

use std::ops::Range;

use lean_vrf::{verify_vrf_proof, VrfKey, VrfProof, VRF_TREE_DEPTH};

use crate::Error;

/// Byte length of a seed, the whole secret of a key.
pub const SEED_LEN: usize = 32;

/// Depth of a VRF tree: it has `2^TREE_DEPTH` leaves, one per slot.
pub const TREE_DEPTH: usize = 31;

/// Byte length of an encoded [`Proof`]: the leaf, then its 31 siblings.
pub const PROOF_LEN: usize = 32 * (TREE_DEPTH + 1);

/// A slot, the index of a leaf.
pub type Slot = u32;

/// The seed a tree is derived from.
pub type Seed = [u8; SEED_LEN];

/// A tree's root, the validator's VRF root.
pub type Root = [u8; 32];

/// The leaf of a slot, then its 31 siblings, bottom-up: the specifications' `VRFProof`.
pub type Proof = [[u8; 32]; TREE_DEPTH + 1];

// The sizes and types above are `lean_vrf`'s.
const _: () = assert!(TREE_DEPTH == VRF_TREE_DEPTH);
const _: fn(VrfProof) -> Proof = |proof| proof;

/// A seed, the range of slots its tree has leaves for, and a cached layer of the tree.
///
/// The seed and the range fix the root, so keep both. The cache is about `sqrt(R)` nodes for a
/// range of `R` slots. Its memory is not zeroized on drop.
#[derive(Clone, Debug)]
pub struct Key(VrfKey);

impl Key {
    /// The key of `seed` with leaves for `slots`, hashing every leaf of the range once.
    ///
    /// # Errors
    ///
    /// Fails when the range is empty or ends past `2^31`.
    pub fn new(seed: Seed, slots: Range<Slot>) -> Result<Self, Error> {
        let (start, end) = (slots.start, slots.end);
        VrfKey::new(seed, slots)
            .map(Self)
            .ok_or(Error::InvalidVrfRange { start, end })
    }

    /// The tree's root, the validator's VRF root.
    #[must_use]
    pub fn root(&self) -> Root {
        self.0.root()
    }

    /// The proof a block at `slot` reveals, hashing about `3 sqrt(R)` nodes.
    ///
    /// # Errors
    ///
    /// Fails when the slot is outside the key's range.
    pub fn proof(&self, slot: Slot) -> Result<Proof, Error> {
        self.0.proof(slot).ok_or(Error::VrfSlot { slot })
    }
}

/// Checks that `proof` opens the leaf of `slot` under `root`, as the consensus specifications'
/// `is_valid_vrf_proof` does: only the 31 low bits of the slot count.
///
/// # Errors
///
/// Fails, naming the slot, when the proof does not open under the root.
pub fn verify(root: &Root, slot: u64, proof: &Proof) -> Result<(), Error> {
    if verify_vrf_proof(root, slot, proof) {
        Ok(())
    } else {
        Err(Error::VrfVerify { slot })
    }
}
