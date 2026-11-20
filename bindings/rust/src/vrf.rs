//! The VRF tree of the consensus `pq` feature, pruned to a range of slots.
//!
//! A validator registers the root; a block reveals its slot's proof as its RANDAO reveal. The
//! tree has depth 31, one leaf per slot (`i` and `j` as 8 little-endian bytes, `h` as 1 byte):
//!
//! ```text
//!     secret i     Keccak-256("VRF_SECRET" | seed | i), for i in the range
//!     leaf i       Keccak-256("VRF_LEAF" | secret i | i)
//!     node         Keccak-256(left | right)
//!     surrogate    Keccak-256("VRF_SURROGATE" | seed | j | h), for a subtree at height h,
//!                  index j, with no slot of the range; nobody can open it
//! ```

use std::ops::Range;

use lean_vrf::{verify_vrf_proof, VrfKey, VrfProof, VRF_TREE_DEPTH};

use crate::Error;

/// Byte length of a seed, the whole secret of a key.
pub const SEED_LEN: usize = 32;

/// Depth of the tree: `2^TREE_DEPTH` slots.
pub const TREE_DEPTH: usize = 31;

/// Byte length of a [`Proof`].
pub const PROOF_LEN: usize = 32 * (TREE_DEPTH + 1);

/// A slot, the index of a leaf.
pub type Slot = u32;

/// The seed a tree is derived from.
pub type Seed = [u8; SEED_LEN];

/// A tree's root, the validator's VRF root.
pub type Root = [u8; 32];

/// A slot's secret, then its leaf's 31 siblings: the specifications' `VRFProof`.
pub type Proof = [[u8; 32]; TREE_DEPTH + 1];

// The sizes and types above are `lean_vrf`'s.
const _: () = assert!(TREE_DEPTH == VRF_TREE_DEPTH);
const _: fn(VrfProof) -> Proof = |proof| proof;

/// A seed, its range of slots, and one cached layer of its tree, about `sqrt(R)` nodes for `R`
/// slots.
///
/// The seed and the range fix the root: keep both. Memory is not zeroized on drop.
#[derive(Clone, Debug)]
pub struct Key(VrfKey);

impl Key {
    /// Builds the key, hashing every slot of the range.
    ///
    /// # Errors
    ///
    /// Fails if the range is empty or ends past `2^31`.
    pub fn new(seed: Seed, slots: Range<Slot>) -> Result<Self, Error> {
        let (start, end) = (slots.start, slots.end);
        VrfKey::new(seed, slots)
            .map(Self)
            .ok_or(Error::InvalidVrfRange { start, end })
    }

    /// Rebuilds a key from its seed, its root and a cache from [`Self::cache_to_bytes`], without
    /// hashing the range.
    ///
    /// # Errors
    ///
    /// Fails if the cache is malformed or does not lead to `root`.
    pub fn from_cache_bytes(seed: Seed, root: &Root, cache: &[u8]) -> Result<Self, Error> {
        VrfKey::from_cache_bytes(seed, root, cache)
            .map(Self)
            .ok_or(Error::InvalidVrfCache)
    }

    /// Encodes the cache: the range, then the cached layer, about `32 sqrt(R)` bytes. It holds no
    /// secret.
    #[must_use]
    pub fn cache_to_bytes(&self) -> Vec<u8> {
        self.0.cache_to_bytes()
    }

    /// The root, which the validator registers.
    #[must_use]
    pub fn root(&self) -> Root {
        self.0.root()
    }

    /// The proof of `slot`, in about `3 sqrt(R)` hashes.
    ///
    /// # Errors
    ///
    /// Fails if the slot is outside the range.
    pub fn proof(&self, slot: Slot) -> Result<Proof, Error> {
        self.0.proof(slot).ok_or(Error::VrfSlot { slot })
    }
}

/// Checks that `proof` opens `slot` under `root`, as the specifications' `is_valid_vrf_proof`.
///
/// # Errors
///
/// Fails if the proof does not open.
pub fn verify(root: &Root, slot: u64, proof: &Proof) -> Result<(), Error> {
    if verify_vrf_proof(root, slot, proof) {
        Ok(())
    } else {
        Err(Error::VrfVerify { slot })
    }
}
