//! The VRF tree of the consensus specifications' `pq` feature: a Keccak-256 Merkle tree of
//! depth 31 with one leaf per slot, pruned to the slots a validator proposes in. Leaf `i` of the
//! range is `Keccak-256(seed | i)`, a node `Keccak-256(left | right)`, and a subtree holding no
//! slot of the range the surrogate `Keccak-256(seed | j | h)` at height `h` and index `j`, which
//! nobody can open (`i` and `j` as 8 little-endian bytes, `h` as 1).
//!
//! A [`VrfKey`] keeps the layer at half the height of the range's subtree, about `sqrt(R)` nodes
//! for `R` slots, so building it hashes every leaf once and a proof then costs about `3 sqrt(R)`.

use std::ops::Range;

use keccak256::{Hash, hash_pair};

/// Depth of a VRF tree: it has `2^31` leaves, one for each slot.
pub const VRF_TREE_DEPTH: usize = 31;

/// The leaf of a slot, then its path: the specifications' `VRFProof`.
pub type VrfProof = [Hash; VRF_TREE_DEPTH + 1];

/// A seed, the range of slots its tree holds leaves for, and the tree's cached layer.
#[derive(Clone)]
pub struct VrfKey {
    seed: [u8; 32],
    slots: Range<u32>,
    /// Height of the cached layer.
    level: usize,
    /// The nodes at `level` that hold a slot of the range, left to right.
    cache: Vec<Hash>,
    root: Hash,
}

/// The range alone: the seed is secret.
impl std::fmt::Debug for VrfKey {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("VrfKey")
            .field("slots", &self.slots)
            .finish_non_exhaustive()
    }
}

impl VrfKey {
    /// The key of `seed` with the leaves of `slots`, hashing each of them once, or `None` for an
    /// empty range or one past `2^31`.
    pub fn new(seed: [u8; 32], slots: Range<u32>) -> Option<Self> {
        let (level, first, last) = layer(&slots)?;
        let uncached = Self::uncached(seed, slots);
        let cache = (first..=last).map(|j| uncached.node(level, j.into())).collect();
        Some(uncached.with_cache(level, cache))
    }

    /// The range, `start` then `end` as 4 little-endian bytes each, then the cached layer. The
    /// bytes hold no secret, and [`Self::from_cache_bytes`] loads them in place of hashing the
    /// range again.
    pub fn cache_to_bytes(&self) -> Vec<u8> {
        [
            &self.slots.start.to_le_bytes(),
            &self.slots.end.to_le_bytes(),
            self.cache.as_flattened(),
        ]
        .concat()
    }

    /// The key of `seed` and the bytes of [`Self::cache_to_bytes`], hashing about `sqrt(R)` nodes
    /// for the root, or `None` for bytes that do not encode a range and its layer. The layer is
    /// not checked: a wrong one gives a wrong root, so compare [`Self::root`] with the registered
    /// root before revealing a proof.
    pub fn from_cache_bytes(seed: [u8; 32], bytes: &[u8]) -> Option<Self> {
        let (start, rest) = bytes.split_first_chunk::<4>()?;
        let (end, nodes) = rest.split_first_chunk::<4>()?;
        let slots = u32::from_le_bytes(*start)..u32::from_le_bytes(*end);
        let (level, first, last) = layer(&slots)?;
        let (nodes, []) = nodes.as_chunks::<32>() else {
            return None;
        };
        (nodes.len() == (last - first + 1) as usize)
            .then(|| Self::uncached(seed, slots).with_cache(level, nodes.to_vec()))
    }

    /// The validator's VRF root.
    pub fn root(&self) -> Hash {
        self.root
    }

    /// A key with no layer cached yet, whose nodes are hashed from their leaves.
    fn uncached(seed: [u8; 32], slots: Range<u32>) -> Self {
        Self {
            seed,
            slots,
            level: usize::MAX,
            cache: Vec::new(),
            root: Hash::default(),
        }
    }

    fn with_cache(self, level: usize, cache: Vec<Hash>) -> Self {
        let mut key = Self { level, cache, ..self };
        key.root = key.node(VRF_TREE_DEPTH, 0);
        key
    }

    /// The proof of `slot`, or `None` outside the range.
    pub fn proof(&self, slot: u32) -> Option<VrfProof> {
        self.slots.contains(&slot).then(|| {
            std::array::from_fn(|i| match i {
                0 => self.derive(slot.into(), &[]),
                _ => self.node(i - 1, u64::from(slot >> (i - 1)) ^ 1),
            })
        })
    }

    fn node(&self, level: usize, index: u64) -> Hash {
        let (start, end) = (u64::from(self.slots.start), u64::from(self.slots.end));
        if (index + 1) << level <= start || index << level >= end {
            return self.derive(index, &[level as u8]);
        }
        if level == self.level {
            return self.cache[(index - (start >> level)) as usize];
        }
        if level == 0 {
            return self.derive(index, &[]);
        }
        hash_pair(&self.node(level - 1, 2 * index), &self.node(level - 1, 2 * index + 1))
    }

    fn derive(&self, index: u64, suffix: &[u8]) -> Hash {
        keccak256::Hasher::new()
            .update(&self.seed)
            .update(&index.to_le_bytes())
            .update(suffix)
            .finalize()
    }
}

/// The height of the cached layer, at half the height of the range's subtree but at least 1, so
/// that no leaf is cached, and the indices of its first and last node holding a slot of the
/// range; `None` for an empty range or one past `2^31`.
fn layer(slots: &Range<u32>) -> Option<(usize, u32, u32)> {
    if slots.is_empty() || slots.end > 1 << VRF_TREE_DEPTH {
        return None;
    }
    let level = slots.len().next_power_of_two().ilog2().div_ceil(2).max(1) as usize;
    Some((level, slots.start >> level, (slots.end - 1) >> level))
}

/// Whether `proof` opens the leaf of `slot` under `root`, as `is_valid_vrf_proof` of the
/// consensus specifications does: only the 31 low bits of the slot count.
pub fn verify_vrf_proof(root: &Hash, slot: u64, proof: &VrfProof) -> bool {
    let leaf = proof[0];
    let path = &proof[1..];
    keccak256::path_fold(
        leaf,
        slot as usize,
        path,
        |_| {},
        |_, _, [left, right]| hash_pair(left, right),
    ) == *root
}
