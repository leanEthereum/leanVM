//! The VRF tree of the consensus `pq` feature, pruned to a range of slots.
//!
//! The tree is a Keccak-256 Merkle tree of depth 31, one leaf per slot (`i` and `j` as 8
//! little-endian bytes, `h` as 1 byte):
//!
//! ```text
//!     secret i     Keccak-256("VRF_SECRET" | seed | i), for i in the range
//!     leaf i       Keccak-256("VRF_LEAF" | secret i | i)
//!     node         Keccak-256(left | right)
//!     surrogate    Keccak-256("VRF_SURROGATE" | seed | j | h), for a subtree at height h,
//!                  index j, with no slot of the range; nobody can open it
//! ```
//!
//! A proof of slot `i` reveals secret `i`; its branch holds only leaves and nodes, which reveal no
//! other secret.
//!
//! A [`VrfKey`] caches one layer of about `sqrt(R)` nodes for a range of `R` slots: building it
//! hashes the range once, and a proof then costs about `3 sqrt(R)` hashes.

use std::ops::Range;

use keccak256::{Hash, hash_pair};

/// Depth of the tree: `2^31` slots.
pub const VRF_TREE_DEPTH: usize = 31;

/// A slot's secret, then its leaf's 31 siblings: the specifications' `VRFProof`.
pub type VrfProof = [Hash; VRF_TREE_DEPTH + 1];

const VRF_SECRET_DOMAIN: &[u8] = b"VRF_SECRET";
const VRF_LEAF_DOMAIN: &[u8] = b"VRF_LEAF";
const VRF_SURROGATE_DOMAIN: &[u8] = b"VRF_SURROGATE";

/// A seed, its range of slots, and one cached layer of its tree.
#[derive(Clone)]
pub struct VrfKey {
    seed: [u8; 32],
    slots: Range<u32>,
    /// Height of the cached layer.
    level: usize,
    /// The layer's nodes that hold a slot of the range, left to right.
    cache: Vec<Hash>,
    root: Hash,
}

/// Prints the range only: the seed is secret.
impl std::fmt::Debug for VrfKey {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("VrfKey")
            .field("slots", &self.slots)
            .finish_non_exhaustive()
    }
}

impl VrfKey {
    /// Builds the key, hashing every slot of the range. `None` if the range is empty or ends past
    /// `2^31`.
    pub fn new(seed: [u8; 32], slots: Range<u32>) -> Option<Self> {
        let (level, first, last) = layer(&slots)?;
        let uncached = Self::uncached(seed, slots);
        let cache = (first..=last).map(|j| uncached.node(level, j.into())).collect();
        Some(uncached.with_cache(level, cache))
    }

    /// Rebuilds a key from its seed, its root and a cache from [`Self::cache_to_bytes`], without
    /// hashing the range. `None` if the cache is malformed or does not lead to `root`.
    pub fn from_cache_bytes(seed: [u8; 32], root: &Hash, bytes: &[u8]) -> Option<Self> {
        let (start, rest) = bytes.split_first_chunk::<4>()?;
        let (end, nodes) = rest.split_first_chunk::<4>()?;
        let slots = u32::from_le_bytes(*start)..u32::from_le_bytes(*end);
        let (level, first, last) = layer(&slots)?;
        let (nodes, []) = nodes.as_chunks::<32>() else {
            return None;
        };
        if nodes.len() != (last - first + 1) as usize {
            return None;
        }
        let key = Self::uncached(seed, slots).with_cache(level, nodes.to_vec());
        // The root pins the cached nodes, not where the range ends inside the first and last: any
        // other range treats a subtree beside one of its end slots wrongly, so that slot fails.
        let opens = |slot: u32| {
            key.proof(slot)
                .is_some_and(|proof| verify_vrf_proof(root, slot.into(), &proof))
        };
        (key.root == *root && opens(key.slots.start) && opens(key.slots.end - 1)).then_some(key)
    }

    /// Encodes the cache: `start` and `end` (4 little-endian bytes each), then the cached layer. It
    /// holds no secret.
    pub fn cache_to_bytes(&self) -> Vec<u8> {
        [
            &self.slots.start.to_le_bytes(),
            &self.slots.end.to_le_bytes(),
            self.cache.as_flattened(),
        ]
        .concat()
    }

    /// The root, which the validator registers.
    pub fn root(&self) -> Hash {
        self.root
    }

    /// The proof of `slot`. `None` outside the range.
    pub fn proof(&self, slot: u32) -> Option<VrfProof> {
        self.slots.contains(&slot).then(|| {
            std::array::from_fn(|i| match i {
                0 => self.secret(slot.into()),
                _ => self.node(i - 1, u64::from(slot >> (i - 1)) ^ 1),
            })
        })
    }

    /// A key with no layer cached yet: its nodes are hashed from the leaves.
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

    fn node(&self, level: usize, index: u64) -> Hash {
        let (start, end) = (u64::from(self.slots.start), u64::from(self.slots.end));
        if (index + 1) << level <= start || index << level >= end {
            return self.surrogate(level, index);
        }
        if level == self.level {
            return self.cache[(index - (start >> level)) as usize];
        }
        if level == 0 {
            return leaf(&self.secret(index), index);
        }
        hash_pair(&self.node(level - 1, 2 * index), &self.node(level - 1, 2 * index + 1))
    }

    fn secret(&self, index: u64) -> Hash {
        keccak256::Hasher::new()
            .update(VRF_SECRET_DOMAIN)
            .update(&self.seed)
            .update(&index.to_le_bytes())
            .finalize()
    }

    fn surrogate(&self, level: usize, index: u64) -> Hash {
        keccak256::Hasher::new()
            .update(VRF_SURROGATE_DOMAIN)
            .update(&self.seed)
            .update(&index.to_le_bytes())
            .update(&[level as u8])
            .finalize()
    }
}

/// The cached layer's height and its first and last node index. `None` if the range is empty or
/// ends past `2^31`.
///
/// The height is half that of the range's subtree.
fn layer(slots: &Range<u32>) -> Option<(usize, u32, u32)> {
    if slots.is_empty() || slots.end > 1 << VRF_TREE_DEPTH {
        return None;
    }
    let level = slots.len().next_power_of_two().ilog2().div_ceil(2) as usize;
    Some((level, slots.start >> level, (slots.end - 1) >> level))
}

/// The leaf of `index`, which commits to `secret`: the specifications' `compute_vrf_leaf`.
fn leaf(secret: &Hash, index: u64) -> Hash {
    keccak256::Hasher::new()
        .update(VRF_LEAF_DOMAIN)
        .update(secret)
        .update(&index.to_le_bytes())
        .finalize()
}

/// Whether `proof` reveals the secret of `slot` under `root`, as the specifications'
/// `is_valid_vrf_proof`: the leaf commits to all of `slot`, and its 31 low bits choose the path.
pub fn verify_vrf_proof(root: &Hash, slot: u64, proof: &VrfProof) -> bool {
    keccak256::path_fold(
        leaf(&proof[0], slot),
        slot as usize,
        &proof[1..],
        |_| {},
        |_, _, [left, right]| hash_pair(left, right),
    ) == *root
}
