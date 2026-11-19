//! The VRF tree of the consensus specifications' `pq` feature: a SHA-256 Merkle tree
//! of depth 31 whose root a validator registers and whose leaf for a slot a block
//! reveals, with the leaf's path, as its RANDAO contribution. Leaf `i` is
//! `SHA-256(seed | i as 8 little-endian bytes)` below the number of filled leaves
//! and zero from there on. A [`VrfState`] is the path of one slot, so a validator
//! holds no tree.

use sha2::{Digest as _, Sha256};

/// Depth of a VRF tree: it has `2^31` leaves, one for each slot.
pub const VRF_TREE_DEPTH: usize = 31;
/// How many hashes in a [`VrfProof`]: the leaf, then its path.
pub const VRF_PROOF_LEN: usize = VRF_TREE_DEPTH + 1;
/// How many bytes in a [`VrfNode`].
pub const VRF_NODE_LEN: usize = 32;
/// How many bytes in a [`VrfState`].
pub const VRF_STATE_SIZE: usize = size_of::<u32>() + VRF_TREE_DEPTH * VRF_NODE_LEN;
/// How many leaves devnets fill: enough for 145 days of 12 s slots.
pub const DEFAULT_VRF_LEAVES: u64 = 1 << 20;

const VRF_LEAVES: u64 = 1 << VRF_TREE_DEPTH;

/// A leaf or an inner node of a VRF tree.
pub type VrfNode = [u8; VRF_NODE_LEN];
/// The leaf of a slot, then its path: the specifications' `VRFProof`.
pub type VrfProof = [VrfNode; VRF_PROOF_LEN];

/// Derives the leaves of a VRF tree from a seed. It holds no tree.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct VrfKey {
    seed: [u8; 32],
    leaves: u64,
    zeros: [VrfNode; VRF_TREE_DEPTH],
}

/// The state to reveal the leaf of one slot from the seed alone: the leaf's path. It
/// holds nothing secret once the leaf is revealed.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct VrfState {
    slot: u32,
    path: [VrfNode; VRF_TREE_DEPTH],
}

impl VrfKey {
    /// The key of `seed` with its first `leaves` leaves filled, or `None` for more than `2^31`.
    pub fn new(seed: [u8; 32], leaves: u64) -> Option<Self> {
        if leaves > VRF_LEAVES {
            return None;
        }
        let mut zeros = [[0; VRF_NODE_LEN]; VRF_TREE_DEPTH];
        for level in 1..VRF_TREE_DEPTH {
            zeros[level] = node(&zeros[level - 1], &zeros[level - 1]);
        }
        Some(Self { seed, leaves, zeros })
    }

    /// The state at `slot`, hashing every filled leaf once, or `None` for a slot past the tree.
    pub fn state(&self, slot: u32) -> Option<VrfState> {
        if u64::from(slot) >= VRF_LEAVES {
            return None;
        }
        let path = std::array::from_fn(|level| self.subtree(level, u64::from(slot >> level) ^ 1));
        Some(VrfState { slot, path })
    }

    /// The state at `slot`, or `None` for a slot past the tree. It hashes the filled
    /// leaves of the subtree below the level where the two slots' paths part, and none of
    /// the leaves past the filled ones. It may move backwards: revealing a leaf twice
    /// gives nothing away, unlike signing twice at a leaf index.
    pub fn advance(&self, state: &VrfState, slot: u32) -> Option<VrfState> {
        if u64::from(slot) >= VRF_LEAVES {
            return None;
        }
        let mut next = state.clone();
        next.slot = slot;
        if slot == state.slot {
            return Some(next);
        }
        let split = (slot ^ state.slot).ilog2() as usize;
        next.path[split] = self.fold(state, split);
        for level in 0..split {
            next.path[level] = self.subtree(level, u64::from(slot >> level) ^ 1);
        }
        Some(next)
    }

    /// The root the state leads to under the seed: the validator's VRF root.
    pub fn root(&self, state: &VrfState) -> VrfNode {
        self.fold(state, VRF_TREE_DEPTH)
    }

    /// The proof of the state's slot.
    pub fn proof(&self, state: &VrfState) -> VrfProof {
        let mut proof = [[0; VRF_NODE_LEN]; VRF_PROOF_LEN];
        proof[0] = self.leaf(u64::from(state.slot));
        proof[1..].copy_from_slice(&state.path);
        proof
    }

    fn leaf(&self, index: u64) -> VrfNode {
        if index >= self.leaves {
            return self.zeros[0];
        }
        Sha256::new()
            .chain_update(self.seed)
            .chain_update(index.to_le_bytes())
            .finalize()
            .into()
    }

    fn fold(&self, state: &VrfState, levels: usize) -> VrfNode {
        fold(
            self.leaf(u64::from(state.slot)),
            u64::from(state.slot),
            &state.path[..levels],
        )
    }

    fn subtree(&self, level: usize, index: u64) -> VrfNode {
        if index << level >= self.leaves {
            return self.zeros[level];
        }
        if level == 0 {
            return self.leaf(index);
        }
        node(
            &self.subtree(level - 1, 2 * index),
            &self.subtree(level - 1, 2 * index + 1),
        )
    }
}

impl VrfState {
    pub fn slot(&self) -> u32 {
        self.slot
    }

    /// The slot as 4 little-endian bytes, then the path.
    pub fn to_bytes(&self) -> [u8; VRF_STATE_SIZE] {
        let mut out = [0; VRF_STATE_SIZE];
        let (slot, path) = out.split_at_mut(size_of::<u32>());
        slot.copy_from_slice(&self.slot.to_le_bytes());
        path.copy_from_slice(self.path.as_flattened());
        out
    }

    /// `None` for a slot past the tree. Check the state against the expected root with
    /// [`VrfKey::root`] before revealing from it.
    pub fn from_bytes(bytes: &[u8; VRF_STATE_SIZE]) -> Option<Self> {
        let (slot, path) = bytes.split_at(size_of::<u32>());
        let slot = u32::from_le_bytes(slot.try_into().unwrap());
        if u64::from(slot) >= VRF_LEAVES {
            return None;
        }
        let (nodes, _) = path.as_chunks();
        Some(Self {
            slot,
            path: nodes.try_into().unwrap(),
        })
    }
}

/// Whether `proof` opens the leaf of `slot` under `root`, as `is_valid_vrf_proof` of the
/// consensus specifications does: only the 31 low bits of the slot count.
pub fn verify_vrf_proof(root: &VrfNode, slot: u64, proof: &VrfProof) -> bool {
    fold(proof[0], slot, &proof[1..]) == *root
}

fn fold(leaf: VrfNode, index: u64, path: &[VrfNode]) -> VrfNode {
    path.iter().enumerate().fold(leaf, |current, (level, sibling)| {
        if (index >> level) & 1 == 0 {
            node(&current, sibling)
        } else {
            node(sibling, &current)
        }
    })
}

fn node(left: &VrfNode, right: &VrfNode) -> VrfNode {
    Sha256::new().chain_update(left).chain_update(right).finalize().into()
}
