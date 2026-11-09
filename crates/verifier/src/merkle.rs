//! Merkle openings: one full path per query.
//!
//! A node is the hash of its four children's digests, left to right; a tree of odd height has a two-child root.

use crate::field::K;
use crate::hash::{Digest, keccak_hash};

pub fn hash_pair(left: &[u8], right: &[u8]) -> Digest {
    let mut pair = [0u8; 64];
    pair[..32].copy_from_slice(left);
    pair[32..].copy_from_slice(right);
    keccak_hash(&pair)
}

fn hash_leaf(image: &[K]) -> Digest {
    keccak_hash(&image.iter().flat_map(|word| word.to_bytes()).collect::<Vec<u8>>())
}

/// Siblings on a path in a tree `height` bits tall: three per four-child level, one at a two-child root.
pub(crate) fn sibling_count(height: usize) -> usize {
    3 * (height / 2) + height % 2
}

/// One query's own opening, the form the Rust and Python verifiers read.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MerklePath {
    pub leaf_index: u64,
    /// The whole leaf image, its zero prefix included.
    pub leaf: Vec<K>,
    /// Per level, bottom first, the other children of the node's parent, left to right: three, and one at a
    /// two-child root.
    pub siblings: Vec<[u8; 32]>,
}

impl MerklePath {
    pub(crate) fn root(&self) -> Digest {
        let mut node = hash_leaf(&self.leaf);
        let mut index = self.leaf_index;
        for siblings in self.siblings.chunks(3) {
            let arity = siblings.len() + 1;
            let at = index as usize % arity;
            let mut children = [[0u8; 32]; 4];
            let (before, after) = siblings.split_at(at);
            let ordered = before.iter().chain([&node.0]).chain(after);
            for (slot, child) in children.iter_mut().zip(ordered) {
                *slot = *child;
            }
            node = keccak_hash(children[..arity].as_flattened());
            index /= arity as u64;
        }
        node
    }
}
