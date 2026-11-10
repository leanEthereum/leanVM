// CREDIT: https://github.com/succinctlabs/flock (flock-core), MIT OR Apache-2.0.
//! Digest encoding and Merkle openings carried by proofs.

use primitives::field::{F64, F192};

use crate::digest_words;

pub type Hash = [u8; 32];

/// Encode a Merkle hash as the two field words transcripts carry it in: two
/// 128-bit halves, each a K pair with a spare top lane. Every digest in the
/// protocol uses this one split (the commitment root, the public input, the
/// guest's MD state), so the VM sees one shape everywhere.
#[inline]
pub fn hash_to_scalars(hash: &Hash) -> [F192; 2] {
    let [w0, w1, w2, w3] = digest_words(hash);
    [F192::new(w0.0, w1.0, 0), F192::new(w2.0, w3.0, 0)]
}

/// Hash one leaf ([`primitives::hash::hash`]).
#[inline]
pub fn hash_leaf(data: &[u8]) -> Hash {
    primitives::hash::hash(data)
}

/// Hash one leaf given as its words, little-endian on any host.
pub fn hash_words(words: &[F64]) -> Hash {
    hash_leaf(&words.iter().flat_map(|word| word.0.to_le_bytes()).collect::<Vec<u8>>())
}

/// Hash two children into their parent.
#[inline]
pub fn hash_pair(left: &Hash, right: &Hash) -> Hash {
    let mut buf = [0u8; 64];
    buf[..32].copy_from_slice(left);
    buf[32..].copy_from_slice(right);
    primitives::hash::hash(&buf)
}

/// One query's Merkle opening: its position, the whole leaf image it hashes, and its siblings, bottom level first.
///
/// Leaf data is `F64` because that is what a Merkle preimage is; an `E`-valued row of width `w` is `3w` words, packed
/// by the opener.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MerklePath {
    pub leaf_index: u64,
    pub leaf: Vec<F64>,
    pub siblings: Vec<Hash>,
}

/// Prover side: the paths of `positions` in a tree of `num_leaves` leaves held in pieces, climbing `levels` levels: the
/// whole height for a tree, fewer for a forest of subtrees. `node(level, i)` is node `i` of `level`, leaves at level 0,
/// and the leaf at `q` is `row(q)` behind the zeros that make it `leaf_words` long.
pub fn open<'a>(
    num_leaves: usize,
    levels: usize,
    positions: &[usize],
    leaf_words: usize,
    node: impl Fn(usize, usize) -> Hash,
    row: impl Fn(usize) -> &'a [F64],
) -> Vec<MerklePath> {
    assert!(num_leaves.is_power_of_two() && levels <= num_leaves.trailing_zeros() as usize);
    let path = |&q: &usize| MerklePath {
        leaf_index: q as u64,
        leaf: padded(row(q), leaf_words),
        siblings: (0..levels).map(|level| node(level, q >> level ^ 1)).collect(),
    };
    positions.iter().map(path).collect()
}

/// The `leaf_words` leaf whose words after the leading zeros are `row`.
pub(crate) fn padded(row: &[F64], leaf_words: usize) -> Vec<F64> {
    let zeros = std::iter::repeat_n(F64::ZERO, leaf_words - row.len());
    zeros.chain(row.iter().copied()).collect()
}
