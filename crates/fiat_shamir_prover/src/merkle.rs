// CREDIT: https://github.com/succinctlabs/flock (flock-core), MIT OR Apache-2.0.
//! Digest encoding and the Merkle openings a proof carries ([`MerklePath`]), prover side.

use crate::Scalar;
use verifier::Digest;
pub use verifier::MerklePath;

pub type Hash = [u8; 32];

/// A digest as the two scalars it travels in, its halves ([`Digest::halves`]) in the prover's field.
pub fn hash_to_scalars<F: Scalar>(hash: &Hash) -> [F; 2] {
    let (low, high) = Digest(*hash).halves();
    [low, high].map(|half| F::from_limbs([half.c0, half.c1]))
}

/// Hash one leaf given as its words, little-endian on any host.
pub fn hash_words(words: impl IntoIterator<Item = u64>) -> Hash {
    keccak256::hash(&words.into_iter().flat_map(u64::to_le_bytes).collect::<Vec<u8>>())
}

pub use keccak256::hash_pair;

/// Prover side: the paths of `positions` in a tree of `num_leaves` leaves held in pieces. `node(level, i)` is node `i`
/// of `level`, leaves at level 0, and the leaf at `q` is the words `row(q)` behind the zeros that make it
/// `leaf_words` long.
pub fn open<R: IntoIterator<Item = u64>>(
    num_leaves: usize,
    positions: &[usize],
    leaf_words: usize,
    node: impl Fn(usize, usize) -> Hash,
    row: impl Fn(usize) -> R,
) -> Vec<MerklePath> {
    assert!(num_leaves.is_power_of_two());
    let height = num_leaves.trailing_zeros() as usize;
    let path = |&q: &usize| {
        let row: Vec<verifier::K> = row(q).into_iter().map(verifier::K).collect();
        let mut leaf = vec![verifier::K(0); leaf_words - row.len()];
        leaf.extend(row);
        MerklePath {
            leaf_index: q as u64,
            leaf,
            siblings: (0..height).map(|level| node(level, q >> level ^ 1)).collect(),
        }
    };
    positions.iter().map(path).collect()
}
