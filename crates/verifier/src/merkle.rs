//! Merkle openings in the form a proof travels in: one batch per opening phase, each shared sibling sent once.

use crate::field::K;
use crate::hash::{Digest, sha3_hash};
use crate::{VerifierError, require};

/// A proof's Merkle openings, in either form. Both authenticate the same leaf images against the same roots.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum MerkleOpenings {
    /// Every query's own opening, in the order the verifier reads them: its leaf's words, then its sibling digests.
    Raw(Vec<u8>),
    /// One batch per opening phase, in the order the verifier reads them.
    Pruned(Vec<PrunedMerklePaths>),
}

impl MerkleOpenings {
    /// What the transcript's cursor counts: bytes of the raw form, batches of the pruned one.
    pub(crate) fn len(&self) -> usize {
        match self {
            Self::Raw(data) => data.len(),
            Self::Pruned(batches) => batches.len(),
        }
    }
}

/// One opening phase: the row at each distinct queried position, ascending, and the siblings that
/// authenticate all of them together, bottom level first and left to right within a level.
///
/// A row may be narrower than the leaf image it hashes to. The words it leaves out are a zero prefix,
/// which is how a level-0 commitment keeps the lanes past the end of the stack out of the proof.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct PrunedMerklePaths {
    pub leaf_data: Vec<Vec<K>>,
    pub sibling_hashes: Vec<[u8; 32]>,
}

pub fn hash_pair(left: &[u8], right: &[u8]) -> Digest {
    let mut pair = [0u8; 64];
    pair[..32].copy_from_slice(left);
    pair[32..].copy_from_slice(right);
    sha3_hash(&pair)
}

fn hash_leaf(image: &[K]) -> Digest {
    sha3_hash(&image.iter().flat_map(|word| word.to_bytes()).collect::<Vec<u8>>())
}

/// One query's own opening, the form the recursion guest and the Python verifier read.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MerklePath {
    pub leaf_index: u64,
    /// The whole leaf image, its zero prefix included.
    pub leaf: Vec<K>,
    /// Bottom level first.
    pub siblings: Vec<[u8; 32]>,
}

impl MerklePath {
    pub(crate) fn root(&self) -> Digest {
        let mut node = hash_leaf(&self.leaf);
        for (level, sibling) in self.siblings.iter().enumerate() {
            node = if self.leaf_index >> level & 1 == 0 {
                hash_pair(&node.0, sibling)
            } else {
                hash_pair(sibling, &node.0)
            };
        }
        node
    }
}

impl PrunedMerklePaths {
    /// The root the batch hashes to, and each query's own path, in `queries` order.
    ///
    /// Every node on a queried path is rebuilt bottom-up, a sibling being read only where it is not itself on one.
    /// Comparing the root is the caller's: nothing here authenticates the batch.
    pub(crate) fn expand(
        &self,
        height: usize,
        queries: &[u64],
        row_words: usize,
        leaf_words: usize,
    ) -> Result<(Digest, Vec<MerklePath>), VerifierError> {
        let mut positions = queries.to_vec();
        positions.sort_unstable();
        positions.dedup();
        require(
            positions.last().is_some_and(|&last| last >> height == 0)
                && positions.len() == self.leaf_data.len()
                && row_words <= leaf_words
                && self.leaf_data.iter().all(|row| row.len() == row_words),
            VerifierError::MerkleOpeningShape,
        )?;
        let mut paths: Vec<MerklePath> = positions
            .iter()
            .zip(&self.leaf_data)
            .map(|(&leaf_index, row)| MerklePath {
                leaf_index,
                leaf: [&vec![K(0); leaf_words - row_words], &row[..]].concat(),
                siblings: Vec::with_capacity(height),
            })
            .collect();

        let mut siblings = self.sibling_hashes.iter();
        let mut nodes: Vec<(u64, Digest)> = paths
            .iter()
            .map(|path| (path.leaf_index, hash_leaf(&path.leaf)))
            .collect();
        let mut node_of: Vec<usize> = (0..paths.len()).collect(); // where each position's ancestor sits in `nodes`
        for _ in 0..height {
            let mut parents = Vec::with_capacity(nodes.len());
            let mut level_siblings = Vec::with_capacity(nodes.len()); // each node's sibling, and where its parent sits
            let mut i = 0;
            while i < nodes.len() {
                let (index, node) = nodes[i];
                let paired = index & 1 == 0 && nodes.get(i + 1).is_some_and(|&(next, _)| next == index | 1);
                let parent = if paired {
                    let right = nodes[i + 1].1;
                    level_siblings.extend([(right.0, parents.len()), (node.0, parents.len())]);
                    hash_pair(&node.0, &right.0)
                } else {
                    let sibling = siblings.next().ok_or(VerifierError::MerkleOpeningMissing)?;
                    level_siblings.push((*sibling, parents.len()));
                    if index & 1 == 0 {
                        hash_pair(&node.0, sibling)
                    } else {
                        hash_pair(sibling, &node.0)
                    }
                };
                parents.push((index >> 1, parent));
                i += if paired { 2 } else { 1 };
            }
            for (path, node) in paths.iter_mut().zip(&mut node_of) {
                let (sibling, parent) = level_siblings[*node];
                path.siblings.push(sibling);
                *node = parent;
            }
            nodes = parents;
        }
        require(siblings.next().is_none(), VerifierError::MerkleNotConsumed)?;

        let path_of = |query: &u64| paths[positions.binary_search(query).expect("every query is a position")].clone();
        Ok((nodes[0].1, queries.iter().map(path_of).collect()))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// A depth-3 tree over four-word images whose first word is zero, opened at repeated and adjacent positions.
    #[test]
    fn open_expands_the_honest_batch() {
        let (height, leaf_words, row_words) = (3, 4, 3);
        let image = |position: u64| -> Vec<K> {
            (0..4)
                .map(|word| K(if word == 0 { 0 } else { 4 * position + word }))
                .collect()
        };
        let hash = |image: &[K]| sha3_hash(&image.iter().flat_map(|word| word.to_bytes()).collect::<Vec<u8>>());
        let mut levels = vec![(0..8).map(|position| hash(&image(position))).collect::<Vec<Digest>>()];
        for level in 0..height {
            let parents = levels[level]
                .as_chunks()
                .0
                .iter()
                .map(|[left, right]| hash_pair(&left.0, &right.0));
            levels.push(parents.collect());
        }
        let root = levels[height][0];

        // Positions 1, 4, 5: leaf 0 and the hash of leaves 2..4 below the left half, the hash of leaves 6..8 below the right.
        let queries = [5, 1, 5, 4];
        let good = PrunedMerklePaths {
            leaf_data: [1, 4, 5]
                .iter()
                .map(|&position| image(position)[1..].to_vec())
                .collect(),
            sibling_hashes: vec![levels[0][0].0, levels[1][1].0, levels[1][3].0],
        };
        let (batch_root, paths) = good
            .expand(height, &queries, row_words, leaf_words)
            .expect("the honest batch opens");
        assert_eq!(batch_root, root);
        for (path, query) in paths.iter().zip(queries) {
            assert_eq!((path.leaf_index, &path.leaf), (query, &image(query)));
            assert_eq!(path.root(), root, "the path of {query} is its own opening");
        }
    }
}
