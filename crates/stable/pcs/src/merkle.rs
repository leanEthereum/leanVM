// CREDIT: https://github.com/succinctlabs/flock (flock-core), MIT OR Apache-2.0.
//! Binary Merkle tree with Keccak-256: the committer's half. What a proof carries lives in [`fiat_shamir::merkle`].

pub use fiat_shamir::merkle::{Hash, MerklePath, hash_leaf, hash_pair};
use primitives::field::F64;
use primitives::hash::{OUT_LEN, RATE, hash_many, hash_many_from_state, zero_prefix_state};

/// Leaves or nodes a task hashes at a time.
const CHUNK: usize = 1 << 10;

/// A Merkle tree with every level kept, the leaf digests first and the root last.
pub(crate) struct MerkleTree {
    levels: Vec<Vec<Hash>>,
}

impl MerkleTree {
    /// The tree over `rows`, `row_words` each, a leaf being `zeros(leaf_words - row_words) ‖ row`.
    ///
    /// The leaves' whole blocks of leading zeros are one sponge state, absorbed once for every leaf.
    pub(crate) fn build(rows: &[F64], row_words: usize, leaf_words: usize) -> Self {
        let num_leaves = rows.len() / row_words;
        assert!(num_leaves.is_power_of_two() && rows.len() == num_leaves * row_words);
        assert!(0 < row_words && row_words <= leaf_words, "a leaf holds its row");
        let (row_bytes, leaf_bytes) = (8 * row_words, 8 * leaf_words);
        let zero_blocks = (leaf_bytes - row_bytes) / RATE;
        let state = zero_prefix_state(zero_blocks);
        // The bytes each leaf hashes past the shared prefix: its row, behind the zeros left over.
        let image = leaf_bytes - zero_blocks * RATE;
        let bytes: &[u8] = primitives::cast_slice(rows);
        let mut leaves = vec![[0u8; OUT_LEN]; num_leaves];
        parallel::chunks_mut(&mut leaves, CHUNK, |i, out| {
            let rows = &bytes[i * CHUNK * row_bytes..][..out.len() * row_bytes];
            let mut images = vec![0u8; out.len() * image];
            for (slot, row) in images.chunks_exact_mut(image).zip(rows.chunks_exact(row_bytes)) {
                slot[image - row_bytes..].copy_from_slice(row);
            }
            hash_many_from_state(&images, image, &state, out.as_flattened_mut());
        });
        let mut levels = vec![leaves];
        while let Some(children) = levels.last().filter(|level| level.len() > 1) {
            let mut parents = vec![[0u8; OUT_LEN]; children.len() / 2];
            parallel::chunks_mut(&mut parents, CHUNK, |i, out| {
                let children = &children[2 * i * CHUNK..][..2 * out.len()];
                hash_many(children.as_flattened(), 2 * OUT_LEN, out.as_flattened_mut());
            });
            levels.push(parents);
        }
        Self { levels }
    }

    pub(crate) fn root(&self) -> Hash {
        self.levels[self.levels.len() - 1][0]
    }

    /// The paths of `positions`, with `row(q)` the row at `q`, padded to `leaf_words`.
    pub(crate) fn open<'a>(
        &self,
        positions: &[usize],
        leaf_words: usize,
        row: impl Fn(usize) -> &'a [F64],
    ) -> Vec<MerklePath> {
        let node = |level: usize, i: usize| self.levels[level][i];
        fiat_shamir::merkle::open(self.levels[0].len(), positions, leaf_words, node, row)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Every level and every path agree with the tree hashed one leaf and one pair at a time, whether the leaf's
    /// zeros fill whole blocks, a block and a part, or less than a block.
    #[test]
    fn tree_matches_the_sequential_reference() {
        for (num_leaves, row_words, leaf_words) in [
            (1usize, 4usize, 4usize),
            (8, 64, 64),
            (2048, 37, 64),
            (256, 30, 64),
            (64, 1, 64),
            (32, 5, 8),
            (16, 3, 5),
            (1 << 12, 6, 6),
        ] {
            let rows: Vec<F64> = (0..row_words * num_leaves)
                .map(|i| F64(i.wrapping_mul(0x9E37_79B9_7F4A_7C15) as u64 | 1))
                .collect();
            let row = |q: usize| &rows[q * row_words..][..row_words];
            let mut level: Vec<Hash> = (0..num_leaves)
                .map(|q| {
                    let mut image = vec![0u8; 8 * (leaf_words - row_words)];
                    image.extend_from_slice(primitives::cast_slice(row(q)));
                    hash_leaf(&image)
                })
                .collect();
            let tree = MerkleTree::build(&rows, row_words, leaf_words);
            let context = format!("num_leaves={num_leaves} row_words={row_words} leaf_words={leaf_words}");
            assert_eq!(tree.levels.len(), num_leaves.ilog2() as usize + 1, "{context}");
            for got in &tree.levels {
                assert_eq!(*got, level, "{context}");
                level = level.as_chunks::<2>().0.iter().map(|[a, b]| hash_pair(a, b)).collect();
            }
            let positions = [0, num_leaves / 3, num_leaves - 1, 0];
            for path in tree.open(&positions, leaf_words, row) {
                let image: Vec<u8> = path.leaf.iter().flat_map(|w| w.0.to_le_bytes()).collect();
                let mut node = hash_leaf(&image);
                for (level, sibling) in path.siblings.iter().enumerate() {
                    node = if (path.leaf_index >> level) & 1 == 0 {
                        hash_pair(&node, sibling)
                    } else {
                        hash_pair(sibling, &node)
                    };
                }
                assert_eq!(node, tree.root(), "path {}, {context}", path.leaf_index);
            }
        }
    }
}
