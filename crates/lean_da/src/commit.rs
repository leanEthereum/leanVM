//! A Merkle tree per blob, then one over the blob roots.
//!
//! A blob's leaves are its `ℓ = m/c` cell digests, so the left subtree of its root covers the
//! systematic payload and a sampled cell opens against its blob root. The blob roots, padded with
//! the zero codeword's to a power of two, are the leaves of the commitment's tree.

use fiat_shamir::merkle::Hash;
use primitives::hash::{OUT_LEN, hash, hash_many};

use crate::{
    BLOB_SYMBOLS, BlobSizeError, CELL_SYMBOLS, CELLS_PER_ROW, CODEWORD_SYMBOLS, checked_row_count, encode_rows,
    row_count,
};

/// Digests in one blob's flat tree.
const BLOB_TREE: usize = 2 * CELLS_PER_ROW - 1;

/// What the builder keeps, to answer samples and to feed the proof.
pub struct DaWitness {
    /// `n_rows · m` symbols, row-major. Padding rows are zero and not stored.
    pub codewords: Vec<u64>,
    /// One flat tree per blob of the padded matrix, `2ℓ - 1` digests each: its `ℓ` cell
    /// digests, then each level in turn, its root last.
    pub blob_trees: Vec<Hash>,
    /// The flat tree over the `n_padded` blob roots, laid out likewise.
    pub root_tree: Vec<Hash>,
}

impl DaWitness {
    /// Blob `i`'s flat tree, its cell digests first, for any `i` below `n_padded`.
    pub fn blob_tree(&self, i: usize) -> &[Hash] {
        &self.blob_trees[i * BLOB_TREE..(i + 1) * BLOB_TREE]
    }

    /// The `n_padded` blob roots, the padding blobs' included.
    pub fn blob_roots(&self) -> &[Hash] {
        &self.root_tree[..self.root_tree.len().div_ceil(2)]
    }
}

/// Commit to payload rows of little-endian 64-bit symbols and their systematic encoding.
///
/// Returns the root, which the builder publishes: the root of the tree over the blob roots,
/// binding the matrix including its zero padding.
///
/// # Errors
///
/// If `rows` is empty, ends in a partial blob, or holds more blobs than one commitment takes.
#[tracing::instrument(name = "Commit", skip_all)]
pub fn commit(rows: &[u64]) -> Result<(Hash, DaWitness), BlobSizeError> {
    checked_row_count(rows.len(), BLOB_SYMBOLS).ok_or(BlobSizeError { symbols: rows.len() })?;
    let codewords = encode_rows(rows);
    Ok(commit_codewords(codewords))
}

/// [`commit`] over rows that are already encoded.
///
/// # Panics
///
/// If `codewords` is empty, ends in a partial codeword, or holds more codewords than one commitment takes.
pub fn commit_codewords(codewords: Vec<u64>) -> (Hash, DaWitness) {
    let blob_trees = blob_trees(&codewords);
    let blob_roots = blob_trees
        .as_chunks::<BLOB_TREE>()
        .0
        .iter()
        .map(|tree| tree[BLOB_TREE - 1]);
    let root_tree = tree_from_leaves(blob_roots.collect());
    let root = *root_tree.last().expect("a tree has at least its root");
    let witness = DaWitness {
        codewords,
        blob_trees,
        root_tree,
    };
    (root, witness)
}

/// The root of a padding blob, the zero codeword.
pub fn padding_root() -> Hash {
    padding_tree()[BLOB_TREE - 1]
}

/// The tree of a padding blob, over `ℓ` copies of the zero cell's digest.
fn padding_tree() -> Vec<Hash> {
    tree_from_leaves(vec![hash(&[0u8; CELL_SYMBOLS * size_of::<u64>()]); CELLS_PER_ROW])
}

/// Every blob's tree, its leaves `e_{i,j} = H(W_{i,j})`, a padding blob's copied in.
#[tracing::instrument(name = "Hashing blobs", skip_all)]
fn blob_trees(codewords: &[u64]) -> Vec<Hash> {
    let m = CODEWORD_SYMBOLS;
    let n_rows = row_count(codewords.len(), m);
    let padding = padding_tree();
    let mut trees = vec![Hash::default(); n_rows.next_power_of_two() * BLOB_TREE];
    parallel::chunks_mut(&mut trees, BLOB_TREE, |i, tree| {
        if i < n_rows {
            hash_many(
                as_bytes(&codewords[i * m..(i + 1) * m]),
                CELL_SYMBOLS * size_of::<u64>(),
                tree[..CELLS_PER_ROW].as_flattened_mut(),
            );
            fill_levels(tree);
        } else {
            tree.copy_from_slice(&padding);
        }
    });
    trees
}

/// The flat Merkle tree over leaves that are already digests: see [`fill_levels`].
fn tree_from_leaves(mut tree: Vec<Hash>) -> Vec<Hash> {
    let n = tree.len();
    assert!(n.is_power_of_two(), "leaf count must be a power of two");
    tree.resize(2 * n - 1, Hash::default());
    fill_levels(&mut tree);
    tree
}

/// Fill a flat tree whose `n` leaves sit in `tree[..n]`: each level follows in turn, the root
/// last. Unlike [`pcs::merkle`] the leaves are not re-hashed, since a cell digest is already the leaf.
fn fill_levels(tree: &mut [Hash]) {
    let (mut base, mut width) = (0, tree.len().div_ceil(2));
    while width > 1 {
        let (read, write) = tree.split_at_mut(base + width);
        hash_many(
            read[base..].as_flattened(),
            2 * OUT_LEN,
            write[..width / 2].as_flattened_mut(),
        );
        base += width;
        width /= 2;
    }
}

fn as_bytes(data: &[u64]) -> &[u8] {
    const { assert!(cfg!(target_endian = "little"), "digests use little-endian symbols") };
    // SAFETY: u64 has no padding; the endian check fixes the byte representation.
    unsafe { core::slice::from_raw_parts(data.as_ptr().cast::<u8>(), size_of_val(data)) }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::DA_MAX_ROWS;
    use fiat_shamir::merkle::hash_pair;
    use rand::{Rng, SeedableRng, rngs::StdRng};

    fn payload(n_rows: usize, seed: u64) -> Vec<u64> {
        let mut rng = StdRng::seed_from_u64(seed);
        (0..n_rows * BLOB_SYMBOLS).map(|_| rng.random()).collect()
    }

    /// Rebuilt pairwise from scratch, independently of the flat layout's offsets: each blob root
    /// is the root over its own cells, and the commitment the root over the blob roots, padded
    /// with the zero codeword's.
    #[test]
    fn commitment_is_the_tree_of_blob_trees() {
        fn root(mut level: Vec<Hash>) -> Hash {
            while level.len() > 1 {
                level = level.chunks(2).map(|pair| hash_pair(&pair[0], &pair[1])).collect();
            }
            level[0]
        }
        let n_rows = 5usize;
        let codewords = encode_rows(&payload(n_rows, 1));
        let (commitment, witness) = commit_codewords(codewords.clone());
        let zero = vec![0; CODEWORD_SYMBOLS];

        let mut blob_roots = Vec::new();
        for i in 0..n_rows.next_power_of_two() {
            let blob = codewords.chunks(CODEWORD_SYMBOLS).nth(i).unwrap_or(&zero);
            let cells: Vec<Hash> = blob.chunks(CELL_SYMBOLS).map(|cell| hash(as_bytes(cell))).collect();
            assert_eq!(witness.blob_tree(i)[..CELLS_PER_ROW], cells, "blob {i}'s leaves");
            blob_roots.push(root(cells));
            assert_eq!(witness.blob_tree(i)[BLOB_TREE - 1], blob_roots[i], "blob {i}'s root");
        }
        assert_eq!(witness.blob_roots(), blob_roots);
        assert_eq!(commitment, root(blob_roots));
    }

    /// Padding rows are zero codewords sharing one root. A payload whose
    /// real rows are unchanged must commit identically whether or not the row count
    /// happens to be a power of two, up to the padding the shape declares.
    #[test]
    fn padding_rows_are_the_zero_codeword() {
        let n_rows = 3usize;
        let rows = payload(n_rows, 3);
        let mut extended = rows.clone();
        extended.extend(std::iter::repeat_n(0, BLOB_SYMBOLS));

        let (short, _) = commit(&rows).unwrap();
        let (long, _) = commit(&extended).unwrap();
        assert_eq!(short, long);
    }

    #[test]
    fn commit_rejects_payloads_that_are_not_whole_blobs_within_the_limit() {
        // Empty, one symbol short of or past one blob, and one blob past the limit.
        for symbols in [0, BLOB_SYMBOLS - 1, BLOB_SYMBOLS + 1, (DA_MAX_ROWS + 1) * BLOB_SYMBOLS] {
            let rows = vec![0; symbols];
            assert_eq!(commit(&rows).err(), Some(BlobSizeError { symbols }));
        }
    }
}
