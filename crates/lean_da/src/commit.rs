//! A Merkle tree per blob, then one over the blob roots.
//!
//! A blob's leaves are its `ℓ = m/c` cell digests, so the left subtree of its root covers the
//! systematic payload and a sampled cell opens against its blob root. The blob roots, padded with
//! the zero codeword's to a power of two, are the leaves of the commitment's tree.

use fiat_shamir::merkle::Hash;
use primitives::hash::{OUT_LEN, hash, hash_many};

use crate::{Blob, BlobCountError, CELL_SYMBOLS, CELLS_PER_ROW, Codeword, DA_MAX_ROWS, encode::encode_rows};

/// Digests in one blob's flat tree.
const BLOB_TREE: usize = 2 * CELLS_PER_ROW - 1;

/// The encoded pq-blobs. Store this to be able to answer sample requests, or
/// to aggregate the pq-blobs in a STARK with leanVM.
pub struct DaWitness {
    /// One codeword per blob. Padding rows are zero and not stored.
    codewords: Vec<Codeword>,
    /// The root of the tree over the blob roots.
    root: Hash,
}

impl DaWitness {
    /// Blob `i`, encoded: `CODEWORD_SYMBOLS` symbols, or `None` if `i` is not below the number of
    /// blobs. The encoding is systematic: the first `BLOB_SYMBOLS` symbols are the blob itself, the
    /// rest its redundancy, and any `BLOB_SYMBOLS` of them recover it.
    pub fn row(&self, i: usize) -> Option<&Codeword> {
        self.codewords.get(i)
    }

    /// Column `j`, what a sample reads: cell `j` of each blob, `CELL_SYMBOLS` symbols each, or
    /// `None` if `j` is not below `CELLS_PER_ROW`.
    pub fn column(&self, j: usize) -> Option<impl Iterator<Item = &[u64; CELL_SYMBOLS]>> {
        (j < CELLS_PER_ROW).then(|| self.codewords.iter().map(move |row| &row.as_chunks().0[j]))
    }

    /// The commitment the builder publishes: the root of the tree over the blob roots.
    pub fn root(&self) -> Hash {
        self.root
    }
}

/// Encode the blobs and commit to them; [`DaWitness::root`] is the commitment.
///
/// # Errors
///
/// If there are not 1 to [`DA_MAX_ROWS`] blobs.
#[tracing::instrument(name = "Commit", skip_all)]
pub fn commit(blobs: &[Blob]) -> Result<DaWitness, BlobCountError> {
    if !(1..=DA_MAX_ROWS).contains(&blobs.len()) {
        return Err(BlobCountError { blobs: blobs.len() });
    }
    let codewords = encode_rows(blobs);
    let blob_roots = blob_trees(&codewords)
        .as_chunks::<BLOB_TREE>()
        .0
        .iter()
        .map(|tree| tree[BLOB_TREE - 1])
        .collect();
    let root = *tree_from_leaves(blob_roots)
        .last()
        .expect("a matrix has at least one blob");
    Ok(DaWitness { codewords, root })
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
fn blob_trees(codewords: &[Codeword]) -> Vec<Hash> {
    let n_rows = codewords.len();
    let padding = padding_tree();
    let mut trees = vec![Hash::default(); n_rows.next_power_of_two() * BLOB_TREE];
    parallel::chunks_mut(&mut trees, BLOB_TREE, |i, tree| {
        if i < n_rows {
            hash_many(
                as_bytes(&codewords[i]),
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
    primitives::cast_slice(data)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{BLOB_SYMBOLS, CODEWORD_SYMBOLS};
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
        let blobs = payload(n_rows, 1);
        let codewords = encode_rows(blobs.as_chunks().0);
        let witness = commit(blobs.as_chunks().0).unwrap();
        let trees = blob_trees(&codewords);
        let zero = vec![0; CODEWORD_SYMBOLS];

        let mut blob_roots = Vec::new();
        for i in 0..n_rows.next_power_of_two() {
            let blob = codewords.get(i).map_or(&zero[..], |codeword| &codeword[..]);
            let cells: Vec<Hash> = blob.chunks(CELL_SYMBOLS).map(|cell| hash(as_bytes(cell))).collect();
            assert_eq!(
                trees.as_chunks::<BLOB_TREE>().0[i][..CELLS_PER_ROW],
                cells,
                "blob {i}'s leaves"
            );
            blob_roots.push(root(cells));
            assert_eq!(
                trees.as_chunks::<BLOB_TREE>().0[i][BLOB_TREE - 1],
                blob_roots[i],
                "blob {i}'s root"
            );
        }
        for (i, row) in codewords.iter().enumerate() {
            assert_eq!(witness.row(i), Some(row));
        }
        assert!(witness.row(n_rows).is_none());
        for j in [0, CELLS_PER_ROW - 1] {
            let column: Vec<&[u64]> = witness.column(j).unwrap().map(|cell| &cell[..]).collect();
            let cells: Vec<&[u64]> = codewords
                .iter()
                .map(|row| &row[j * CELL_SYMBOLS..(j + 1) * CELL_SYMBOLS])
                .collect();
            assert_eq!(column, cells);
        }
        assert!(witness.column(CELLS_PER_ROW).is_none());
        assert_eq!(witness.root(), root(blob_roots));
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

        assert_eq!(
            commit(rows.as_chunks().0).unwrap().root(),
            commit(extended.as_chunks().0).unwrap().root()
        );
    }
}
