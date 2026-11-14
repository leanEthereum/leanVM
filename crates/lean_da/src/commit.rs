use fiat_shamir::merkle::{Hash, hash_pair};
use primitives::hash::{OUT_LEN, hash, hash_many};

use crate::{Blob, CELL_SYMBOLS, CELLS_PER_ROW, Codeword, DA_MAX_ROWS, Symbol, encode::encode_rows};

/// Nodes in one blob's flat Merkle tree.
const BLOB_MERKLE_NODES: usize = 2 * CELLS_PER_ROW - 1;

/// The encoded blobs and their Merkle trees: what a builder keeps to answer samples and to
/// aggregate the blobs with leanVM.
pub struct DaWitness {
    /// One codeword per blob; the zero padding rows are not stored.
    codewords: Vec<Codeword>,
    /// Each padded blob's flat Merkle tree: its cell digests, then each level, its root last.
    blob_merkle_nodes: Vec<Hash>,
    /// The flat Merkle tree over the blob roots, its root last.
    root_merkle_nodes: Vec<Hash>,
}

impl DaWitness {
    /// Encode the blobs and commit to them.
    ///
    /// # Errors
    ///
    /// If there are not 1 to [`DA_MAX_ROWS`] blobs.
    #[tracing::instrument(name = "Commit", skip_all)]
    pub fn build(blobs: &[Blob]) -> Result<Self, BlobCountError> {
        if !(1..=DA_MAX_ROWS).contains(&blobs.len()) {
            return Err(BlobCountError { blobs: blobs.len() });
        }
        let codewords = encode_rows(blobs);
        let blob_merkle_nodes = blob_merkle_nodes(&codewords);
        let blob_roots = blob_merkle_nodes
            .as_chunks::<BLOB_MERKLE_NODES>()
            .0
            .iter()
            .map(|tree| tree[BLOB_MERKLE_NODES - 1])
            .collect();
        let root_merkle_nodes = merkle_nodes_from_leaves(blob_roots);
        Ok(Self {
            codewords,
            blob_merkle_nodes,
            root_merkle_nodes,
        })
    }

    /// The number of blobs, without padding.
    pub fn n_blobs(&self) -> usize {
        self.codewords.len()
    }

    /// Blob `blob_idx`, encoded (`None` out of range). The encoding is systematic: the first
    /// `BLOB_SYMBOLS` symbols are the blob, and any `BLOB_SYMBOLS` of them recover it.
    pub fn row(&self, blob_idx: usize) -> Option<&Codeword> {
        self.codewords.get(blob_idx)
    }

    /// Cell `col_idx` of every blob (`None` out of range).
    pub fn column(&self, col_idx: usize) -> Option<impl Iterator<Item = &[Symbol; CELL_SYMBOLS]>> {
        (col_idx < CELLS_PER_ROW).then(|| (0..self.n_blobs()).filter_map(move |blob_idx| self.cell(blob_idx, col_idx)))
    }

    /// Cell `col_idx` of blob `blob_idx` (`None` out of range).
    pub fn cell(&self, blob_idx: usize, col_idx: usize) -> Option<&[Symbol; CELL_SYMBOLS]> {
        self.row(blob_idx)?.as_chunks().0.get(col_idx)
    }

    /// The commitment: the root of the tree over the blob roots.
    pub fn top_root(&self) -> Hash {
        *self.root_merkle_nodes.last().expect("a matrix has at least one blob")
    }

    /// The Merkle path of cell `col_idx` of blob `blob_idx`, which [`verify_cell`] checks (`None` out
    /// of range).
    pub fn merkle_path_for_cell(&self, blob_idx: usize, col_idx: usize) -> Option<Vec<Hash>> {
        (blob_idx < self.n_blobs() && col_idx < CELLS_PER_ROW).then(|| {
            let blob_nodes = &self.blob_merkle_nodes.as_chunks::<BLOB_MERKLE_NODES>().0[blob_idx];
            siblings(blob_nodes, col_idx)
                .chain(siblings(&self.root_merkle_nodes, blob_idx))
                .collect()
        })
    }
}

/// The siblings of `leaf` in a flat tree, from the leaves up.
fn siblings(tree: &[Hash], mut leaf: usize) -> impl Iterator<Item = Hash> {
    let (mut base, mut width) = (0, tree.len().div_ceil(2));
    std::iter::from_fn(move || {
        (width > 1).then(|| {
            let sibling = tree[base + (leaf ^ 1)];
            (base, width, leaf) = (base + width, width / 2, leaf / 2);
            sibling
        })
    })
}

/// Whether `path` proves `cell` is cell `col_idx` of blob `blob_idx` under `root`, the commitment to
/// `n_blobs` blobs.
pub fn verify_cell(
    root: &Hash,
    n_blobs: usize,
    blob_idx: usize,
    col_idx: usize,
    cell: &[Symbol; CELL_SYMBOLS],
    path: &[Hash],
) -> bool {
    let depth = CELLS_PER_ROW.ilog2() as usize + n_blobs.next_power_of_two().ilog2() as usize;
    if !(1..=DA_MAX_ROWS).contains(&n_blobs) || blob_idx >= n_blobs || col_idx >= CELLS_PER_ROW || path.len() != depth {
        return false;
    }
    let mut position = CELLS_PER_ROW * blob_idx + col_idx;
    let mut node = hash(as_bytes(cell));
    for sibling in path {
        node = if position.is_multiple_of(2) {
            hash_pair(&node, sibling)
        } else {
            hash_pair(sibling, &node)
        };
        position /= 2;
    }
    node == *root
}

/// The number of blobs is not 1 to [`DA_MAX_ROWS`].
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct BlobCountError {
    /// The number of blobs given.
    pub blobs: usize,
}

impl std::fmt::Display for BlobCountError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{} blobs: expected 1 to {DA_MAX_ROWS}", self.blobs)
    }
}

impl std::error::Error for BlobCountError {}

/// The root of a padding blob, the zero codeword.
pub fn root_of_padding_blob() -> Hash {
    padding_merkle_nodes()[BLOB_MERKLE_NODES - 1]
}

/// A padding blob's flat Merkle tree.
fn padding_merkle_nodes() -> Vec<Hash> {
    merkle_nodes_from_leaves(vec![hash(&[0u8; CELL_SYMBOLS * size_of::<Symbol>()]); CELLS_PER_ROW])
}

/// Each padded blob's flat Merkle tree, its leaves the cell digests.
#[tracing::instrument(name = "Hashing blobs", skip_all)]
fn blob_merkle_nodes(codewords: &[Codeword]) -> Vec<Hash> {
    let n_rows = codewords.len();
    let padding = padding_merkle_nodes();
    let mut trees = vec![Hash::default(); n_rows.next_power_of_two() * BLOB_MERKLE_NODES];
    for (i, tree) in trees.chunks_mut(BLOB_MERKLE_NODES).enumerate() {
        if i < n_rows {
            hash_many(
                as_bytes(&codewords[i]),
                CELL_SYMBOLS * size_of::<Symbol>(),
                tree[..CELLS_PER_ROW].as_flattened_mut(),
            );
            fill_levels(tree);
        } else {
            tree.copy_from_slice(&padding);
        }
    }
    trees
}

/// The flat Merkle tree over `leaves`.
fn merkle_nodes_from_leaves(mut leaves: Vec<Hash>) -> Vec<Hash> {
    let n = leaves.len();
    assert!(n.is_power_of_two(), "leaf count must be a power of two");
    leaves.resize(2 * n - 1, Hash::default());
    fill_levels(&mut leaves);
    leaves
}

/// Fills each level of a flat tree from its leaves, the first half, up to its root, last. Unlike
/// [`pcs::merkle`]'s, the leaves are digests already and are not hashed again.
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

fn as_bytes(data: &[Symbol]) -> &[u8] {
    const { assert!(cfg!(target_endian = "little"), "digests use little-endian symbols") };
    primitives::cast_slice(data)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{BLOB_SYMBOLS, CODEWORD_SYMBOLS};
    use rand::{Rng, SeedableRng, rngs::StdRng};

    fn payload(n_rows: usize, seed: u64) -> Vec<Symbol> {
        let mut rng = StdRng::seed_from_u64(seed);
        (0..n_rows * BLOB_SYMBOLS).map(|_| rng.random()).collect()
    }

    /// Each blob root is the root over its cells, and the commitment the root over the blob roots,
    /// padded with the zero codeword's.
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
        let witness = DaWitness::build(blobs.as_chunks().0).unwrap();
        let trees = blob_merkle_nodes(&codewords);
        let zero = vec![0; CODEWORD_SYMBOLS];

        let mut blob_roots = Vec::new();
        for i in 0..n_rows.next_power_of_two() {
            let blob = codewords.get(i).map_or(&zero[..], |codeword| &codeword[..]);
            let cells: Vec<Hash> = blob.chunks(CELL_SYMBOLS).map(|cell| hash(as_bytes(cell))).collect();
            assert_eq!(
                trees.as_chunks::<BLOB_MERKLE_NODES>().0[i][..CELLS_PER_ROW],
                cells,
                "blob {i}'s leaves"
            );
            blob_roots.push(root(cells));
            assert_eq!(
                trees.as_chunks::<BLOB_MERKLE_NODES>().0[i][BLOB_MERKLE_NODES - 1],
                blob_roots[i],
                "blob {i}'s root"
            );
        }
        for (i, row) in codewords.iter().enumerate() {
            assert_eq!(witness.row(i), Some(row));
        }
        assert!(witness.row(n_rows).is_none());
        for j in [0, CELLS_PER_ROW - 1] {
            let column: Vec<&[Symbol]> = witness.column(j).unwrap().map(|cell| &cell[..]).collect();
            let cells: Vec<&[Symbol]> = codewords
                .iter()
                .map(|row| &row[j * CELL_SYMBOLS..(j + 1) * CELL_SYMBOLS])
                .collect();
            assert_eq!(column, cells);
        }
        assert!(witness.column(CELLS_PER_ROW).is_none());
        assert_eq!(witness.top_root(), root(blob_roots));
    }

    /// A trailing zero blob within the padded height commits like padding.
    #[test]
    fn padding_rows_are_the_zero_codeword() {
        let n_rows = 3usize;
        let rows = payload(n_rows, 3);
        let mut extended = rows.clone();
        extended.extend(std::iter::repeat_n(0, BLOB_SYMBOLS));

        assert_eq!(
            DaWitness::build(rows.as_chunks().0).unwrap().top_root(),
            DaWitness::build(extended.as_chunks().0).unwrap().top_root()
        );
    }

    /// A path proves its cell, and not another cell or position.
    #[test]
    fn openings_verify() {
        let witness = DaWitness::build(payload(3, 5).as_chunks().0).unwrap();
        let root = witness.top_root();
        for (i, j) in [(0, 0), (1, 77), (2, CELLS_PER_ROW - 1)] {
            let cell = *witness.cell(i, j).unwrap();
            let path = witness.merkle_path_for_cell(i, j).unwrap();
            assert!(verify_cell(&root, witness.n_blobs(), i, j, &cell, &path));
            let mut other = cell;
            other[0] ^= 1;
            assert!(!verify_cell(&root, 3, i, j, &other, &path));
            assert!(!verify_cell(&root, 3, i, (j + 1) % CELLS_PER_ROW, &cell, &path));
        }
        assert!(witness.merkle_path_for_cell(3, 0).is_none());
    }
}
