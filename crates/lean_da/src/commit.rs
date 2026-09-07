//! Two commitment branches over the same cell digests.
//!
//! A row digest hashes its first `k/c` cell digests, covering the systematic
//! payload. A Merkle tree over these digests gives `root_row`.
//! A second tree has all cell digests as leaves, in column-major order; its
//! intermediate column roots authenticate samples, and its root is `root_col`.
//! The final commitment is `H(root_row, root_col)`.

use fiat_shamir::merkle::{Hash, hash_pair};
use primitives::hash::{OUT_LEN, hash, hash_many_dyn};

use crate::{CELL_SYMBOLS, CELLS_PER_ROW, CODEWORD_SYMBOLS, PAYLOAD_CELLS, encode_rows, row_count};

/// What the builder publishes.
#[derive(Clone, Copy, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct DaCommitment {
    /// `H(root_row, root_col)`, binding the matrix including its zero padding.
    pub root: Hash,
    pub root_row: Hash,
    pub root_col: Hash,
}

/// What the builder keeps, to answer samples and to feed the proof.
pub struct DaWitness {
    /// `n_rows · m` symbols, row-major. Padding rows are zero and not stored.
    pub codewords: Vec<u64>,
    /// `n_rows · ℓ` cell digests, row-major.
    pub cell_digests: Vec<Hash>,
    /// The flat tree over the column-major cell digests; see the module docs.
    pub column_tree: Vec<Hash>,
    /// The flat tree over the `n_padded` row digests.
    pub row_tree: Vec<Hash>,
}

impl DaWitness {
    /// The `ℓ` column roots `C_j`, the level at height `log n_padded`.
    pub fn column_roots(&self) -> &[Hash] {
        let (n_pad, cells) = (
            row_count(self.codewords.len(), CODEWORD_SYMBOLS).next_power_of_two(),
            CELLS_PER_ROW,
        );
        let offset = 2 * n_pad * cells - 2 * cells;
        &self.column_tree[offset..offset + cells]
    }
}

/// Commit to payload rows of little-endian 64-bit symbols and their systematic encoding.
#[tracing::instrument(name = "Commit", skip_all)]
pub fn commit(rows: &[u64]) -> (DaCommitment, DaWitness) {
    let codewords = encode_rows(rows);
    commit_codewords(codewords)
}

/// [`commit`] over rows that are already encoded.
pub fn commit_codewords(codewords: Vec<u64>) -> (DaCommitment, DaWitness) {
    let n_rows = row_count(codewords.len(), CODEWORD_SYMBOLS);
    let (cells, n_pad, t) = (CELLS_PER_ROW, n_rows.next_power_of_two(), PAYLOAD_CELLS);
    let cell_digests = hash_cells(&codewords);
    let (padding_cell, padding_row) = padding_digests();

    // Row branch: hash each payload's cell digests.
    let mut prefixes = vec![Hash::default(); n_rows * t];
    parallel::chunks_mut(&mut prefixes, t, |i, prefix| {
        prefix.copy_from_slice(&cell_digests[i * cells..i * cells + t]);
    });
    let mut row_digests = vec![padding_row; n_pad];
    hash_many_dyn(
        prefixes.as_flattened(),
        t * OUT_LEN,
        row_digests[..n_rows].as_flattened_mut(),
    );
    drop(prefixes);
    let row_tree = tree_from_leaves(row_digests);

    // Column branch: the same digests, column-major, one tree carrying both levels.
    let mut column_major = vec![Hash::default(); cells * n_pad];
    parallel::chunks_mut(&mut column_major, n_pad, |j, column| {
        for (i, slot) in column.iter_mut().enumerate() {
            *slot = if i < n_rows {
                cell_digests[i * cells + j]
            } else {
                padding_cell
            };
        }
    });
    let column_tree = tree_from_leaves(column_major);

    let (root_row, root_col) = (*row_tree.last().unwrap(), *column_tree.last().unwrap());
    let commitment = DaCommitment {
        root: hash_pair(&root_row, &root_col),
        root_row,
        root_col,
    };
    let witness = DaWitness {
        codewords,
        cell_digests,
        column_tree,
        row_tree,
    };
    (commitment, witness)
}

/// Shape-dependent padding digests: the zero cell and its repeated digest for a row.
pub fn padding_digests() -> (Hash, Hash) {
    let cell = hash(&[0u8; CELL_SYMBOLS * size_of::<u64>()]);
    (cell, hash([cell; PAYLOAD_CELLS].as_flattened()))
}

/// `e_{i,j} = H(W_{i,j})` for every cell of every real row, row-major.
#[tracing::instrument(name = "Hashing cells", skip_all)]
fn hash_cells(codewords: &[u64]) -> Vec<Hash> {
    let (cells, m) = (CELLS_PER_ROW, CODEWORD_SYMBOLS);
    let n_rows = codewords.len() / m;
    let mut digests = vec![Hash::default(); n_rows * cells];
    parallel::chunks_mut(&mut digests, cells, |i, row| {
        hash_many_dyn(
            as_bytes(&codewords[i * m..(i + 1) * m]),
            CELL_SYMBOLS * size_of::<u64>(),
            row.as_flattened_mut(),
        );
    });
    digests
}

/// The flat Merkle tree over leaves that are already digests: `tree[..n]` is the
/// leaves, then each level in turn, the root last. Unlike [`pcs::merkle`] the
/// leaves are not re-hashed, since a cell digest is already the leaf.
fn tree_from_leaves(mut tree: Vec<Hash>) -> Vec<Hash> {
    let n = tree.len();
    assert!(n.is_power_of_two(), "leaf count must be a power of two");
    tree.resize(2 * n - 1, Hash::default());

    let (mut base, mut width) = (0, n);
    while width > 1 {
        let (read, write) = tree.split_at_mut(base + width);
        hash_many_dyn(
            read[base..].as_flattened(),
            2 * OUT_LEN,
            write[..width / 2].as_flattened_mut(),
        );
        base += width;
        width /= 2;
    }
    tree
}

fn as_bytes(data: &[u64]) -> &[u8] {
    const { assert!(cfg!(target_endian = "little"), "digests use little-endian symbols") };
    // SAFETY: u64 has no padding; the endian check fixes the byte representation.
    unsafe { core::slice::from_raw_parts(data.as_ptr().cast::<u8>(), size_of_val(data)) }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::BLOB_SYMBOLS;
    use rand::{Rng, SeedableRng, rngs::StdRng};

    fn payload(n_rows: usize, seed: u64) -> Vec<u64> {
        let mut rng = StdRng::seed_from_u64(seed);
        (0..n_rows * BLOB_SYMBOLS).map(|_| rng.random()).collect()
    }

    /// `column_roots` indexes into the flat tree by an offset derived from the
    /// shape, which is the easiest thing here to get wrong by a level. Each one has
    /// to be the root of its own column's subtree, rebuilt independently.
    #[test]
    fn column_roots_are_their_own_subtrees() {
        let n_rows = 5usize;
        let (_, witness) = commit(&payload(n_rows, 1));
        let (n_pad, cells) = (n_rows.next_power_of_two(), CELLS_PER_ROW);
        let padding_cell = hash(&[0u8; CELL_SYMBOLS * size_of::<u64>()]);

        for (j, &got) in witness.column_roots().iter().enumerate() {
            let column: Vec<Hash> = (0..n_pad)
                .map(|i| {
                    if i < n_rows {
                        witness.cell_digests[i * cells + j]
                    } else {
                        padding_cell
                    }
                })
                .collect();
            assert_eq!(got, *tree_from_leaves(column).last().unwrap(), "column {j}");
        }
    }

    /// Both branches have to be binding, and independently so: a change inside the
    /// first half must move `root_row`, and a change in the second half must
    /// still move `root_col` even though no row digest covers it.
    #[test]
    fn both_branches_bind() {
        let n_rows = 3usize;
        let codewords = crate::encode_rows(&payload(n_rows, 2));
        let (base, _) = commit_codewords(codewords.clone());

        for &position in &[0usize, BLOB_SYMBOLS - 1, BLOB_SYMBOLS, CODEWORD_SYMBOLS - 1] {
            let mut corrupted = codewords.clone();
            corrupted[position] ^= 1;
            let (moved, _) = commit_codewords(corrupted);
            assert_ne!(moved.root, base.root, "root ignored a flip at {position}");
            assert_ne!(moved.root_col, base.root_col, "root_col ignored a flip at {position}");
            if position < BLOB_SYMBOLS {
                assert_ne!(moved.root_row, base.root_row, "root_row ignored a payload flip");
            }
        }
    }

    /// Padding rows are zero codewords sharing one cell digest. A payload whose
    /// real rows are unchanged must commit identically whether or not the row count
    /// happens to be a power of two, up to the padding the shape declares.
    #[test]
    fn padding_rows_are_the_zero_codeword() {
        let n_rows = 3usize;
        let rows = payload(n_rows, 3);
        let mut extended = rows.clone();
        extended.extend(std::iter::repeat_n(0, BLOB_SYMBOLS));

        let (short, _) = commit(&rows);
        let (long, _) = commit(&extended);
        assert_eq!(short.root, long.root);
    }
}
