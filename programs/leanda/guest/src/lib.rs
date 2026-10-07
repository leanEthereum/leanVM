//! leanDA's check: blobs that are Reed-Solomon codewords, and their commitment.
//!
//! A blob is `k = 2^14` little-endian 64-bit symbols, encoded at rate 1/2 to `m = 2k`.
//!
//! The encoded blobs are the rows of a matrix, cut into cells of 256 symbols.
//!
//! The commitment `H(root_row, root_col)` has two branches over the cell digests:
//!
//! ```text
//!   root_row   Merkle root of the row digests, each the hash of a row's first 64 cells
//!   root_col   Merkle root of all cell digests in column-major order
//! ```
//!
//! A row is a codeword iff it is orthogonal to a random dual codeword `L`, with high probability.
//!
//! `L` has entries in `GF(2^64)^3`, and is fixed by the root through Fiat-Shamir.
//!
//! It is the codeword of the tensor `(1, z_0) x .. x (1, z_13)`, 14 challenges in `GF(2^192)`.
//!
//! A row that is not a codeword passes with probability at most `14 / 2^192`.
//!
//! The design post checks membership barycentrically over KoalaBear with Poseidon2.
//!
//! This is the binary-field version: `GF(2^64)` symbols, an additive NTT, and BLAKE2s.
//!
//! The guest reads `L` from the advice and cannot sample it, so it commits the root and `H(L)`.
//!
//! A verifier derives `L` from the root, and checks the output against both.
//!
//! Rows past the last blob, up to a power of two, are zero codewords.
//!
//! See <https://ethresear.ch/t/leanda-design-and-benchmark/25642>.
#![no_std]
use leanvm_guest::ext::{ONE, Registers, Y, Y2};
use leanvm_guest::hash_with;
use thiserror::Error;

/// A BLAKE2s-256 digest, as four little-endian words.
pub type Hash = [u64; 4];
/// An entry of the dual codeword `L`: three `GF(2^64)` limbs, little-endian.
pub type Dual = [u64; 3];

/// `log2(k)`: payload symbols per blob, `2^14` (128 KiB).
pub const LOG_K: usize = 14;
/// `m`: symbols per encoded blob.
pub const M: usize = 2 << LOG_K;
/// Symbols per cell (2 KiB).
pub const CELL: usize = 256;
/// Cells per encoded blob.
pub const CELLS: usize = M / CELL;
/// Cells in a blob's payload half, which its row digest covers.
pub const PAYLOAD_CELLS: usize = CELLS / 2;
/// Most blobs one commitment holds, as the leanDA design fixes it.
pub const MAX_ROWS: usize = 1024;

/// Why a matrix is rejected.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Error)]
pub enum DaError {
    /// No rows, or more than a commitment holds.
    #[error("{rows} rows, and a commitment holds 1 to {MAX_ROWS}")]
    RowCount { rows: usize },
    /// This row is not orthogonal to `L`, so not a codeword.
    #[error("row {row} is not a codeword")]
    NotACodeword { row: usize },
}

/// Check that every row is a codeword, and return the public values: the root and `H(L)`.
///
/// The scratch holds the cell digests: one row of them per row, padding included, and `e` is the extension registers.
///
/// # Errors
///
/// A row count out of range, or the first row that is not a codeword.
pub fn check(
    e: &mut Registers,
    dual: &[Dual; M],
    rows: &[[u64; M]],
    cells: &mut [[Hash; CELLS]],
) -> Result<[Hash; 2], DaError> {
    // Membership first: the commitment is only worth computing over codewords.
    for (i, row) in rows.iter().enumerate() {
        if !is_orthogonal(e, dual, row) {
            return Err(DaError::NotACodeword { row: i });
        }
    }
    Ok([commit(rows, cells)?, dual_digest(dual)])
}

/// The commitment's root `H(root_row, root_col)`.
///
/// # Errors
///
/// No rows, or more than a commitment holds.
pub fn commit(rows: &[[u64; M]], cells: &mut [[Hash; CELLS]]) -> Result<Hash, DaError> {
    if rows.is_empty() || rows.len() > MAX_ROWS {
        return Err(DaError::RowCount { rows: rows.len() });
    }
    // For example 3 rows pad to 4, the fourth a zero codeword.
    let padded = rows.len().next_power_of_two();
    let cells = &mut cells[..padded];
    // Every cell of a padding row is the zero cell.
    let pad_cell = hash(&[0; CELL]);
    // The cell digests: 128 per row, 32 compressions each.
    for (digests, row) in cells.iter_mut().zip(rows) {
        for (digest, cell) in digests.iter_mut().zip(row.as_chunks::<CELL>().0) {
            *digest = hash(cell);
        }
    }
    cells[rows.len()..].fill([pad_cell; CELLS]);

    // The row branch: each row's payload cells in one hash, then a tree over the rows.
    //
    // The buffer holds one digest per row, and serves both branches.
    let mut column = [[0; 4]; MAX_ROWS];
    let column = &mut column[..padded];
    for (digest, row) in column.iter_mut().zip(cells.iter()) {
        *digest = hash(row[..PAYLOAD_CELLS].as_flattened());
    }
    let root_row = merkle_root(column);

    // The column branch: a tree over each column, then a tree over the column roots.
    //
    // That is the one tree over all cell digests in column-major order:
    //
    //     leaves  e(0,0) e(1,0) .. e(n-1,0) | e(0,1) .. e(n-1,1) | .. | .. e(n-1,127)
    //     level log n:  one root per column, then 7 levels up to the root
    let mut roots = [[0; 4]; CELLS];
    for (j, root) in roots.iter_mut().enumerate() {
        for (digest, row) in column.iter_mut().zip(cells.iter()) {
            *digest = row[j];
        }
        *root = merkle_root(column);
    }
    Ok(hash_pair(&root_row, &merkle_root(&mut roots)))
}

/// BLAKE2s of `L`, each entry's three limbs in order.
pub fn dual_digest(dual: &[Dual; M]) -> Hash {
    hash(dual.as_flattened())
}

/// The root of a Merkle tree over a power of two of leaves, folded in place.
fn merkle_root(leaves: &mut [Hash]) -> Hash {
    let mut width = leaves.len();
    // Parent `j` reads only children `2j` and `2j + 1`, which no earlier parent overwrote.
    while width > 1 {
        width /= 2;
        for j in 0..width {
            leaves[j] = hash_pair(&leaves[2 * j], &leaves[2 * j + 1]);
        }
    }
    leaves[0]
}

/// BLAKE2s of two digests: a Merkle node, and the commitment's root.
fn hash_pair(left: &Hash, right: &Hash) -> Hash {
    hash_with(|stream| {
        stream.write(*left).write(*right);
    })
}

/// BLAKE2s of the little-endian bytes of some words, whole blocks of them.
///
/// The stream writes each block straight into the one the instruction reads, where the chaining value stays.
fn hash(words: &[u64]) -> Hash {
    let (blocks, []) = words.as_chunks::<8>() else {
        unreachable!("whole blocks")
    };
    hash_with(|stream| {
        stream.write_each(blocks.len(), |i| blocks[i]);
    })
}

/// Whether `sum_x L_x * w_x`, in `GF(2^192)`, is zero.
///
/// Each term multiplies an element of the extension field by a symbol of the base field.
///
/// The machine's product is on its extension registers, so the sum is kept limb by limb of `L`:
///
/// ```text
///     f6 = w_x                   as an element of E
///     f3 += f6 * L_x,0           f4 += f6 * L_x,1           f5 += f6 * L_x,2
///     sum = f3 + y * f4 + y^2 * f5
/// ```
///
/// On the VM the run only goes on if the sum is zero.
fn is_orthogonal(e: &mut Registers, dual: &[Dual; M], row: &[u64; M]) -> bool {
    e.mul_base::<3, ONE>(0);
    e.mul_base::<4, ONE>(0);
    e.mul_base::<5, ONE>(0);
    for (l, &w) in dual.iter().zip(row) {
        e.mul_base::<6, ONE>(w);
        e.mul_add_base::<3, 6>(l[0]);
        e.mul_add_base::<4, 6>(l[1]);
        e.mul_add_base::<5, 6>(l[2]);
    }
    e.mul_add::<3, Y, 4>();
    e.mul_add_is_zero::<3, Y2, 5>()
}
