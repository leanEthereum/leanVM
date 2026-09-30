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

use leanvm_guest::Blake2s;

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
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Error {
    /// No rows, or more than a commitment holds.
    RowCount,
    /// This row is not orthogonal to `L`, so not a codeword.
    NotACodeword(usize),
}

/// Check that every row is a codeword, and return the public values: the root and `H(L)`.
///
/// The scratch holds the cell digests: one row of them per row, padding included.
///
/// # Errors
///
/// A row count out of range, or the first row that is not a codeword.
pub fn check(dual: &[Dual; M], rows: &[[u64; M]], cells: &mut [[Hash; CELLS]]) -> Result<[Hash; 2], Error> {
    // SAFETY: zero is a valid `u64`.
    // Why zeroed: one `memset`, where an array expression copies each window.
    let mut buckets: Buckets = unsafe { core::mem::zeroed() };
    // Membership first: the commitment is only worth computing over codewords.
    for (i, row) in rows.iter().enumerate() {
        if !is_orthogonal(&mut buckets, dual, row) {
            return Err(Error::NotACodeword(i));
        }
    }
    Ok([commit(rows, cells)?, dual_digest(dual)])
}

/// The commitment's root `H(root_row, root_col)`.
///
/// # Errors
///
/// No rows, or more than a commitment holds.
pub fn commit(rows: &[[u64; M]], cells: &mut [[Hash; CELLS]]) -> Result<Hash, Error> {
    if rows.is_empty() || rows.len() > MAX_ROWS {
        return Err(Error::RowCount);
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
    let mut hasher = Blake2s::new();
    hasher.update_words(left).update_words(right);
    hasher.finalize_words()
}

/// BLAKE2s of the little-endian bytes of some words.
fn hash(words: &[u64]) -> Hash {
    let mut hasher = Blake2s::new();
    hasher.update_words(words);
    hasher.finalize_words()
}

/// Bits of a symbol one bucket index takes.
///
/// Eleven covers a symbol in six windows, with a mask that fits one `andi`.
///
/// Its buckets take 384 KiB of RAM, where thirteen bits (five windows) would not fit 1 MiB.
const WINDOW: usize = 11;
const WINDOWS: usize = 64usize.div_ceil(WINDOW);

/// The inner product `<L, w>` with no field multiplication, for a machine without carry-less products.
///
/// Split each symbol into windows: `w_x = sum_q t^(11q) * v_{x,q}(t)`, each `v` below `2^11`.
///
/// ```text
///   <L, w> = sum_q t^(11q) * sum_v v(t) * B[q][v],    B[q][v] = XOR of L_x over x with v_{x,q} = v
/// ```
///
/// So each window of each symbol costs one XOR of `L_x` into its bucket.
///
/// One fold per row then weighs the buckets, and one reduction per limb ends it.
///
/// `B[q][v]` holds three limbs and one spare, so an index is a shift.
type Buckets = [[[u64; 4]; 1 << WINDOW]; WINDOWS];

/// Whether `sum_x L_x * w_x`, in `GF(2^64)` limb by limb, is zero.
///
/// The buckets start zero, and weighing them leaves them zero.
fn is_orthogonal(buckets: &mut Buckets, dual: &[Dual; M], row: &[u64; M]) -> bool {
    const MASK: u64 = (1 << WINDOW) - 1;
    // Phase 1: each window of each symbol XORs the symbol's `L_x` into its bucket.
    //
    //     w_x = 0x...  -> windows v_0 = bits 0..11, v_1 = bits 11..22, .., v_5 = bits 55..64
    //     B[q][v_q] ^= L_x   for q = 0..6
    for (l, &w) in dual.iter().zip(row) {
        for (q, window) in buckets.iter_mut().enumerate() {
            let bucket = &mut window[((w >> (WINDOW * q)) & MASK) as usize];
            bucket[0] ^= l[0];
            bucket[1] ^= l[1];
            bucket[2] ^= l[2];
        }
    }
    // Phase 2: weigh each window's buckets, shift it into place, and sum.
    //
    // Degree below 128: the top window holds 9 bits, so `63 + 8 + 55 < 128`.
    let mut product = [0u128; 3];
    for (q, window) in buckets.iter_mut().enumerate() {
        for (p, s) in product.iter_mut().zip(weigh(window)) {
            *p ^= s << (WINDOW * q);
        }
    }
    // Phase 3: reduce each limb once, as reduction is linear.
    product.iter().all(|&p| reduce(p) == 0)
}

/// `sum_v v(t) * B[v]`, per limb, as unreduced polynomials.
///
/// Halving from the top bit: `sum_v v(t) B[v] = sum_j t^j * (XOR of B[v] over v with bit j)`.
///
/// Folding the top half onto the bottom leaves the sums for the lower bits.
///
/// Each bucket is zeroed once folded, so the next row starts from zero.
fn weigh(buckets: &mut [[u64; 4]; 1 << WINDOW]) -> [u128; 3] {
    let mut weighted = [0u128; 3];
    // At bit `j` the live buckets are the first `2^(j+1)`, indexed by the low `j + 1` bits of `v`.
    //
    //     j = 10:  [ bit 10 clear: 0..1024 | bit 10 set: 1024..2048 ]
    //              the top half sums to the coefficient of t^10, then folds onto the bottom
    for j in (0..WINDOW).rev() {
        let (low, high) = buckets[..2 << j].split_at_mut(1 << j);
        let mut sum = [0u64; 3];
        for (lo, hi) in low.iter_mut().zip(high.iter_mut()) {
            for c in 0..3 {
                sum[c] ^= hi[c];
                lo[c] ^= hi[c];
                hi[c] = 0;
            }
        }
        for (w, s) in weighted.iter_mut().zip(sum) {
            *w ^= u128::from(s) << j;
        }
    }
    // What is left is the XOR of all buckets, which `v = 0` weighs by zero.
    buckets[0] = [0; 4];
    weighted
}

/// Reduce a carry-less product of degree below 128 modulo `t^64 + t^4 + t^3 + t + 1`.
///
/// ```text
///   hi * t^64 = f(hi),     f(v) = v ^ v<<1 ^ v<<3 ^ v<<4
///   the 4 bits f shifts past t^63 fold back once more, in 8 bits
/// ```
fn reduce(p: u128) -> u64 {
    let (lo, hi) = (p as u64, (p >> 64) as u64);
    // Folding the spill into `hi` first merges the two folds, as `f` is linear.
    let v = hi ^ (hi >> 63) ^ (hi >> 61) ^ (hi >> 60);
    lo ^ v ^ (v << 1) ^ (v << 3) ^ (v << 4)
}
