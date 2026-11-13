//! LeanDA over `K = GF(2^64)` with Keccak-256, following
//! <https://ethresear.ch/t/leanda-design-and-benchmark/25642>.
//!
//! Each payload row contains `k` symbols, systematically encoded to `m = 2k`
//! evaluations on an additive domain. Each encoded row, a blob, has a Merkle root
//! over its cell digests, and the commitment is the Merkle root over the blob roots.
//! A row belongs to the code iff it is orthogonal to a membership vector the root's
//! challenge determines, with high probability over that challenge (`membership`).
//! The aggregation guest proves this check together with the commitment.
//!
//! Row and cell widths are powers of two. The tree over the blob roots pads the row
//! count with zero rows. A root binds this padded matrix, not the original row count:
//! a trailing zero row is indistinguishable from padding within the same padded height.

mod commit;
mod encode;
mod membership;

pub use commit::{DaWitness, commit, padding_root};
pub use membership::subspace_above;

/// Payload symbols per blob, as a logarithm (128 KiB).
pub const LOG_BLOB_SYMBOLS: usize = 14;
pub const LOG_CELL_SYMBOLS: usize = 8;
/// Maximum blobs in one commitment, a power of two: the matrix pads its rows to one.
pub const DA_MAX_ROWS: usize = 32;
const _: () = assert!(DA_MAX_ROWS.is_power_of_two());

/// 64-bit symbols in one payload blob.
pub const BLOB_SYMBOLS: usize = 1 << LOG_BLOB_SYMBOLS;
/// 64-bit symbols in one encoded blob.
pub const CODEWORD_SYMBOLS: usize = 2 * BLOB_SYMBOLS;
/// 64-bit symbols in one sampling cell.
pub const CELL_SYMBOLS: usize = 1 << LOG_CELL_SYMBOLS;
/// Sampling cells in one encoded blob.
pub const CELLS_PER_ROW: usize = CODEWORD_SYMBOLS / CELL_SYMBOLS;
const LOG_CODEWORD_SYMBOLS: usize = LOG_BLOB_SYMBOLS + 1;

/// A payload blob: [`BLOB_SYMBOLS`] symbols, little-endian 64-bit words.
pub type Blob = [u64; BLOB_SYMBOLS];
/// An encoded blob: [`CODEWORD_SYMBOLS`] symbols, the blob's own first.
pub type Codeword = [u64; CODEWORD_SYMBOLS];

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
