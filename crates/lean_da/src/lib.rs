//! LeanDA over `E = GF(2^128)` with Keccak-256, following
//! <https://ethresear.ch/t/leanda-design-and-benchmark/25642>.
//!
//! Each payload row contains `k` symbols of `E`, a VM word each, systematically encoded to
//! `m = 2k` evaluations on an additive domain inside `K = GF(2^64)`. Each encoded row, a blob,
//! has a Merkle root over its cell digests, and the commitment is the Merkle root over the blob
//! roots. A row belongs to the code iff it is orthogonal to a membership vector the
//! root's challenge determines, with high probability over that challenge. The
//! aggregation guest proves this check together with the commitment.
//!
//! The tree over the blob roots pads the row count with zero rows, to the next power of two.

mod commit;
mod encode;

pub use commit::{DaWitness, commit, padding_root};

/// Each blob is 128 KiB = 2^LOG_BLOB_SYMBOLS symbols in GF(2^128).
pub const LOG_BLOB_SYMBOLS: usize = 13;
/// Each encoded blob (256 KiB) = 2^LOG_CELL_SYMBOLS 'cells' of 2 KiB each.
pub const LOG_CELL_SYMBOLS: usize = 7;
/// We support at most DA_MAX_ROWS rows.
pub const DA_MAX_ROWS: usize = 32;

/// How many GF(2^128) symbols in one blob.
pub const BLOB_SYMBOLS: usize = 1 << LOG_BLOB_SYMBOLS;
/// How many GF(2^128) symbols in one encoded blob.
pub const CODEWORD_SYMBOLS: usize = 2 * BLOB_SYMBOLS;
/// How many 2 KiB cells in one encoded blob.
pub const CELL_SYMBOLS: usize = 1 << LOG_CELL_SYMBOLS;
/// How many cells in one encoded blob.
pub const CELLS_PER_ROW: usize = CODEWORD_SYMBOLS / CELL_SYMBOLS;
/// How many GF(2^128) symbols in one encoded row.
/// Symbols in one encoded blob, as a logarithm: rate one half.
pub const LOG_CODEWORD_SYMBOLS: usize = LOG_BLOB_SYMBOLS + 1;

pub type Symbol = u128;
pub type Blob = [Symbol; BLOB_SYMBOLS];
pub type Codeword = [Symbol; CODEWORD_SYMBOLS];

const _: () = assert!(DA_MAX_ROWS.is_power_of_two());

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
