//! LeanDA over `E = GF(2^128)` with Keccak-256, following
//! <https://ethresear.ch/t/leanda-design-and-benchmark/25642>.
//!
//! Each payload row contains `k` symbols of `E`, a VM word each, systematically encoded to
//! `m = 2k` evaluations on an additive domain inside `K = GF(2^64)`. The domain and the novel
//! basis lie in `K`, so a codeword is two `K`-codewords interleaved, one per limb. Each encoded
//! row, a blob, has a Merkle root over its cell digests, and the commitment is the Merkle root
//! over the blob roots. A row belongs to the code iff it is orthogonal to a membership vector the
//! root's challenge determines, with high probability over that challenge (`membership`). The
//! aggregation guest proves this check together with the commitment.
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
pub const LOG_BLOB_SYMBOLS: usize = 13;
/// Symbols per sampling cell, as a logarithm (2 KiB).
pub const LOG_CELL_SYMBOLS: usize = 7;
/// Maximum blobs in one commitment, a power of two: the matrix pads its rows to one.
pub const DA_MAX_ROWS: usize = 32;
const _: () = assert!(DA_MAX_ROWS.is_power_of_two());

/// Symbols in one payload blob.
pub const BLOB_SYMBOLS: usize = 1 << LOG_BLOB_SYMBOLS;
/// Symbols in one encoded blob.
pub const CODEWORD_SYMBOLS: usize = 2 * BLOB_SYMBOLS;
/// Symbols in one sampling cell.
pub const CELL_SYMBOLS: usize = 1 << LOG_CELL_SYMBOLS;
/// Sampling cells in one encoded blob.
pub const CELLS_PER_ROW: usize = CODEWORD_SYMBOLS / CELL_SYMBOLS;
const LOG_CODEWORD_SYMBOLS: usize = LOG_BLOB_SYMBOLS + 1;

/// A symbol: the element `c0 + c1·y` of `E`, its low 64 bits `c0` and its high 64 bits `c1`.
/// Every bit pattern is a symbol, and its bytes are the 128-bit word's, little-endian.
pub type Symbol = u128;
/// A payload blob: [`BLOB_SYMBOLS`] symbols.
pub type Blob = [Symbol; BLOB_SYMBOLS];
/// An encoded blob: [`CODEWORD_SYMBOLS`] symbols, the blob's own first.
pub type Codeword = [Symbol; CODEWORD_SYMBOLS];

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
