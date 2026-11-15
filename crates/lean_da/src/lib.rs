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
//! The matrix always has [`DA_MAX_ROWS`] rows: zero rows pad the blobs, so every cell's Merkle path
//! has [`MERKLE_PATH_LEN`] siblings.

mod commit;
mod encode;

pub use commit::{BlobCountError, BlobMatrix, Hash, MERKLE_PATH_LEN, root_of_padding_blob, verify_cell};

/// Symbols in one blob, as a logarithm: a blob is 128 KiB.
pub use verifier::da::LOG_BLOB_SYMBOLS;
/// Symbols in one cell, as a logarithm: a cell is 2 KiB.
pub const LOG_CELL_SYMBOLS: usize = 7;
/// The matrix's height: at most this many blobs, padded to it with zero rows.
pub const DA_MAX_ROWS: usize = 32;

/// Symbols in one blob.
pub const BLOB_SYMBOLS: usize = 1 << LOG_BLOB_SYMBOLS;
/// Symbols in one encoded blob: rate one half.
pub const CODEWORD_SYMBOLS: usize = 2 * BLOB_SYMBOLS;
/// Symbols in one cell.
pub const CELL_SYMBOLS: usize = 1 << LOG_CELL_SYMBOLS;
/// Cells in one encoded blob.
pub const CELLS_PER_ROW: usize = CODEWORD_SYMBOLS / CELL_SYMBOLS;
/// Symbols in one encoded blob, as a logarithm.
pub const LOG_CODEWORD_SYMBOLS: usize = LOG_BLOB_SYMBOLS + 1;

/// One element of `E`, as its 128 bits.
pub type Symbol = u128;
/// One blob: [`BLOB_SYMBOLS`] symbols.
pub type Blob = [Symbol; BLOB_SYMBOLS];
/// A [`Blob`] encoded at rate one half: [`CODEWORD_SYMBOLS`] symbols.
pub type Codeword = [Symbol; CODEWORD_SYMBOLS];

const _: () = assert!(DA_MAX_ROWS.is_power_of_two());
