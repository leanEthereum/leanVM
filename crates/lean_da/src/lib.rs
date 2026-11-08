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

pub use commit::{DaWitness, commit, commit_codewords, padding_root};
pub use encode::encode_rows;
pub use membership::subspace_above;

/// Payload symbols per blob, as a logarithm (128 KiB).
pub const DA_LOG_K: usize = 14;
/// Symbols per sampling cell, as a logarithm (2 KiB).
pub const DA_LOG_CELL: usize = 8;
/// Maximum blobs in one commitment.
pub const DA_MAX_ROWS: usize = 1024;

/// 64-bit symbols in one payload blob.
pub const BLOB_SYMBOLS: usize = 1 << DA_LOG_K;
/// 64-bit symbols in one encoded blob.
pub const CODEWORD_SYMBOLS: usize = 2 * BLOB_SYMBOLS;
/// 64-bit symbols in one sampling cell.
pub const CELL_SYMBOLS: usize = 1 << DA_LOG_CELL;
/// Sampling cells in one encoded blob.
pub const CELLS_PER_ROW: usize = CODEWORD_SYMBOLS / CELL_SYMBOLS;
const LOG_M: usize = DA_LOG_K + 1;

/// The payload is not 1 to [`DA_MAX_ROWS`] full blobs.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct BlobSizeError {
    /// The payload's length in symbols.
    pub symbols: usize,
}

impl std::fmt::Display for BlobSizeError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{} symbols: expected 1 to {DA_MAX_ROWS} full blobs of {BLOB_SYMBOLS} symbols",
            self.symbols
        )
    }
}

impl std::error::Error for BlobSizeError {}

/// How many `width`-symbol rows `symbols` symbols fill, or `None` if that is not 1 to [`DA_MAX_ROWS`] full rows.
fn row_count(symbols: usize, width: usize) -> Option<usize> {
    let rows = symbols / width;
    (symbols.is_multiple_of(width) && (1..=DA_MAX_ROWS).contains(&rows)).then_some(rows)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn row_counts_reject_empty_partial_and_oversized_inputs() {
        for width in [BLOB_SYMBOLS, CODEWORD_SYMBOLS] {
            assert_eq!(row_count(width, width), Some(1));
            assert_eq!(row_count(DA_MAX_ROWS * width, width), Some(DA_MAX_ROWS));
            for symbols in [0, width - 1, width + 1, (DA_MAX_ROWS + 1) * width, usize::MAX] {
                assert_eq!(row_count(symbols, width), None);
            }
        }
    }
}
