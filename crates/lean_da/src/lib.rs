//! LeanDA over `K = GF(2^64)` with BLAKE2s, following
//! <https://ethresear.ch/t/leanda-design-and-benchmark/25642>.
//!
//! Each payload row contains `k` symbols, systematically encoded to `m = 2k`
//! evaluations on an additive domain. The row branch commits to the first `k`
//! evaluations, which are the original payload; the column branch authenticates
//! sampled cells. [`check_membership`] checks that every row belongs to the code.
//! The aggregation guest proves this check together with both commitment branches.
//!
//! Row and cell widths are powers of two. Trees pad the row count with zero rows.
//! A root binds this padded matrix, not the original row count: a trailing zero
//! row is indistinguishable from padding within the same padded height.

mod commit;
mod encode;
mod membership;

pub use commit::{DaCommitment, DaWitness, commit, commit_codewords, padding_digests};
pub use encode::encode_rows;
pub use membership::{
    check_membership, dual_codeword, membership_challenges, membership_vector, row_residuals, vector_digest,
};

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
const PAYLOAD_CELLS: usize = BLOB_SYMBOLS / CELL_SYMBOLS;
const LOG_M: usize = DA_LOG_K + 1;

fn row_count(symbols: usize, width: usize) -> usize {
    assert!(symbols.is_multiple_of(width), "partial blob row");
    let rows = symbols / width;
    assert!((1..=DA_MAX_ROWS).contains(&rows), "expected 1..=DA_MAX_ROWS blobs");
    rows
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn row_counts_reject_empty_partial_and_oversized_inputs() {
        for width in [BLOB_SYMBOLS, CODEWORD_SYMBOLS] {
            assert_eq!(row_count(width, width), 1);
            assert_eq!(row_count(DA_MAX_ROWS * width, width), DA_MAX_ROWS);
            for symbols in [0, width - 1, width + 1, (DA_MAX_ROWS + 1) * width, usize::MAX] {
                assert!(std::panic::catch_unwind(|| row_count(symbols, width)).is_err());
            }
        }
    }
}
