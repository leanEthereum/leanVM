//! Field-element encodings shared by the host and the guest.

use primitives::field::{F128, g_pow};

/// A count as the guest carries it: in the exponent, `g^n`.
pub(super) fn count(n: usize) -> F128 {
    F128::from(g_pow(n))
}

/// Bytes, each in the exponent: how the guest bounds a value it rebuilds
/// (`sp_from_bytes`).
pub(super) fn exponent_bytes(bytes: &[u8]) -> Vec<F128> {
    bytes.iter().map(|&b| count(b.into())).collect()
}

/// A 16-byte native value as one cell, little-endian.
pub(super) fn pack_16_bytes(bytes: &[u8]) -> F128 {
    u128::from_le_bytes(bytes[..16].try_into().unwrap()).into()
}

/// A run of cells as the byte string the hash takes: each cell little-endian,
/// which is the order the VM's hash instruction reads a memory cell in.
pub(super) fn cell_bytes(cells: impl IntoIterator<Item = F128>) -> Vec<u8> {
    cells
        .into_iter()
        .flat_map(|cell| u128::from(cell).to_le_bytes())
        .collect()
}
