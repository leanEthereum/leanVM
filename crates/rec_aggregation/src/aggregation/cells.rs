//! Field-element encodings shared by the host and the guest.

use primitives::field::{F192, g_pow};

/// A count as the guest carries it: in the exponent, `g^n`.
pub(super) fn count(n: usize) -> F192 {
    F192::new(g_pow(n).0, 0, 0)
}

/// Bytes, each in the exponent: how the guest bounds a value it rebuilds
/// (`sp_from_bytes`).
pub(super) fn exponent_bytes(bytes: &[u8]) -> Vec<F192> {
    bytes.iter().map(|&b| count(b.into())).collect()
}

/// A field element as the decimal `u128` literal the zkDSL parser accepts.
pub(super) fn dsl_u128(value: F192) -> u128 {
    value
        .as_u128()
        .expect("u128 DSL literal cannot encode the top F192 limb")
}

pub(super) fn f192_literal(f: F192) -> String {
    format!("f192({},{},{})", f.c0, f.c1, f.c2)
}

/// A 16-byte native value as one canonical 128-bit cell.
pub(super) fn pack_16_bytes(bytes: &[u8]) -> F192 {
    F192::from(u128::from_le_bytes(
        bytes[..16].try_into().expect("a cell packs 16 bytes"),
    ))
}

/// A run of canonical 128-bit cells as the byte string the hash takes: each cell
/// is its two low limbs, little-endian, which is the order the VM's hash
/// instruction reads a memory cell in.
pub(super) fn cell_bytes(cells: impl IntoIterator<Item = F192>) -> Vec<u8> {
    let mut bytes = Vec::new();
    for cell in cells {
        bytes.extend_from_slice(&cell.c0.to_le_bytes());
        bytes.extend_from_slice(&cell.c1.to_le_bytes());
    }
    bytes
}
