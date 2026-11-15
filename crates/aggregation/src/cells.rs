//! Field-element encodings shared by the host and the guest.

use verifier::E;

pub(super) const ZERO: E = E::new(0, 0);
pub(super) const ONE: E = E::new(1, 0);

/// A count as the guest carries it: in the exponent, `g^n`.
pub(super) fn count(n: usize) -> E {
    E::new(primitives::field::g_pow(n).0, 0)
}

/// Bytes, each in the exponent: how the guest bounds a value it rebuilds
/// (`sp_from_bytes`).
pub(super) fn exponent_bytes(bytes: &[u8]) -> Vec<E> {
    bytes.iter().map(|&b| count(b.into())).collect()
}

/// A word as its 128 bits, the low limb low.
pub(super) fn bits(x: E) -> u128 {
    u128::from(x.c1) << 64 | u128::from(x.c0)
}

/// 128 bits as a word, the low limb low.
pub(super) fn word(x: u128) -> E {
    E::new(x as u64, (x >> 64) as u64)
}

/// A 16-byte native value as one cell, little-endian.
pub(super) fn pack_16_bytes(bytes: &[u8]) -> E {
    word(u128::from_le_bytes(bytes[..16].try_into().unwrap()))
}

/// A run of cells as the byte string the hash takes: each cell little-endian,
/// which is the order the VM's hash instruction reads a memory cell in.
pub(super) fn cell_bytes(cells: impl IntoIterator<Item = E>) -> Vec<u8> {
    cells.into_iter().flat_map(|cell| bits(cell).to_le_bytes()).collect()
}

/// A digest as the two words transcripts carry it in: its four little-endian words, two to a word.
pub(super) fn hash_to_scalars(hash: &[u8; 32]) -> [E; 2] {
    let w: [u64; 4] = std::array::from_fn(|i| u64::from_le_bytes(hash[8 * i..8 * i + 8].try_into().unwrap()));
    [E::new(w[0], w[1]), E::new(w[2], w[3])]
}
