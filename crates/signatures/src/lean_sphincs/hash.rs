//! leanSPHINCS's address types, on the shared tweakable hash (`crate::tweak`),
//! whose address names one hash call in the whole structure.

pub use crate::tweak::*;

use crate::lean_sphincs::*;

// Hash types of leanSPHINCS's own.
pub const TWEAK_ENC: u8 = 4;
pub const TWEAK_FORS_PRF: u8 = 14;
pub const TWEAK_FORS_LEAF: u8 = 15;
pub const TWEAK_FORS_NODE: u8 = 17;

/// The `hi` field of a FORS call at `position` of tree `c`: `c + 64 position`,
/// a position being a leaf, a pair of leaves, or `level + 16 j` for node `j`.
pub const fn fors_hi(c: usize, position: usize) -> u32 {
    (c + 64 * position) as u32
}

const _: () = assert!(FORS_TREES <= 64 && FORS_HEIGHT <= 16);
const _: () = assert!(fors_hi(FORS_TREES - 1, 16 << FORS_HEIGHT) < 1 << 24);
