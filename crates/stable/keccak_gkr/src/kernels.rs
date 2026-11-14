//! The bit-level kernels of the layer prover, over one block position at a time: the 32 packs of
//! one bit position of one block.

use primitives::field::gf2_64::mul_wide;

use crate::rmfe::RMFE;
use crate::witness::BLOCK_WORDS;

/// Packs in a block position.
pub(crate) const PACKS: usize = 32;
/// Packs the first rounds fold together: half a block.
pub const GROUP: usize = 16;
/// Variables indexing the packs of a group.
pub(crate) const SKIP: usize = 4;

/// The 32 packs of a block position, embedded.
pub fn embed(words: &[u64; BLOCK_WORDS]) -> [u32; PACKS] {
    std::array::from_fn(|q| RMFE.embed((words[q / 4] >> (16 * (q % 4))) as u16))
}

/// The unprojected `chi` of 32 packs: `ones * (a + c) + b * c`.
pub fn products(a: &[u32; PACKS], b: &[u32; PACKS], c: &[u32; PACKS]) -> [u64; PACKS] {
    let ones = RMFE.ones as u64;
    std::array::from_fn(|q| (mul_wide(ones, (a[q] ^ c[q]) as u64) ^ mul_wide(b[q] as u64, c[q] as u64)) as u64)
}

/// For both groups of a block position, `sum over the group's packs of weights[.][q] * e[q]`,
/// as two partial products.
pub fn fold_groups(e: &[u32; PACKS], weights: &[[u64; GROUP]; 2]) -> [[u128; 2]; 2] {
    std::array::from_fn(|half| {
        std::array::from_fn(|k| (0..GROUP).fold(0, |acc, q| acc ^ mul_wide(e[GROUP * half + q] as u64, weights[k][q])))
    })
}
