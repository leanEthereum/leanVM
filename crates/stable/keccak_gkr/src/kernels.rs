//! The bit-level kernels of the layer prover, over one block position at a time: the 32 packs of
//! one bit position of one block.

use primitives::field::F128;
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

/// The sum of every subset of eight weights, indexed by the byte whose bits pick it.
pub fn byte_sums(weights: &[F128; 8]) -> [F128; 256] {
    let mut t = [F128::ZERO; 256];
    for (bit, &w) in weights.iter().enumerate() {
        for byte in 1usize << bit..2 << bit {
            t[byte] = t[byte - (1 << bit)] + w;
        }
    }
    t
}
