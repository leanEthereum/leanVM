//! BLAKE2s compression on words, as a hash row computes it, and the hashes the circuit builds from it.

use super::Limbs;
use crate::rv::{Hash, InstructionClass};
use fiat_shamir::Hashing;

/// The parameter IV as four words.
pub const PARAM_IV: Limbs = words(primitives::hash::PARAM_IV);

/// One BLAKE2s compression, its inputs in the compression circuit's port order: `t`, `f`, `h0..h3`, `m0..m7`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Compression([u64; 14]);

impl Compression {
    /// The inputs of a padding row: all zero.
    pub(crate) const PADDING: Self = Self([0; 14]);

    /// The compression of the message `m` into `h` at byte counter `t`, final if `last`.
    pub const fn new(h: Limbs, m: [u64; 8], t: u64, last: bool) -> Self {
        let f = if last { Hash::FINAL } else { 0 };
        Self([
            t, f, h[0], h[1], h[2], h[3], m[0], m[1], m[2], m[3], m[4], m[5], m[6], m[7],
        ])
    }

    /// A one-block message from the parameter IV: its only block, so final.
    pub const fn single(m: [u64; 8]) -> Self {
        Self::new(PARAM_IV, m, 64, true)
    }

    /// The inputs, in the compression circuit's port order.
    pub const fn inputs(&self) -> &[u64; 14] {
        &self.0
    }

    /// The output chaining value, as the precompile computes it.
    pub fn output(&self) -> Limbs {
        let i = &self.0;
        let block: [u64; 16] = std::array::from_fn(|w| match w {
            0..4 => i[2 + w],
            4..8 => 0,
            _ => i[6 + w - 8],
        });
        Hash {
            flags: i[1],
            t: i[0],
            block,
        }
        .eval()
    }

    /// The output chaining value by `H`'s compression: the prover's kernel or the native verifier's portable code.
    fn output_by<H: Hashing>(&self) -> Limbs {
        let i = &self.0;
        // Each word of `h` and `m` as its two 32-bit halves, low first.
        let mut h: [u32; 8] = std::array::from_fn(|k| (i[2 + k / 2] >> (32 * (k % 2))) as u32);
        let m: [u32; 16] = std::array::from_fn(|k| (i[6 + k / 2] >> (32 * (k % 2))) as u32);
        H::compress(&mut h, &m, i[0], i[1] == Hash::FINAL);
        words(h)
    }
}

/// The chaining value after `n` zero blocks from the parameter IV, as four words.
pub fn zero_prefix(n: usize) -> Limbs {
    words(primitives::hash::zero_prefix_state(n))
}

/// The BLAKE2s hash of the little-endian bytes of `words`, eight words a block, by `H`'s compression.
///
/// The last block is zero padded and its counter is the message's length in bytes.
/// So the length is hashed: appending zero words changes the digest.
pub fn chain<H: Hashing>(words: &[u64]) -> Limbs {
    let n_blocks = words.len().div_ceil(8).max(1);
    let bytes = 8 * words.len() as u64;
    (0..n_blocks).fold(PARAM_IV, |h, j| {
        // The final block retains the message's words and zero-pads its unused slots.
        let m = std::array::from_fn(|k| words.get(8 * j + k).copied().unwrap_or(0));
        Compression::new(h, m, (64 * (j as u64 + 1)).min(bytes), j + 1 == n_blocks).output_by::<H>()
    })
}

/// A transcript digest as four words.
pub(crate) fn digest_limbs(d: &[u8; 32]) -> Limbs {
    fiat_shamir::digest_words(d).map(|w| w.0)
}

/// Four words from eight little-endian 32-bit halves.
const fn words(h: [u32; 8]) -> Limbs {
    let mut out = [0; 4];
    let mut i = 0;
    while i < 4 {
        out[i] = h[2 * i] as u64 | (h[2 * i + 1] as u64) << 32;
        i += 1;
    }
    out
}
