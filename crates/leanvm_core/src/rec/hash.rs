//! BLAKE2s compression on words, as a hash row computes it, and the hashes a verifier program builds from it.

use crate::rv::{Hash, InstructionClass};

/// A digest: four words.
pub type Limbs = [u64; 4];

/// The parameter IV as four words.
pub const PARAM_IV: Limbs = words(primitives::hash::PARAM_IV);

/// The compression of the message `m` into `h` at byte counter `t`, final if `last`, as the instruction computes it.
pub fn compress(h: Limbs, m: [u64; 8], t: u64, last: bool) -> Limbs {
    let flags = if last { Hash::FINAL } else { 0 };
    Hash { flags, x: t, h, m }.eval()
}

/// The hash of two digests: a one-block message from the parameter IV.
pub fn node(left: Limbs, right: Limbs) -> Limbs {
    let m = std::array::from_fn(|k| if k < 4 { left[k] } else { right[k - 4] });
    compress(PARAM_IV, m, Hash::BLOCK_BYTES, true)
}

/// The chaining value after `n` zero blocks from the parameter IV, as four words.
pub fn zero_prefix(n: usize) -> Limbs {
    words(primitives::hash::zero_prefix_state(n))
}

/// The BLAKE2s hash of the little-endian bytes of `words`.
///
/// The length is hashed: appending zero words changes the digest.
pub fn chain(words: &[u64]) -> Limbs {
    let bytes: Vec<u8> = words.iter().flat_map(|w| w.to_le_bytes()).collect();
    digest_limbs(&primitives::hash::hash(&bytes))
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
