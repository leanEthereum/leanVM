//! The bit-level tools the layer's passes share, over a block of the witness ([`crate::witness`]): a run of eight
//! positions along `z` is the unit, lane `i` of a [`Run`] holding position `z + i`.

use primitives::field::F128;
use primitives::field::lanes::{ByteMap, Linear16, map_bytes, map_fields, transpose_bytes, transpose_words};
use verifier::RMFE_EMBED;

use crate::witness::BLOCK_WORDS;

/// Eight values, one per position of a run of eight along `z`.
pub type Run = [u64; 8];

/// Packs in a block position, its 512 instances sixteen to a pack, and the low variables of a pack index, which
/// index them.
pub const PACKS: usize = 32;
pub const PACKS_LOG: usize = 5;

/// The embedding of a pack's sixteen bits (Annex C's `lem:rmfe`), as the lanes apply it.
static EMBEDDING: Linear16 = Linear16::new(RMFE_EMBED);
/// The embedding of all ones: its product with an embedding projects to what that embeds.
pub const ONES: u64 = {
    let (mut ones, mut i) = (0, 0);
    while i < RMFE_EMBED.len() {
        ones ^= RMFE_EMBED[i] as u64;
        i += 1;
    }
    ones
};

pub fn xor(a: Run, b: Run) -> Run {
    std::array::from_fn(|i| a[i] ^ b[i])
}

/// The embeddings of the 32 packs of the eight positions from `j`: pack `q` of position `j + i` is lane `i` of
/// `out[q]`.
pub fn embed_run(block: &[u64], j: usize) -> [Run; PACKS] {
    let positions = block[j * BLOCK_WORDS..][..8 * BLOCK_WORDS].as_chunks::<BLOCK_WORDS>().0;
    let words = transpose_words(positions.try_into().expect("eight positions"));
    let mut out = [[0; 8]; PACKS];
    for (out, word) in out.as_chunks_mut::<4>().0.iter_mut().zip(&words) {
        *out = map_fields(&EMBEDDING, *word);
    }
    out
}

/// A GF(2)-linear map from a byte to a field element, as one byte map per byte of the element.
pub type FieldMap = [ByteMap; 16];

/// The map sending bit `c` of a byte to `images[c]`: a byte to the sum of the images of its set bits.
pub fn field_map(images: &[F128; 8]) -> FieldMap {
    let bytes = images.map(|w| u128::from(w).to_le_bytes());
    std::array::from_fn(|o| ByteMap::new(std::array::from_fn(|c| bytes[c][o])))
}

/// `sum over i of maps[i](byte n of bytes(i))` for each `n` of 64: a linear map of many bytes, 64 at a time.
pub fn map_sums(maps: &[FieldMap], bytes: impl Fn(usize) -> Run) -> [u128; 64] {
    // Four bytes of the sums at a time, which keeps the accumulators in registers.
    const HELD: usize = 4;
    let mut sums = [[0u64; 8]; 16];
    for (o, sums) in sums.as_chunks_mut::<HELD>().0.iter_mut().enumerate() {
        for (i, maps) in maps.iter().enumerate() {
            let x = bytes(i);
            for (sum, map) in sums.iter_mut().zip(&maps[HELD * o..]) {
                *sum = xor(*sum, map_bytes(map, x));
            }
        }
    }
    transpose_bytes(&sums)
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
