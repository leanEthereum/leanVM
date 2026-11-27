//! The bit-level tools the layer's passes share, over a block of the witness ([`crate::witness`]): a run of eight
//! positions along `z` is the unit, lane `i` of a [`Run`] holding position `z + i`.

use primitives::field::F128;
use primitives::field::lanes::{ByteMap, Linear16, map_bytes, map_fields, transpose_bytes, transpose_words};
use verifier::keccak::RMFE_EMBED;

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
    primitives::field::lanes::xor8(a, b)
}

/// The embeddings of the 32 packs of the eight positions from `j`: pack `q` of position `j + i` is lane `i` of
/// `out[q]`. Out of line: one copy for every pass.
#[inline(never)]
pub fn embed_run(block: &[u64], j: usize, out: &mut [Run; PACKS]) {
    let positions = block[j * BLOCK_WORDS..][..8 * BLOCK_WORDS].as_chunks::<BLOCK_WORDS>().0;
    let words = transpose_words(positions.try_into().expect("eight positions"));
    for (out, word) in out.as_chunks_mut::<4>().0.iter_mut().zip(&words) {
        *out = map_fields(&EMBEDDING, *word);
    }
}

/// `primitives::multilinear::eq_table` out of line: one copy for every table.
#[inline(never)]
pub fn eq_table(r: &[F128]) -> Vec<F128> {
    primitives::multilinear::eq_table(r)
}

/// A GF(2)-linear map from a byte to a field element, as one byte map per byte of the element.
pub type FieldMap = [ByteMap; 16];

/// The map sending bit `c` of a byte to `images[c]`: a byte to the sum of the images of its set bits. Out of line:
/// one copy for every pass.
#[inline(never)]
pub fn field_map(images: &[F128; 8]) -> FieldMap {
    let bytes = images.map(|w| u128::from(w).to_le_bytes());
    std::array::from_fn(|o| ByteMap::new(std::array::from_fn(|c| bytes[c][o])))
}

/// `sum over i of maps[i](byte n of run i)` for each `n` of 64, run `i` being the eight words of `words` from
/// `stride * i`: a linear map of many bytes, 64 at a time. Out of line: one copy for every pass.
#[inline(never)]
pub fn map_sums(maps: &[FieldMap], words: &[u64], stride: usize) -> [u128; 64] {
    let mut sums = [[0u64; 8]; 16];
    // Four bytes of the sums at a time, each its own accumulator, which keeps them in registers.
    for (o, sums) in sums.as_chunks_mut::<4>().0.iter_mut().enumerate() {
        let [mut s0, mut s1, mut s2, mut s3] = [[0u64; 8]; 4];
        for (i, maps) in maps.iter().enumerate() {
            let x: Run = words[stride * i..][..8].try_into().expect("eight words");
            let [m0, m1, m2, m3] = &maps.as_chunks::<4>().0[o];
            s0 = xor(s0, map_bytes(m0, x));
            s1 = xor(s1, map_bytes(m1, x));
            s2 = xor(s2, map_bytes(m2, x));
            s3 = xor(s3, map_bytes(m3, x));
        }
        *sums = [s0, s1, s2, s3];
    }
    transpose_bytes(&sums)
}
