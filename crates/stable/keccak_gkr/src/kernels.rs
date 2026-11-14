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

/// Points of `{0, 1, infinity}^SKIP`, infinity as digit 2, variable `k` the `k`-th digit; and
/// those with a digit at infinity.
pub(crate) const TERNARY: usize = 3usize.pow(SKIP as u32);
pub(crate) const MIXED: usize = TERNARY - GROUP;
/// The products of a block position the skip sums: each group's packs, then each group's mixed
/// points, padded to whole vectors of eight.
pub const SLOTS: usize = (2 * TERNARY).next_multiple_of(8);

/// The point of `{0, 1, infinity}^SKIP` of a pack of a group.
pub(crate) const fn ternary(q: usize) -> usize {
    (q & 1) + 3 * (q >> 1 & 1) + 9 * (q >> 2 & 1) + 27 * (q >> 3 & 1)
}

/// The mixed points in increasing order, each with the points at `0` and `1` along its lowest
/// digit at infinity, whose values sum to its own.
pub(crate) const MIXED_POINTS: [[usize; 3]; MIXED] = {
    let mut out = [[0; 3]; MIXED];
    let (mut i, mut t) = (0, 0);
    while t < TERNARY {
        let (mut k, mut step) = (0, 1);
        while k < SKIP && t / step % 3 != 2 {
            k += 1;
            step *= 3;
        }
        if k < SKIP {
            out[i] = [t, t - 2 * step, t - step];
            i += 1;
        }
        t += 1;
    }
    out
};

/// A block position's packs at every point of `{0, 1, infinity}^SKIP` of each group, at their
/// slots: along a variable, the value at infinity is the sum of the two others.
pub fn extend(packs: &[u32; PACKS]) -> [u64; SLOTS] {
    let mut out = [0u64; SLOTS];
    for half in 0..2 {
        let mut values = [0u32; TERNARY];
        for q in 0..GROUP {
            values[ternary(q)] = packs[GROUP * half + q];
            out[GROUP * half + q] = packs[GROUP * half + q] as u64;
        }
        for (i, &[t, zero, one]) in MIXED_POINTS.iter().enumerate() {
            values[t] = values[zero] ^ values[one];
            out[2 * GROUP + MIXED * half + i] = values[t] as u64;
        }
    }
    out
}

/// One row of five positions, which `chi` mixes cyclically: per slot, the sum over the row of
/// its position's weight times its product, as the two partial products of the weight's words.
/// A pack's product is the unprojected `chi`; a mixed point's keeps only `u[j + 1] * u[j + 2]`,
/// the rest being linear, so of degree one in a variable at infinity.
pub fn skip_row(acc: &mut [[u128; 2]; SLOTS], e: &[[u64; SLOTS]; 5], weights: [[u64; 2]; 5]) {
    let ones = RMFE.ones as u64;
    for (p, acc) in acc.iter_mut().enumerate().take(2 * TERNARY) {
        for (x, w) in weights.iter().enumerate() {
            let (b, c) = (e[(x + 1) % 5][p], e[(x + 2) % 5][p]);
            let mut product = mul_wide(b, c) as u64;
            if p < 2 * GROUP {
                product ^= mul_wide(ones, e[x][p] ^ c) as u64;
            }
            acc[0] ^= mul_wide(product, w[0]);
            acc[1] ^= mul_wide(product, w[1]);
        }
    }
}
