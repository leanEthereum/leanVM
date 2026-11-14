//! The bit-level kernels of the layer prover, over one block position at a time: the 32 packs of
//! one bit position of one block.

use primitives::field::{Acc8, F64, F64x8, F128, F128x8, clmul8_low};

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
    let mut out = [0u64; PACKS];
    for (v, out) in out.as_chunks_mut::<8>().0.iter_mut().enumerate() {
        let lanes = |e: &[u32; PACKS]| -> [u64; 8] { std::array::from_fn(|i| e[8 * v + i] as u64) };
        let (a, b, c) = (lanes(a), lanes(b), lanes(c));
        let linear = clmul8_low([RMFE.ones as u64; 8], std::array::from_fn(|i| a[i] ^ c[i]));
        let quadratic = clmul8_low(b, c);
        *out = std::array::from_fn(|i| linear[i] ^ quadratic[i]);
    }
    out
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
pub fn extend(packs: &[u32; PACKS], out: &mut [u64; SLOTS]) {
    // Both groups at once, group `half` in bits `32 * half ..` of each value.
    let mut values = [0u64; TERNARY];
    for q in 0..GROUP {
        values[ternary(q)] = packs[q] as u64 | (packs[GROUP + q] as u64) << 32;
    }
    for &[t, zero, one] in &MIXED_POINTS {
        values[t] = values[zero] ^ values[one];
    }
    for half in 0..2 {
        for q in 0..GROUP {
            out[GROUP * half + q] = packs[GROUP * half + q] as u64;
        }
        for (i, &[t, ..]) in MIXED_POINTS.iter().enumerate() {
            out[2 * GROUP + MIXED * half + i] = values[t] >> (32 * half) & 0xffff_ffff;
        }
    }
}

/// One row of five positions, which `chi` mixes cyclically: per slot, the sum over the row of
/// its position's weight times its product. A weight is a polynomial in `s` ([`AtS::poly`]), its
/// two words held as an element's limbs, so its product by a product is a mixed one, unreduced: the
/// two partial products of its words. A pack's product is the unprojected `chi`; a mixed point's
/// keeps only `u[j + 1] * u[j + 2]`, the rest being linear, so of degree one in a variable at
/// infinity.
///
/// [`AtS::poly`]: crate::poly::AtS::poly
pub fn skip_row(acc: &mut SkipAcc, e: &[[u64; SLOTS]; 5], weights: [F128x8; 5]) {
    let xor = |a: [u64; 8], b: [u64; 8]| -> [u64; 8] { std::array::from_fn(|i| a[i] ^ b[i]) };
    for (v, acc) in acc.0.iter_mut().enumerate() {
        let e: [[u64; 8]; 5] = std::array::from_fn(|x| e[x][8 * v..][..8].try_into().unwrap());
        let mut sum = Acc8::ZERO;
        for (x, weight) in weights.iter().enumerate() {
            let (b, c) = (e[(x + 1) % 5], e[(x + 2) % 5]);
            let mut product = clmul8_low(b, c);
            if 8 * v < 2 * GROUP {
                product = xor(product, clmul8_low([RMFE.ones as u64; 8], xor(e[x], c)));
            }
            sum += weight.mul_base_unreduced(F64x8::from_array(&product.map(F64)));
        }
        *acc += sum;
    }
}

/// Per slot, the sums [`skip_row`] takes, eight slots to a run.
pub struct SkipAcc([Acc8; SLOTS / 8]);

impl SkipAcc {
    pub fn new() -> Box<Self> {
        Box::new(Self([Acc8::ZERO; SLOTS / 8]))
    }

    pub fn clear(&mut self) {
        self.0 = [Acc8::ZERO; SLOTS / 8];
    }

    /// The two partial products of slot `p`: the sums of the products times each word of their weights.
    pub fn get(&self, p: usize) -> [u128; 2] {
        self.0[p / 8].to_array()[p % 8].to_limbs()
    }
}
