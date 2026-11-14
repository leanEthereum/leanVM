//! The bit-level kernels of the layer prover, over one block position at a time: the 32 packs of
//! one bit position of one block.

use primitives::field::{Acc8, F64, F64x8, F128, F128x8, clmul8_low};

use crate::keccak::row_positions;

use crate::rmfe::RMFE;
use crate::witness::{BLOCK_WORDS, words};

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

/// Eight values, one per position of a run of eight along `z`.
type Run = [u64; 8];

fn xor(a: Run, b: Run) -> Run {
    std::array::from_fn(|i| a[i] ^ b[i])
}

/// The packs of a run of positions at every point of `{0, 1, infinity}^SKIP` of each group, at
/// their slots: along a variable, the value at infinity is the sum of the two others.
fn extend(packs: &[Run; PACKS], out: &mut [Run; SLOTS]) {
    // Both groups at once, group `half` in bits `32 * half ..` of each value.
    let mut values = [[0u64; 8]; TERNARY];
    for q in 0..GROUP {
        values[ternary(q)] = std::array::from_fn(|i| packs[q][i] | packs[GROUP + q][i] << 32);
    }
    for &[t, zero, one] in &MIXED_POINTS {
        values[t] = xor(values[zero], values[one]);
    }
    out[..2 * GROUP].copy_from_slice(packs);
    for half in 0..2 {
        for (i, &[t, ..]) in MIXED_POINTS.iter().enumerate() {
            out[2 * GROUP + MIXED * half + i] = values[t].map(|v| v >> (32 * half) & 0xffff_ffff);
        }
    }
}

/// The skip's sums over a block: per slot, the sum over positions of the position's weight times
/// its product. A weight is a polynomial in `s` ([`AtS::poly`]), its two words held as an element's
/// limbs, so its product by a product is a mixed one, unreduced: the two partial products of its
/// words. A pack's product is the unprojected `chi`; a mixed point's keeps only
/// `u[j + 1] * u[j + 2]`, the rest being linear, so of degree one in a variable at infinity.
///
/// Lane `i` of a slot's sums is position `z + i` of every run along `z`: a row of five positions,
/// which `chi` mixes, is five runs, and their weights are eight consecutive ones.
///
/// [`AtS::poly`]: crate::poly::AtS::poly
pub(crate) struct SkipBlock {
    acc: Vec<Acc8>,
    extended: Vec<[Run; SLOTS]>,
}

impl SkipBlock {
    pub fn new() -> Self {
        Self {
            acc: vec![Acc8::ZERO; 2 * TERNARY],
            extended: vec![[[0; 8]; SLOTS]; 5],
        }
    }

    pub fn run(&mut self, block: &[u64], weights: &[F128]) {
        self.acc.fill(Acc8::ZERO);
        let ones = [RMFE.ones as u64; 8];
        for r in 0..5 {
            for z in (0..64).step_by(8) {
                let js = row_positions(r, z);
                for (extended, &j) in self.extended.iter_mut().zip(&js) {
                    let packs: [[u32; PACKS]; 8] = std::array::from_fn(|i| embed(words(block, j + i)));
                    extend(
                        &std::array::from_fn(|q| std::array::from_fn(|i| packs[i][q] as u64)),
                        extended,
                    );
                }
                let w: [F128x8; 5] = js.map(|j| F128x8::load(&weights[j..][..8]));
                let e = &self.extended;
                for (p, acc) in self.acc.iter_mut().enumerate() {
                    let mut sum = Acc8::ZERO;
                    for (x, w) in w.iter().enumerate() {
                        let (b, c) = (e[(x + 1) % 5][p], e[(x + 2) % 5][p]);
                        let mut product = clmul8_low(b, c);
                        if p < 2 * GROUP {
                            product = xor(product, clmul8_low(ones, xor(e[x][p], c)));
                        }
                        sum += w.mul_base_unreduced(F64x8::from_array(&product.map(F64)));
                    }
                    *acc += sum;
                }
            }
        }
    }

    /// The two partial products of slot `p`: the sums of the products times each word of their
    /// weights.
    pub fn get(&self, p: usize) -> [u128; 2] {
        let lanes = self.acc[p].to_array().map(|l| l.to_limbs());
        lanes.into_iter().fold([0; 2], |a, b| [a[0] ^ b[0], a[1] ^ b[1]])
    }
}
