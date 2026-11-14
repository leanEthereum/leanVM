//! The bit-level kernels of the layer prover, over one block position at a time: the 32 packs of
//! one bit position of one block.

use primitives::field::gf2_64::mul_wide;

use crate::keccak::row_positions;
use crate::rmfe::RMFE;
use crate::witness::BLOCK_WORDS;

/// Packs in a block position.
pub(crate) const PACKS: usize = 32;
/// Packs the bit-level rounds fold together: half a block.
pub const GROUP: usize = 16;
/// Variables indexing the packs of a group.
pub(crate) const SKIP: usize = 4;
/// Points of `{0, 1, infinity}^SKIP`, and those of them with a coordinate at infinity.
pub(crate) const TERNARY: usize = 3usize.pow(SKIP as u32);
pub(crate) const MIXED: usize = TERNARY - GROUP;
/// The mixed points of a block position's two groups, rounded up to whole vectors.
pub const SLOTS: usize = (2 * MIXED).next_multiple_of(8);

/// Sums of `value * weight word`, a 128-bit product each, laid out as the vector kernel leaves
/// them: entry `i` of a run of eight sits at `lane(i)`.
#[derive(Clone, Copy)]
#[repr(C, align(64))]
pub struct Lanes(pub(crate) [u128; 4]);

/// The [`Lanes`] of entry `i`, and its lane there.
#[inline(always)]
const fn lane(i: usize) -> (usize, usize) {
    (2 * (i / 8) + i % 2, (i % 8) / 2)
}

/// Per mixed point of each group, the sum over positions of `weight * product`, as two
/// partial products.
pub struct SkipAcc(pub(crate) [[Lanes; SLOTS / 4]; 2]);

impl SkipAcc {
    pub fn new() -> Box<Self> {
        Box::new(Self([[Lanes([0; 4]); SLOTS / 4]; 2]))
    }

    pub fn clear(&mut self) {
        self.0 = [[Lanes([0; 4]); SLOTS / 4]; 2];
    }

    /// The two partial products of slot `i`.
    pub fn get(&self, i: usize) -> [u128; 2] {
        let (v, l) = lane(i);
        std::array::from_fn(|k| self.0[k][v].0[l])
    }
}

/// The points of `{0, 1, infinity}^2` of the high two variables, with infinity as 2, in the
/// order [`extend_group`] builds their values: the four binary points, then the mixed ones.
const HIGH: [(usize, usize); 9] = [(0, 0), (1, 0), (0, 1), (1, 1), (2, 0), (2, 1), (0, 2), (1, 2), (2, 2)];
/// The mixed points of the low two variables, in the order their values fill a vector.
const LOW_MIXED: [(usize, usize); 4] = [(2, 0), (2, 1), (0, 2), (1, 2)];

/// The slot of output `i` of group `half` of a block position: each group's first 64 outputs
/// are whole vectors, and their last outputs share a pair of slots.
#[inline(always)]
pub const fn slot(half: usize, i: usize) -> usize {
    if i < 64 { 64 * half + i } else { 128 + half }
}

/// Extend one group's values on the binary cube to the mixed points of `{0, 1, infinity}^SKIP`:
/// along each variable, the value at infinity is the sum of the two others.
///
/// The values are four vectors of four, the high two variables across the vectors and the low
/// two within them. Across, there are nine vectors, five of them new. Within each of the nine,
/// the low variables have five mixed points: four filling a vector, and the sum of all four
/// lanes. The outputs are the new vectors' binary points, every vector's four low mixed points,
/// then every vector's lane sum; [`mixed_points`] names each by its ternary digits.
pub(crate) fn extend_group(v: &[u32; GROUP]) -> [u32; MIXED] {
    let q = |k: usize| -> [u32; 4] { v[4 * k..][..4].try_into().unwrap() };
    let x = |a: [u32; 4], b: [u32; 4]| -> [u32; 4] { std::array::from_fn(|l| a[l] ^ b[l]) };
    let (w4, w5) = (x(q(0), q(1)), x(q(2), q(3)));
    let w = [q(0), q(1), q(2), q(3), w4, w5, x(q(0), q(2)), x(q(1), q(3)), x(w4, w5)];
    let mut out = [0u32; MIXED];
    for (k, w) in w[4..].iter().enumerate() {
        out[4 * k..][..4].copy_from_slice(w);
    }
    for (k, w) in w.iter().enumerate() {
        out[20 + 4 * k..][..4].copy_from_slice(&[w[0] ^ w[1], w[2] ^ w[3], w[0] ^ w[2], w[1] ^ w[3]]);
        out[56 + k] = w[0] ^ w[1] ^ w[2] ^ w[3];
    }
    out
}

/// The ternary index of each output of [`extend_group`]: variable `k`'s point is its `k`-th
/// digit, with infinity as 2.
pub(crate) fn mixed_points() -> [usize; MIXED] {
    let index = |(c0, c1): (usize, usize), (c2, c3): (usize, usize)| c0 + 3 * c1 + 9 * c2 + 27 * c3;
    std::array::from_fn(|i| match i {
        0..20 => index(((i % 4) & 1, (i % 4) >> 1), HIGH[4 + i / 4]),
        20..56 => index(LOW_MIXED[(i - 20) % 4], HIGH[(i - 20) / 4]),
        _ => index((2, 2), HIGH[i - 56]),
    })
}

/// Both groups of a block position, at their [`slot`]s.
pub fn extend(packs: &[u32; PACKS], out: &mut [u32; SLOTS]) {
    for half in 0..2 {
        let e = extend_group(packs[GROUP * half..][..GROUP].try_into().unwrap());
        for (i, &e) in e.iter().enumerate() {
            out[slot(half, i)] = e;
        }
    }
}

/// The 32 packs of a block position, embedded.
pub fn embed(words: &[u64; BLOCK_WORDS]) -> [u32; PACKS] {
    std::array::from_fn(|q| RMFE.embed((words[q / 4] >> (16 * (q % 4))) as u16))
}

/// The unprojected `chi` of 32 packs: `ones * (a + c) + b * c`.
pub fn products(a: &[u32; PACKS], b: &[u32; PACKS], c: &[u32; PACKS]) -> [u64; PACKS] {
    let ones = RMFE.ones as u64;
    std::array::from_fn(|q| (mul_wide(ones, (a[q] ^ c[q]) as u64) ^ mul_wide(b[q] as u64, c[q] as u64)) as u64)
}

/// One row of five positions, which `chi` mixes cyclically: for every pattern,
/// `acc[p] += sum over x of weights[x] * e[x + 1][p] * e[x + 2][p]`.
pub fn skip_row(acc: &mut SkipAcc, e: &[[u32; SLOTS]; 5], weights: [&[u64; 2]; 5]) {
    for x in 0..5 {
        let (b, c) = (&e[(x + 1) % 5], &e[(x + 2) % 5]);
        for p in 0..SLOTS {
            let product = mul_wide(b[p] as u64, c[p] as u64) as u64;
            let (v, l) = lane(p);
            for k in 0..2 {
                acc.0[k][v].0[l] ^= mul_wide(product, weights[x][k]);
            }
        }
    }
}

/// For both groups of a block position, `sum over the group's packs of weights[.][q] * e[q]`,
/// as two partial products.
pub fn fold_groups(e: &[u32; PACKS], weights: &[[u64; GROUP]; 2]) -> [[u128; 2]; 2] {
    std::array::from_fn(|half| {
        std::array::from_fn(|k| (0..GROUP).fold(0, |acc, q| acc ^ mul_wide(e[GROUP * half + q] as u64, weights[k][q])))
    })
}

/// [`skip_row`] over every row and slice of a block, a position at a time.
pub(crate) struct SkipBlock {
    acc: Box<SkipAcc>,
    extended: [[u32; SLOTS]; 5],
}

impl SkipBlock {
    pub fn new() -> Box<Self> {
        Box::new(Self {
            acc: SkipAcc::new(),
            extended: [[0; SLOTS]; 5],
        })
    }

    /// Sum a block, the position weights as elements.
    pub fn run(&mut self, block: &[u64], weights: &[[u64; 2]]) {
        self.acc.clear();
        for r in 0..5 {
            for z in 0..64 {
                let js = row_positions(r, z);
                for x in 0..5 {
                    extend(&embed(crate::witness::words(block, js[x])), &mut self.extended[x]);
                }
                skip_row(&mut self.acc, &self.extended, std::array::from_fn(|x| &weights[js[x]]));
            }
        }
    }

    /// The two partial products of slot `i`.
    pub fn get(&self, i: usize) -> [u128; 2] {
        self.acc.get(i)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use primitives::test_rng::Rng;

    #[test]
    fn extension_follows_the_ternary_digits() {
        let mut rng = Rng::new(31);
        let v: [u32; GROUP] = std::array::from_fn(|_| rng.next_u64() as u32);
        let out = extend_group(&v);
        let points = mixed_points();
        let mut seen = [false; TERNARY];
        for (i, &p) in points.iter().enumerate() {
            // A digit at infinity sums both points of its variable.
            let digits: [usize; SKIP] = std::array::from_fn(|k| p / 3usize.pow(k as u32) % 3);
            assert!(digits.contains(&2) && !seen[p]);
            seen[p] = true;
            let expected = (0..GROUP)
                .filter(|q| (0..SKIP).all(|k| digits[k] == 2 || digits[k] == q >> k & 1))
                .fold(0, |acc, q| acc ^ v[q]);
            assert_eq!(out[i], expected, "output {i}");
        }
        let slots: std::collections::BTreeSet<usize> =
            (0..2).flat_map(|h| (0..MIXED).map(move |i| slot(h, i))).collect();
        assert_eq!(slots, (0..2 * MIXED).collect());
    }
}
