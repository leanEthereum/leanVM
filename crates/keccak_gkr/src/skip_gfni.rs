//! The first four rounds' sums over a block by GFNI byte products (x86-64 with AVX-512F and
//! GFNI): per [`slot`], the polynomial the five-term row of [`crate::kernels`] sums.
//!
//! A term `w[x] e[x + 1] e[x + 2]` of a row is a binary polynomial of at most
//! `192 + 24 + 24 - 2 = 238` coefficients, and so is a sum of terms. A binary polynomial of at most
//! 240 coefficients is its values at one root of each of the 30 irreducible polynomials of degree
//! 8: a value at a root is a residue modulo the root's minimal polynomial, and the 30 of those
//! multiply to degree 240. In the field of GF2P8MULB a value is a byte, the values of a sum are
//! the sums and the values of a product the byte products. So the kernel has no carry-less
//! product: affine byte maps read the residues off the witness's bytes and the weights'
//! ([`EVAL`], [`WEIGHT`]), a slot's products are byte products, and a last set of byte maps turns
//! a block's sums back into polynomials ([`CRT`]).

use core::arch::x86_64::*;

use register::{LANES, R, load, map, mul, splat, store, xor};

use crate::keccak::{BITS, row_positions};
use crate::kernels::{GROUP, HIGH, SLOTS, slot};
use crate::rmfe::{EMBED_BITS, RMFE};
use crate::witness::BLOCK_WORDS;

/// A register of quadwords and the kernel's operations on it, each of them quadword by quadword
/// or byte by byte.
mod register {
    use core::arch::x86_64::*;

    pub type R = __m512i;
    /// Quadwords in a register.
    pub const LANES: usize = 8;

    /// `x` in every quadword.
    #[inline(always)]
    pub fn splat(x: i64) -> R {
        // SAFETY: AVX-512F is enabled at compile time (`skip_gfni`'s cfg); a register operation.
        unsafe { _mm512_set1_epi64(x) }
    }

    #[inline(always)]
    pub fn load(words: &[i64; LANES]) -> R {
        // SAFETY: AVX-512F is enabled at compile time (`skip_gfni`'s cfg); the load is of the
        // eight words.
        unsafe { _mm512_loadu_si512(words.as_ptr().cast()) }
    }

    #[inline(always)]
    pub fn store(v: R) -> [i64; LANES] {
        let mut words = [0; LANES];
        // SAFETY: AVX-512F is enabled at compile time (`skip_gfni`'s cfg); the store is of the
        // eight words.
        unsafe { _mm512_storeu_si512(words.as_mut_ptr().cast(), v) };
        words
    }

    #[inline(always)]
    pub fn xor(a: R, b: R) -> R {
        // SAFETY: AVX-512F is enabled at compile time (`skip_gfni`'s cfg); a register operation.
        unsafe { _mm512_xor_si512(a, b) }
    }

    /// Each byte of `bytes` through the affine byte map of its quadword of `matrices`.
    #[inline(always)]
    pub fn map(bytes: R, matrices: R) -> R {
        // SAFETY: AVX-512F and GFNI are enabled at compile time (`skip_gfni`'s cfg); a register
        // operation.
        unsafe { _mm512_gf2p8affine_epi64_epi8(bytes, matrices, 0) }
    }

    /// The byte products.
    #[inline(always)]
    pub fn mul(a: R, b: R) -> R {
        // SAFETY: AVX-512F and GFNI are enabled at compile time (`skip_gfni`'s cfg); a register
        // operation.
        unsafe { _mm512_gf2p8mul_epi8(a, b) }
    }
}

/// Points a polynomial is held at.
const POINTS: usize = 30;
/// Registers of a value: a point a quadword, a slice a byte.
const RESIDUES: usize = POINTS.div_ceil(LANES);

/// The byte product: binary polynomials modulo `x^8 + x^4 + x^3 + x + 1`.
const fn gf_mul(a: u8, b: u8) -> u8 {
    let (mut a, mut product) = (a, 0);
    let mut i = 0;
    while i < 8 {
        if b >> i & 1 == 1 {
            product ^= a;
        }
        a = a << 1 ^ if a >> 7 == 1 { 0x1b } else { 0 };
        i += 1;
    }
    product
}

/// `POWERS[i][n]` is point `i` to the power `n`. A point is the least of its eight conjugates,
/// which no element of the subfield of 16 is.
const POWERS: [[u8; 255]; POINTS] = {
    let mut powers = [[1u8; 255]; POINTS];
    let (mut i, mut t) = (0, 0u8);
    while i < POINTS {
        t += 1;
        let (mut conjugate, mut least) = (t, true);
        let mut k = 1;
        while k < 8 {
            conjugate = gf_mul(conjugate, conjugate);
            least &= conjugate > t;
            k += 1;
        }
        if least {
            let mut n = 1;
            while n < 255 {
                powers[i][n] = gf_mul(powers[i][n - 1], t);
                n += 1;
            }
            i += 1;
        }
    }
    powers
};

/// The matrix of the affine byte map sending bit `i` of a byte to `images[i]`: the map reads
/// output bit `t` off matrix byte `7 - t`.
const fn byte_map(images: [u8; 8]) -> i64 {
    let mut matrix = 0u64;
    let mut t = 0;
    while t < 8 {
        let mut i = 0;
        while i < 8 {
            matrix |= ((images[i] >> t & 1) as u64) << (8 * (7 - t) + i);
            i += 1;
        }
        t += 1;
    }
    matrix as i64
}

/// A GF(2)-linear map from a byte to a byte per point (or per byte of a polynomial), as affine
/// byte maps: quadword `k` of register `m` is the matrix to byte `LANES * m + k`, which a
/// register applies to eight bytes at once.
type Maps = [[i64; LANES]; RESIDUES];

/// `EVAL[h]` sends byte `h` of a pack to the residues of its embedding.
const EVAL: [Maps; 2] = {
    let mut maps = [[[0i64; LANES]; RESIDUES]; 2];
    let mut h = 0;
    while h < 2 {
        let mut i = 0;
        while i < POINTS {
            let mut images = [0u8; 8];
            let mut c = 0;
            while c < 8 * EMBED_BITS {
                let (b, n) = (c / EMBED_BITS, c % EMBED_BITS);
                if RMFE.emb[8 * h + b] >> n & 1 == 1 {
                    images[b] ^= POWERS[i][n];
                }
                c += 1;
            }
            maps[h][i / LANES][i % LANES] = byte_map(images);
            i += 1;
        }
        h += 1;
    }
    maps
};

/// `WEIGHT[a]` sends byte `a` of a polynomial of 192 coefficients to its residues.
const WEIGHT: [Maps; 24] = {
    let mut maps = [[[0i64; LANES]; RESIDUES]; 24];
    let mut a = 0;
    while a < 24 {
        let mut i = 0;
        while i < POINTS {
            let mut images = [0u8; 8];
            let mut b = 0;
            while b < 8 {
                images[b] = POWERS[i][8 * a + b];
                b += 1;
            }
            maps[a][i / LANES][i % LANES] = byte_map(images);
            i += 1;
        }
        a += 1;
    }
    maps
};

/// `CRT[i]` sends the residue at point `i` to the bytes of the polynomial of at most 240
/// coefficients with that residue and no other.
///
/// The 240 conjugates of the points are the roots of `G = sum over k <= 16 of X^(15 k)`, and a
/// polynomial `P` of binary coefficients is the sum over them of `P(u) G / ((X - u) G'(u))`, the
/// conjugates of a point adding up to the trace of the point's term. `1 / G'(u)` is `u^16 + u`,
/// which makes coefficient `n` of `G / ((X - u) G'(u))` the sum `u^-n + u^(15 - n % 15)`: bit `n`
/// of `P` is the sum over the points of `trace(P(u) (u^-n + u^(15 - n % 15)))`.
const CRT: [Maps; POINTS] = {
    // Bit `b` of `dual[c]` is the trace of `x^(b + c)`: the trace of `r * a` is the parity of
    // `r` masked by the sum of `dual[c]` over the bits `c` of `a`.
    let mut dual = [0u8; 8];
    let mut c = 0;
    while c < 64 {
        let (mut sum, mut conjugate) = (0, gf_mul(1 << (c / 8), 1 << (c % 8)));
        let mut k = 0;
        while k < 8 {
            sum ^= conjugate;
            conjugate = gf_mul(conjugate, conjugate);
            k += 1;
        }
        dual[c / 8] |= sum << (c % 8);
        c += 1;
    }
    let mut maps = [[[0i64; LANES]; RESIDUES]; POINTS];
    let mut i = 0;
    while i < POINTS {
        let mut n = 0;
        while n < 8 * POINTS {
            let a = POWERS[i][(255 - n) % 255] ^ POWERS[i][15 - n % 15];
            let (mut mask, mut c) = (0u8, 0);
            while c < 8 {
                if a >> c & 1 == 1 {
                    mask ^= dual[c];
                }
                c += 1;
            }
            // Output bit `n % 8` of byte `n / 8`, read off matrix byte `7 - n % 8`.
            maps[i][n / 8 / LANES][n / 8 % LANES] |= (mask as i64) << (8 * (7 - n % 8));
            n += 1;
        }
        i += 1;
    }
    maps
};

/// The bytes a quadword `x`, taken as an affine byte map, sends to the columns of its bits: byte
/// `7 - t` of `map(COLUMNS, x)` holds bit `t` of each byte of `x`.
const COLUMNS: i64 = 0x0102_0408_1020_4080;

/// Eight rows of 32 bytes, transposed: byte `z` of quadword `2 l + h` of output `d` is byte
/// `16 l + 2 d + h` of row `z`. Three rounds of interleaving, of bytes, pairs and fours.
#[inline(always)]
fn transpose_bytes(rows: [__m256i; 8]) -> [[i64; 4]; 8] {
    // SAFETY: AVX2 is enabled at compile time (`skip_gfni`'s cfg implies it); register
    // operations, and each store is of a register into four words.
    unsafe {
        let a: [__m256i; 8] = std::array::from_fn(|i| {
            if i % 2 == 0 {
                _mm256_unpacklo_epi8(rows[i], rows[i + 1])
            } else {
                _mm256_unpackhi_epi8(rows[i - 1], rows[i])
            }
        });
        // Rows `4 r ..`, bytes `16 l + 4 c ..` of them.
        let b: [__m256i; 8] = std::array::from_fn(|i| {
            let (r, c) = (i / 4, i % 4);
            let (x, y) = (a[4 * r + c / 2], a[4 * r + 2 + c / 2]);
            if c % 2 == 0 {
                _mm256_unpacklo_epi16(x, y)
            } else {
                _mm256_unpackhi_epi16(x, y)
            }
        });
        let mut out = [[0i64; 4]; 8];
        for (d, out) in out.iter_mut().enumerate() {
            let (x, y) = (b[d / 2], b[4 + d / 2]);
            let v = if d % 2 == 0 {
                _mm256_unpacklo_epi32(x, y)
            } else {
                _mm256_unpackhi_epi32(x, y)
            };
            _mm256_storeu_si256(out.as_mut_ptr().cast(), v);
        }
        out
    }
}

/// Byte `b` of each of the eight rows [`transpose_bytes`] transposed into `bytes`.
#[inline(always)]
fn byte(bytes: &[[i64; 4]; 8], b: usize) -> i64 {
    bytes[b % 16 / 2][2 * (b / 16) + b % 2]
}

/// The four words `words`, a row for [`transpose_bytes`].
#[inline(always)]
fn row(words: [i64; 4]) -> __m256i {
    // SAFETY: AVX is enabled at compile time (`skip_gfni`'s cfg implies it); a register operation.
    unsafe { _mm256_setr_epi64x(words[0], words[1], words[2], words[3]) }
}

/// `acc += maps(bytes)`, on a byte of each of eight things.
#[inline(always)]
fn add_mapped(acc: &mut [R; RESIDUES], bytes: i64, maps: &Maps) {
    let bytes = splat(bytes);
    for (acc, matrices) in acc.iter_mut().zip(maps) {
        *acc = xor(*acc, map(bytes, load(matrices)));
    }
}

/// Streams of values [`SkipBlock`] extends together: `e[0], e[2], e[4]` and their stars.
const STREAMS: usize = 6;

/// [`extend_group`](crate::kernels::extend_group) on registers, each of eight positions' values,
/// for [`STREAMS`] groups at once and an output at a time: `output(i, values)` takes output `i`
/// of every group. The nine vectors of four are made one after the other, so a group has four
/// registers live and nothing is stored.
#[inline(always)]
fn extend8(v: &[[R; GROUP]; STREAMS], mut output: impl FnMut(usize, [R; STREAMS])) {
    for k in 0..HIGH.len() {
        // Vector `k` of each group: one of its four, or a sum of them.
        let w: [[R; 4]; STREAMS] = std::array::from_fn(|f| {
            std::array::from_fn(|l| {
                let q = |k: usize| v[f][4 * k + l];
                match k {
                    0..4 => q(k),
                    4 => xor(q(0), q(1)),
                    5 => xor(q(2), q(3)),
                    6 => xor(q(0), q(2)),
                    7 => xor(q(1), q(3)),
                    _ => xor(xor(q(0), q(1)), xor(q(2), q(3))),
                }
            })
        });
        if k >= 4 {
            for l in 0..4 {
                output(4 * (k - 4) + l, w.map(|w| w[l]));
            }
        }
        let low = w.map(|w| [xor(w[0], w[1]), xor(w[2], w[3]), xor(w[0], w[2]), xor(w[1], w[3])]);
        for l in 0..4 {
            output(20 + 4 * k + l, low.map(|low| low[l]));
        }
        output(56 + k, low.map(|low| xor(low[0], low[1])));
    }
}

/// [`skip_row`](crate::kernels::skip_row) over every row and slice of a block, eight slices at a
/// time, on residues: a register holds a value of eight positions at [`LANES`] points, so the
/// extension is a sum of registers and a product of two values is [`RESIDUES`] byte products of
/// registers.
///
/// A row's sum `sum over x of w[x] e[x + 1] e[x + 2]` is taken as
/// `e[2] (w[0] e[1] + w[1] e[3]) + e[4] (w[2] e[3] + w[3] e[0]) + e[0] (w[4] e[1])`: the three
/// stars are linear in the values, so they are multiplied out on the group's packs and extended
/// like them, and a slot takes three products.
pub struct SkipBlock {
    /// Per register of residues and slot, the slot's sum, the eight slices' apart.
    acc: [[R; SLOTS]; RESIDUES],
    /// The sums: word `k` of slot `i`'s at `sums[k][i]`.
    sums: [[u64; SLOTS]; 4],
    /// A group of each position of a row, transposed over eight slices.
    bytes: [[[i64; 4]; 8]; 5],
    /// A register of the residues of `e[0], e[2], e[4]` and their stars on the group's packs.
    values: [[R; GROUP]; STREAMS],
    /// The weights' residues, eight consecutive positions to an entry.
    weights: Vec<[R; RESIDUES]>,
}

impl SkipBlock {
    /// For blocks summed at the position weights `weights`, as elements.
    pub fn new(weights: &[[u64; 3]]) -> Box<Self> {
        assert!(weights.len() >= BITS);
        let mut residues = vec![[splat(0); RESIDUES]; BITS / 8];
        for (residues, weights) in residues.iter_mut().zip(weights.as_chunks::<8>().0) {
            let bytes = transpose_bytes(weights.map(|w| row([w[0] as i64, w[1] as i64, w[2] as i64, 0])));
            for (a, maps) in WEIGHT.iter().enumerate() {
                add_mapped(residues, byte(&bytes, a), maps);
            }
        }
        Box::new(Self {
            acc: [[splat(0); SLOTS]; RESIDUES],
            sums: [[0; SLOTS]; 4],
            bytes: [[[0; 4]; 8]; 5],
            values: [[splat(0); GROUP]; STREAMS],
            weights: residues,
        })
    }

    /// Sum a block.
    pub fn run(&mut self, block: &[u64]) {
        self.acc = [[splat(0); SLOTS]; RESIDUES];
        // A group over the whole block, then the other: one group's sums stay in cache.
        for half in 0..2 {
            for r in 0..5 {
                for z in (0..64).step_by(8) {
                    let js = row_positions(r, z);
                    for (bytes, &j) in self.bytes.iter_mut().zip(&js) {
                        // Eight positions from `j`, each as its two groups of four words.
                        let groups = block[BLOCK_WORDS * j..][..8 * BLOCK_WORDS]
                            .as_chunks::<{ BLOCK_WORDS / 2 }>()
                            .0;
                        *bytes = transpose_bytes(std::array::from_fn(|i| {
                            // SAFETY: AVX is enabled at compile time (`skip_gfni`'s cfg implies
                            // it); the load is of a group's four words.
                            unsafe { _mm256_loadu_si256(groups[2 * i + half].as_ptr().cast()) }
                        }));
                    }
                    for m in 0..RESIDUES {
                        self.run_group(half, m, js.map(|j| self.weights[j / 8][m]));
                    }
                }
            }
        }
        self.reconstruct();
    }

    /// Register `m` of the residues of one group of the positions [`Self::run`] transposed, at
    /// the row's weights `w`.
    #[inline(always)]
    fn run_group(&mut self, half: usize, m: usize, w: [R; 5]) {
        let Self { acc, bytes, values, .. } = self;
        let maps = [0, 1].map(|h| load(&EVAL[h][m]));
        for q in 0..GROUP {
            let e: [R; 5] = std::array::from_fn(|x| {
                let [low, high] = [0, 1].map(|h| map(splat(byte(&bytes[x], 2 * q + h)), maps[h]));
                xor(low, high)
            });
            values[0][q] = e[0];
            values[1][q] = e[2];
            values[2][q] = e[4];
            values[3][q] = xor(mul(e[1], w[0]), mul(e[3], w[1]));
            values[4][q] = xor(mul(e[3], w[2]), mul(e[0], w[3]));
            values[5][q] = mul(e[1], w[4]);
        }
        extend8(values, |i, [e0, e2, e4, a, b, c]| {
            let acc = &mut acc[m][slot(half, i)];
            *acc = xor(xor(*acc, mul(e2, a)), xor(mul(e4, b), mul(e0, c)));
        });
    }

    /// The block's sums as polynomials, eight slots at a time: a slot's residues are summed over
    /// its slices into a byte each, which the eight slots' share a quadword for [`CRT`].
    #[inline(always)]
    fn reconstruct(&mut self) {
        for g in 0..SLOTS / 8 {
            let mut points = [[0i64; LANES]; RESIDUES];
            for (points, acc) in points.iter_mut().zip(&self.acc) {
                let mut residues = splat(0);
                for (i, &x) in acc[8 * g..][..8].iter().enumerate() {
                    // The parity of each column of the slices' bits, at byte `i`.
                    let at = splat((0xffu64 << (8 * i)) as i64);
                    residues = xor(residues, map(at, map(splat(COLUMNS), x)));
                }
                *points = store(residues);
            }
            let mut bytes = [splat(0); RESIDUES];
            for (point, maps) in points.as_flattened().iter().zip(&CRT) {
                add_mapped(&mut bytes, *point, maps);
            }
            // Byte `i` of quadword `b` is byte `b` of slot `i`'s polynomial: transposed, a
            // quadword is a word of a slot's.
            let bytes = bytes.map(store);
            let bytes = bytes.as_flattened();
            let words = transpose_bytes(std::array::from_fn(|z| {
                row([bytes[z], bytes[8 + z], bytes[16 + z], bytes[24 + z]])
            }));
            for i in 0..8 {
                for (k, sums) in self.sums.iter_mut().enumerate() {
                    sums[8 * g + i] = byte(&words, 8 * k + i) as u64;
                }
            }
        }
    }

    /// The sum at slot `i`, laid out as the other arms' three partial products are: double words
    /// from words 0, 1 and 2 of the polynomial, the middle one empty.
    pub fn get(&self, i: usize) -> [u128; 3] {
        let word = |k: usize| u128::from(self.sums[k][i]);
        [word(0) | word(1) << 64, 0, word(2) | word(3) << 64]
    }
}

#[cfg(test)]
mod tests {
    use primitives::test_rng::Rng;

    use super::*;

    /// The value at point `i` of the polynomial of words `p`.
    fn residue(p: &[u64], i: usize) -> u8 {
        (0..64 * p.len())
            .filter(|n| p[n / 64] >> (n % 64) & 1 == 1)
            .fold(0, |value, n| value ^ POWERS[i][n])
    }

    /// Byte `z` of point `i` of a value.
    fn at(value: &[R; RESIDUES], i: usize, z: usize) -> u8 {
        store(value[i / LANES])[i % LANES].to_le_bytes()[z]
    }

    #[test]
    fn residues_are_the_values_at_the_points_and_recover_the_polynomial() {
        let mut rng = Rng::new(33);
        let weights: Vec<[u64; 3]> = (0..BITS).map(|_| std::array::from_fn(|_| rng.next_u64())).collect();
        let mut skip = SkipBlock::new(&weights);
        for (j, w) in weights.iter().enumerate() {
            for i in 0..POINTS {
                assert_eq!(at(&skip.weights[j / 8], i, j % 8), residue(w, i), "weight {j} at {i}");
            }
        }
        for _ in 0..50 {
            let pack = rng.next_u64() as u16;
            let mut e = [splat(0); RESIDUES];
            for (h, maps) in EVAL.iter().enumerate() {
                add_mapped(&mut e, i64::from(pack.to_le_bytes()[h]), maps);
            }
            for i in 0..POINTS {
                assert_eq!(at(&e, i, 0), residue(&[u64::from(RMFE.embed(pack))], i), "point {i}");
            }
        }
        // A polynomial of 240 coefficients per slot and slice: a slot's sum is its slices' sum.
        let polys: Vec<[[u64; 4]; 8]> = (0..SLOTS)
            .map(|_| std::array::from_fn(|_| std::array::from_fn(|k| rng.next_u64() >> if k == 3 { 16 } else { 0 })))
            .collect();
        for (m, acc) in skip.acc.iter_mut().enumerate() {
            for (acc, polys) in acc.iter_mut().zip(&polys) {
                *acc = load(&std::array::from_fn(|k| match LANES * m + k {
                    i if i < POINTS => i64::from_le_bytes(polys.map(|p| residue(&p, i))),
                    _ => 0,
                }));
            }
        }
        skip.reconstruct();
        for (i, polys) in polys.iter().enumerate() {
            let sum = polys
                .iter()
                .fold([0; 4], |sum, p| std::array::from_fn(|k| sum[k] ^ p[k]));
            assert_eq!(crate::basis::carry(&skip.get(i)), sum, "slot {i}");
        }
    }
}
