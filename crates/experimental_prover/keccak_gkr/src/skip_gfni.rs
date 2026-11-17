//! The four bit-level rounds' sums over a block, on residues (GFNI, with AVX-512 or AVX2): per
//! [`slot`], the polynomial [`skip_row`](crate::kernels::skip_row) sums over the block.
//!
//! A row's term `w[x] e[x + 1] e[x + 2]`, a weight of 128 coefficients times two embeddings of 24,
//! has degree at most `127 + 23 + 23 = 173`, and so has a block's sum. A binary polynomial of degree
//! below 192 is fixed by its residues modulo 24 distinct irreducibles of degree 8, whose product has
//! degree 192. Its residue modulo one is its value at a root in GF(2^8), the field of GF2P8MULB: a
//! byte, where a sum is a XOR and a product a byte product. Of the 30 irreducibles of degree 8,
//! [`POWERS`] takes a root of 24, three registers of eight with AVX-512, six of four with AVX2.
//!
//! So nothing is a carry-less product: affine byte maps send the witness's bytes and the weights' to
//! residues ([`EVAL`], [`WEIGHT`]), and a slot's products are byte products. Once a block, a slot's
//! residues are summed over its eight slices and affine byte maps send them back to coefficients
//! ([`CRT`], the inverse of the residue map).

use core::arch::x86_64::*;

use primitives::hash::positions::row_positions;
use verifier::keccak::{BITS, EMBED_BITS};

use crate::kernels::{GROUP, SLOTS, slot};
use crate::rmfe::RMFE;
use crate::witness::BLOCK_WORDS;

cfg_select! {
    target_feature = "avx512f" => { type V = __m512i; }
    _ => { type V = __m256i; }
}
/// Quadwords of a [`V`].
const LANES: usize = size_of::<V>() / 8;

/// Points a polynomial is held at.
const POINTS: usize = 24;
const _: () = assert!(
    127 + 2 * (EMBED_BITS - 1) < 8 * POINTS,
    "a slot's sum has more coefficients than the points fix"
);
/// Registers of a value: a point to a quadword, a slice to a byte.
const RESIDUES: usize = POINTS / LANES;
/// Words of a block's sum at a slot, a polynomial of fewer than `8 * POINTS` coefficients.
const WORDS: usize = POINTS / 8;

/// `$zmm` with AVX-512, else `$ymm`.
macro_rules! width {
    ($zmm:expr, $ymm:expr $(,)?) => {
        // SAFETY: the module's cfg enables AVX2 and GFNI, and the AVX-512 arm's AVX-512F.
        unsafe {
            cfg_select! {
                target_feature = "avx512f" => { $zmm }
                _ => { $ymm }
            }
        }
    };
}

/// `x` in every quadword.
#[inline(always)]
fn splat(x: u64) -> V {
    width!(_mm512_set1_epi64(x as i64), _mm256_set1_epi64x(x as i64))
}

#[inline(always)]
fn load(words: &[u64; LANES]) -> V {
    let p = words.as_ptr().cast();
    // SAFETY (with `width!`'s): `p` is to one `V`, which an unaligned load reads.
    width!(_mm512_loadu_si512(p), _mm256_loadu_si256(p))
}

#[inline(always)]
fn store(v: V) -> [u64; LANES] {
    let mut words = [0; LANES];
    let p = words.as_mut_ptr().cast();
    // SAFETY (with `width!`'s): `p` is to one `V`, which an unaligned store writes.
    width!(_mm512_storeu_si512(p, v), _mm256_storeu_si256(p, v));
    words
}

#[inline(always)]
fn xor(a: V, b: V) -> V {
    width!(_mm512_xor_si512(a, b), _mm256_xor_si256(a, b))
}

/// Each byte of `bytes` through the affine byte map of its quadword of `matrices`.
#[inline(always)]
fn map(bytes: V, matrices: V) -> V {
    width!(
        _mm512_gf2p8affine_epi64_epi8(bytes, matrices, 0),
        _mm256_gf2p8affine_epi64_epi8(bytes, matrices, 0),
    )
}

/// The byte products.
#[inline(always)]
fn mul(a: V, b: V) -> V {
    width!(_mm512_gf2p8mul_epi8(a, b), _mm256_gf2p8mul_epi8(a, b))
}

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

/// `POWERS[i][n]` is point `i` to the power `n`. A point is the least of its eight conjugates, the
/// roots of its irreducible, so no two share one; an element of a proper subfield has fewer.
const POWERS: [[u8; 8 * POINTS]; POINTS] = {
    let mut powers = [[1u8; 8 * POINTS]; POINTS];
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
            while n < 8 * POINTS {
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
const fn byte_map(images: [u8; 8]) -> u64 {
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
    matrix
}

/// A GF(2)-linear map from a byte to a byte per point (or per byte of a polynomial), as affine
/// byte maps: quadword `k` of register `m` is the matrix to byte `LANES * m + k`, which a register
/// applies to eight bytes at once.
type Maps = [[u64; LANES]; RESIDUES];

/// `EVAL[h]` sends byte `h` of a pack to the residues of its share of the pack's embedding.
const EVAL: [Maps; 2] = {
    let mut maps = [[[0u64; LANES]; RESIDUES]; 2];
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

/// `WEIGHT[a]` sends byte `a` of a weight, a polynomial of 128 coefficients, to its residues.
const WEIGHT: [Maps; 16] = {
    let mut maps = [[[0u64; LANES]; RESIDUES]; 16];
    let mut a = 0;
    while a < 16 {
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

/// `CRT[i]` sends the residue at point `i` to the bytes of the polynomial of fewer than
/// `8 * POINTS` coefficients with that residue and zero at the other points: column `i` of the
/// inverse of the residue map on such polynomials, by Gauss-Jordan elimination.
const CRT: [Maps; POINTS] = {
    const N: usize = 8 * POINTS;
    // Row `8 i + t` sends a polynomial to bit `t` of its residue at point `i`, beside the row of
    // the identity that the row operations turn into the inverse's.
    let mut rows = [[0u64; 2 * WORDS]; N];
    let mut r = 0;
    while r < N {
        let mut n = 0;
        while n < N {
            rows[r][n / 64] |= ((POWERS[r / 8][n] >> (r % 8) & 1) as u64) << (n % 64);
            n += 1;
        }
        rows[r][WORDS + r / 64] |= 1 << (r % 64);
        r += 1;
    }
    let mut c = 0;
    while c < N {
        let mut p = c;
        while rows[p][c / 64] >> (c % 64) & 1 == 0 {
            p += 1;
        }
        let pivot = rows[p];
        rows.swap(p, c);
        let mut r = 0;
        while r < N {
            if r != c && rows[r][c / 64] >> (c % 64) & 1 == 1 {
                let mut k = 0;
                while k < 2 * WORDS {
                    rows[r][k] ^= pivot[k];
                    k += 1;
                }
            }
            r += 1;
        }
        c += 1;
    }
    // Row `n` sends the residues to coefficient `n`: bit `n % 8` of byte `n / 8`, which a map
    // reads off matrix byte `7 - n % 8`.
    let mut maps = [[[0u64; LANES]; RESIDUES]; POINTS];
    let mut n = 0;
    while n < N {
        let mut r = 0;
        while r < N {
            let bit = rows[n][WORDS + r / 64] >> (r % 64) & 1;
            maps[r / 8][n / 8 / LANES][n / 8 % LANES] |= bit << (8 * (7 - n % 8) + r % 8);
            r += 1;
        }
        n += 1;
    }
    maps
};

/// The bytes an affine byte map `x` sends to the transpose of `x`: byte `7 - t` of
/// `map(splat(COLUMNS), x)` holds bit `t` of each byte of `x`.
const COLUMNS: u64 = 0x0102_0408_1020_4080;

/// Eight rows of 32 bytes, transposed: byte `z` of quadword `b` is byte `b` of row `z`. Three
/// rounds of interleaving, of bytes, pairs and fours, leave each 128-bit half in its own place.
#[inline(always)]
fn transpose_bytes(rows: [[u64; 4]; 8]) -> [u64; 32] {
    // SAFETY: AVX2 is enabled at compile time (the module's cfg); each load is of a row, and each
    // store of a half register into two of the 32 words.
    unsafe {
        let rows: [__m256i; 8] = rows.map(|row| _mm256_loadu_si256(row.as_ptr().cast()));
        let a: [__m256i; 8] = std::array::from_fn(|i| {
            if i % 2 == 0 {
                _mm256_unpacklo_epi8(rows[i], rows[i + 1])
            } else {
                _mm256_unpackhi_epi8(rows[i - 1], rows[i])
            }
        });
        // `b[4 r + c]`, in lane `l`: bytes `16 l + 4 c ..` of rows `4 r ..`.
        let b: [__m256i; 8] = std::array::from_fn(|i| {
            let (r, c) = (i / 4, i % 4);
            let (x, y) = (a[4 * r + c / 2], a[4 * r + 2 + c / 2]);
            if c % 2 == 0 {
                _mm256_unpacklo_epi16(x, y)
            } else {
                _mm256_unpackhi_epi16(x, y)
            }
        });
        // Register `d` holds bytes `2 d, 2 d + 1` of the rows, then bytes `16 + 2 d, 17 + 2 d`.
        let mut out = [0u64; 32];
        for d in 0..8 {
            let (x, y) = (b[d / 2], b[4 + d / 2]);
            let v = if d % 2 == 0 {
                _mm256_unpacklo_epi32(x, y)
            } else {
                _mm256_unpackhi_epi32(x, y)
            };
            _mm256_storeu2_m128i(
                out.as_mut_ptr().add(16 + 2 * d).cast(),
                out.as_mut_ptr().add(2 * d).cast(),
                v,
            );
        }
        out
    }
}

/// `acc += maps(b)` for each byte `b` of `bytes`, kept in `b`'s byte of every quadword.
#[inline(always)]
fn add_mapped(acc: &mut [V; RESIDUES], bytes: u64, maps: &Maps) {
    let bytes = splat(bytes);
    for (acc, matrices) in acc.iter_mut().zip(maps) {
        *acc = xor(*acc, map(bytes, load(matrices)));
    }
}

/// The factors of a slot's three products, `e[2], e[4], e[0]`, each followed by its cofactor.
const FACTORS: usize = 6;

/// [`extend_group`](crate::kernels::extend_group) on registers, for `F` groups at once:
/// `output(i, values)` takes output `i` of every group. The nine vectors of four are made one at a
/// time and passed straight to `output`, so nothing is stored.
#[inline(always)]
fn extend8<const F: usize>(v: &[[V; GROUP]; F], mut output: impl FnMut(usize, [V; F])) {
    for k in 0..9 {
        // Vector `k` of each group: one of its four, or a sum of them.
        let w: [[V; 4]; F] = std::array::from_fn(|f| {
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
/// time, on residues: a register holds a value of eight slices at `LANES` points, so the extension
/// is a sum of registers and a product of two values is [`RESIDUES`] byte products of registers.
///
/// A row's sum `sum over x of w[x] e[x + 1] e[x + 2]` is taken as
/// `e[2] (w[0] e[1] + w[1] e[3]) + e[4] (w[2] e[3] + w[3] e[0]) + e[0] (w[4] e[1])`: the three
/// cofactors are linear in the values, so they are multiplied out on the group's packs and extended
/// like them, and a slot takes three products.
pub struct SkipBlock {
    /// Per register of residues and slot, the slot's sum, the eight slices apart.
    acc: [[V; SLOTS]; RESIDUES],
    /// Per slot, the block's sum.
    sums: [[u64; WORDS]; SLOTS],
    /// The [`FACTORS`]' residues on the group's packs, a register each.
    values: [[V; GROUP]; FACTORS],
    /// The weights' residues, eight consecutive positions to an entry.
    weights: Vec<[V; RESIDUES]>,
}

impl SkipBlock {
    /// For blocks summed at the position weights `weights`, as polynomials.
    pub fn new(weights: &[[u64; 2]]) -> Box<Self> {
        let mut residues = vec![[splat(0); RESIDUES]; BITS / 8];
        for (residues, weights) in residues.iter_mut().zip(weights[..BITS].as_chunks::<8>().0) {
            let bytes = transpose_bytes(weights.map(|w| [w[0], w[1], 0, 0]));
            for (&bytes, maps) in bytes.iter().zip(&WEIGHT) {
                add_mapped(residues, bytes, maps);
            }
        }
        Box::new(Self {
            acc: [[splat(0); SLOTS]; RESIDUES],
            sums: [[0; WORDS]; SLOTS],
            values: [[splat(0); GROUP]; FACTORS],
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
                    // Eight positions from each `j`, each as its two groups of four words.
                    let bytes = js.map(|j| {
                        let groups = block[BLOCK_WORDS * j..][..8 * BLOCK_WORDS].as_chunks::<4>().0;
                        transpose_bytes(std::array::from_fn(|i| groups[2 * i + half]))
                    });
                    for m in 0..RESIDUES {
                        self.run_group(half, m, &bytes, js.map(|j| self.weights[j / 8][m]));
                    }
                }
            }
        }
        self.reconstruct();
    }

    /// Adds to register `m` of the residues group `half` of a row's positions, `bytes` as
    /// [`Self::run`] transposed them, at the row's weights `w`.
    #[inline(always)]
    fn run_group(&mut self, half: usize, m: usize, bytes: &[[u64; 32]; 5], w: [V; 5]) {
        let Self { acc, values, .. } = self;
        let maps = [0, 1].map(|h| load(&EVAL[h][m]));
        for q in 0..GROUP {
            let e: [V; 5] = std::array::from_fn(|x| {
                let [low, high] = [0, 1].map(|h| map(splat(bytes[x][2 * q + h]), maps[h]));
                xor(low, high)
            });
            values[0][q] = e[2];
            values[1][q] = xor(mul(e[1], w[0]), mul(e[3], w[1]));
            values[2][q] = e[4];
            values[3][q] = xor(mul(e[3], w[2]), mul(e[0], w[3]));
            values[4][q] = e[0];
            values[5][q] = mul(e[1], w[4]);
        }
        if cfg!(target_feature = "avx512f") {
            extend8(values, |i, [e2, a, e4, b, e0, c]| {
                let acc = &mut acc[m][slot(half, i)];
                *acc = xor(xor(*acc, mul(e2, a)), xor(mul(e4, b), mul(e0, c)));
            });
        } else {
            // A product at a time: six groups' extensions at once spill AVX2's sixteen registers.
            for pair in values.as_chunks::<2>().0 {
                extend8(pair, |i, [e, c]| {
                    let acc = &mut acc[m][slot(half, i)];
                    *acc = xor(*acc, mul(e, c));
                });
            }
        }
    }

    /// The block's sums as polynomials, eight slots at a time: a slot's residues are summed over its
    /// slices into a byte per point, and the eight slots' bytes share a quadword for [`CRT`].
    #[inline(always)]
    fn reconstruct(&mut self) {
        for g in 0..SLOTS / 8 {
            let mut points = [[0u64; LANES]; RESIDUES];
            for (points, acc) in points.iter_mut().zip(&self.acc) {
                let mut residues = splat(0);
                for (i, &x) in acc[8 * g..][..8].iter().enumerate() {
                    // Byte `i`: per quadword, the XOR of its eight bytes, the slices.
                    let at = splat(0xff << (8 * i));
                    residues = xor(residues, map(at, map(splat(COLUMNS), x)));
                }
                *points = store(residues);
            }
            let mut bytes = [splat(0); RESIDUES];
            for (&point, maps) in points.as_flattened().iter().zip(&CRT) {
                add_mapped(&mut bytes, point, maps);
            }
            // Byte `i` of quadword `b` is byte `b` of slot `i`'s polynomial: transposed, a
            // quadword is a word of a slot's.
            let bytes = bytes.map(store);
            let bytes = bytes.as_flattened();
            let words = transpose_bytes(std::array::from_fn(|z| [bytes[z], bytes[8 + z], bytes[16 + z], 0]));
            for i in 0..8 {
                self.sums[8 * g + i] = std::array::from_fn(|k| words[8 * k + i]);
            }
        }
    }

    /// The sum at slot `i`.
    pub fn get(&self, i: usize) -> [u64; 3] {
        self.sums[i]
    }
}
