//! The bit-level kernels of the layer prover, over one block position at a time: the 32 packs of
//! one bit position of one block.
//!
//! Each has a portable form, an AVX-512 one (AVX-512BW, VPCLMULQDQ, GFNI), an AVX2 one
//! (PCLMULQDQ, and VPCLMULQDQ where it is) and a NEON one (PMULL), which agree bit for bit. The
//! vector forms are compiled only where their features are.

use primitives::field::gf2_64::mul_wide;

use crate::rmfe::RMFE;
use crate::witness::BLOCK_WORDS;

cfg_select! {
    all(
        target_arch = "x86_64",
        target_feature = "avx512f",
        target_feature = "avx512bw",
        target_feature = "vpclmulqdq",
        target_feature = "gfni"
    ) => {
        use x86 as simd;
    }
    all(
        target_arch = "x86_64",
        target_feature = "avx2",
        target_feature = "pclmulqdq",
        not(target_feature = "avx512f")
    ) => {
        use avx2 as simd;
    }
    all(target_arch = "aarch64", target_feature = "aes") => {
        use neon as simd;
    }
    _ => {
        mod simd {
            pub use super::{
                embed_extend_portable as embed_extend, embed_portable as embed, fold_groups_portable as fold_groups,
                products_portable as products, skip_row_portable as skip_row,
            };
        }
    }
}

/// Packs in a block position.
pub const PACKS: usize = 32;
/// Packs the bit-level rounds fold together: half a block.
pub const GROUP: usize = 16;
/// Variables indexing the packs of a group.
pub const SKIP: usize = 4;
/// Points of `{0, 1, infinity}^SKIP`, and those of them with a coordinate at infinity.
pub const TERNARY: usize = 81;
pub const MIXED: usize = 65;
/// The mixed points of a block position's two groups, rounded up to whole vectors.
pub const SLOTS: usize = 136;

/// Sums of `value * weight word`, a 128-bit product each, laid out as the vector kernel leaves
/// them: entry `i` of a run of eight sits at `[2 * (i / 8) + i % 2][(i % 8) / 2]`.
#[derive(Clone, Copy)]
#[repr(C, align(64))]
pub struct Lanes(pub [u128; 4]);

/// Per mixed point of each group, the sum over positions of `weight * product`, as three
/// partial products.
pub struct SkipAcc(pub [[Lanes; SLOTS / 4]; 3]);

impl SkipAcc {
    pub fn new() -> Box<Self> {
        Box::new(Self([[Lanes([0; 4]); SLOTS / 4]; 3]))
    }

    pub fn clear(&mut self) {
        self.0 = [[Lanes([0; 4]); SLOTS / 4]; 3];
    }

    /// The three partial products of slot `i`.
    pub fn get(&self, i: usize) -> [u128; 3] {
        std::array::from_fn(|k| self.0[k][2 * (i / 8) + i % 2].0[(i % 8) / 2])
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
pub fn extend_group(v: &[u32; GROUP]) -> [u32; MIXED] {
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
pub fn mixed_points() -> [usize; MIXED] {
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

/// [`extend`] of [`embed`].
#[inline(always)]
pub fn embed_extend(words: &[u64; BLOCK_WORDS], out: &mut [u32; SLOTS]) {
    simd::embed_extend(words, out)
}

pub fn embed_extend_portable(words: &[u64; BLOCK_WORDS], out: &mut [u32; SLOTS]) {
    extend(&embed(words), out)
}

/// The 32 packs of a block position, embedded.
#[inline(always)]
pub fn embed(words: &[u64; BLOCK_WORDS]) -> [u32; PACKS] {
    simd::embed(words)
}

pub fn embed_portable(words: &[u64; BLOCK_WORDS]) -> [u32; PACKS] {
    std::array::from_fn(|q| RMFE.embed((words[q / 4] >> (16 * (q % 4))) as u16))
}

/// The unprojected `chi` of 32 packs: `ones * (a + c) + b * c`.
#[inline(always)]
pub fn products(a: &[u32; PACKS], b: &[u32; PACKS], c: &[u32; PACKS]) -> [u64; PACKS] {
    simd::products(a, b, c)
}

pub fn products_portable(a: &[u32; PACKS], b: &[u32; PACKS], c: &[u32; PACKS]) -> [u64; PACKS] {
    let ones = RMFE.ones as u64;
    std::array::from_fn(|q| (mul_wide(ones, (a[q] ^ c[q]) as u64) ^ mul_wide(b[q] as u64, c[q] as u64)) as u64)
}

/// One row of five positions, which `chi` mixes cyclically: for every pattern,
/// `acc[p] += sum over x of weights[x] * e[x + 1][p] * e[x + 2][p]`.
#[inline(always)]
pub fn skip_row(acc: &mut SkipAcc, e: &[[u32; SLOTS]; 5], weights: [&[u64; 3]; 5]) {
    simd::skip_row(acc, e, weights)
}

pub fn skip_row_portable(acc: &mut SkipAcc, e: &[[u32; SLOTS]; 5], weights: [&[u64; 3]; 5]) {
    for x in 0..5 {
        let (b, c) = (&e[(x + 1) % 5], &e[(x + 2) % 5]);
        for p in 0..SLOTS {
            let product = mul_wide(b[p] as u64, c[p] as u64) as u64;
            for k in 0..3 {
                acc.0[k][2 * (p / 8) + p % 2].0[(p % 8) / 2] ^= mul_wide(product, weights[x][k]);
            }
        }
    }
}

/// For both groups of a block position, `sum over the group's packs of weights[.][q] * e[q]`,
/// as three partial products.
#[inline(always)]
pub fn fold_groups(e: &[u32; PACKS], weights: &[[u64; GROUP]; 3]) -> [[u128; 3]; 2] {
    simd::fold_groups(e, weights)
}

pub fn fold_groups_portable(e: &[u32; PACKS], weights: &[[u64; GROUP]; 3]) -> [[u128; 3]; 2] {
    std::array::from_fn(|half| {
        std::array::from_fn(|k| (0..GROUP).fold(0, |acc, q| acc ^ mul_wide(e[GROUP * half + q] as u64, weights[k][q])))
    })
}

/// Byte `k` of the embedding of each nibble of a pack: table `4 * k + n` is nibble `n`, low
/// first. The vector forms without an affine byte map look an embedding up a nibble at a time.
pub static NIBBLES: [[u8; 16]; 12] = {
    let mut tables = [[0u8; 16]; 12];
    let mut i = 0;
    while i < 12 {
        let (k, n) = (i / 4, i % 4);
        let mut v = 0;
        while v < 16 {
            let mut e = 0;
            let mut t = 0;
            while t < 4 {
                if v >> t & 1 == 1 {
                    e ^= RMFE.emb[4 * n + t];
                }
                t += 1;
            }
            tables[i][v] = (e >> (8 * k)) as u8;
            v += 1;
        }
        i += 1;
    }
    tables
};

/// The five positions of a row and slice, which `chi` mixes.
#[inline(always)]
fn row_positions(row: usize, z: usize) -> [usize; 5] {
    std::array::from_fn(|x| 64 * (x + 5 * row) + z)
}

#[inline(always)]
fn words(block: &[u64], j: usize) -> &[u64; BLOCK_WORDS] {
    block[j * BLOCK_WORDS..][..BLOCK_WORDS].try_into().expect("eight words")
}

/// [`skip_row`] over every row and slice of a block, the position weights as elements: per
/// [`slot`], the three partial products.
pub fn skip_block_portable(block: &[u64], weights: &[[u64; 3]]) -> Vec<[u128; 3]> {
    let mut acc = SkipAcc::new();
    let mut extended = [[0u32; SLOTS]; 5];
    for r in 0..5 {
        for z in 0..64 {
            let js = row_positions(r, z);
            for x in 0..5 {
                extend(&embed_portable(words(block, js[x])), &mut extended[x]);
            }
            skip_row_portable(&mut acc, &extended, std::array::from_fn(|x| &weights[js[x]]));
        }
    }
    (0..2 * MIXED).map(|i| acc.get(i)).collect()
}

cfg_select! {
    all(
        target_arch = "x86_64",
        target_feature = "avx512f",
        target_feature = "avx512bw",
        target_feature = "vpclmulqdq",
        target_feature = "gfni"
    ) => {
        pub use x86::SkipBlock;
    }
    _ => {
        /// [`skip_row`] over every row and slice of a block, a position at a time.
        pub struct SkipBlock {
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
            pub fn run(&mut self, block: &[u64], weights: &[[u64; 3]]) {
                self.acc.clear();
                for r in 0..5 {
                    for z in 0..64 {
                        let js = row_positions(r, z);
                        for x in 0..5 {
                            embed_extend(words(block, js[x]), &mut self.extended[x]);
                        }
                        skip_row(&mut self.acc, &self.extended, std::array::from_fn(|x| &weights[js[x]]));
                    }
                }
            }

            /// The three partial products of slot `i`.
            pub fn get(&self, i: usize) -> [u128; 3] {
                self.acc.get(i)
            }
        }
    }
}

/// Compiled only where its features are, so its kernels are safe to call.
#[cfg(all(
    target_arch = "x86_64",
    target_feature = "avx512f",
    target_feature = "avx512bw",
    target_feature = "vpclmulqdq",
    target_feature = "gfni"
))]
mod x86 {
    use core::arch::x86_64::*;

    use super::*;
    pub use super::{embed_extend_portable as embed_extend, skip_row_portable as skip_row};
    use crate::keccak::BITS;

    /// The matrices sending a pack's low and high byte to each byte of its embedding. An affine
    /// byte map reads output bit `t` off matrix byte `7 - t`.
    const MATRICES: [[i64; 3]; 2] = {
        let mut m = [[0i64; 3]; 2];
        let mut half = 0;
        while half < 2 {
            let mut k = 0;
            while k < 3 {
                let mut matrix = 0u64;
                let mut t = 0;
                while t < 8 {
                    let mut row = 0u64;
                    let mut i = 0;
                    while i < 8 {
                        row |= ((RMFE.emb[8 * half + i] >> (8 * k + t) & 1) as u64) << i;
                        i += 1;
                    }
                    matrix |= row << (8 * (7 - t));
                    t += 1;
                }
                m[half][k] = matrix as i64;
                k += 1;
            }
            half += 1;
        }
        m
    };

    #[inline(always)]
    pub fn embed(words: &[u64; BLOCK_WORDS]) -> [u32; PACKS] {
        unsafe {
            let m = &MATRICES;
            let v = _mm512_loadu_si512(words.as_ptr().cast());
            // Byte `k` of the embedding, in the low byte of each pack's 16 bits.
            let byte = |k: usize| {
                let lo = _mm512_gf2p8affine_epi64_epi8(v, _mm512_set1_epi64(m[0][k]), 0);
                let hi = _mm512_gf2p8affine_epi64_epi8(v, _mm512_set1_epi64(m[1][k]), 0);
                _mm512_and_si512(
                    _mm512_xor_si512(lo, _mm512_srli_epi16(hi, 8)),
                    _mm512_set1_epi16(0x00ff),
                )
            };
            let low = _mm512_or_si512(byte(0), _mm512_slli_epi16(byte(1), 8));
            let high = byte(2);
            // Interleaving the halves leaves each lane's four low packs, then its four high ones.
            let (first, second) = (_mm512_unpacklo_epi16(low, high), _mm512_unpackhi_epi16(low, high));
            let mut out = [0u32; PACKS];
            let order = |from: i64| {
                _mm512_setr_epi64(
                    from,
                    from + 1,
                    8 + from,
                    9 + from,
                    from + 2,
                    from + 3,
                    10 + from,
                    11 + from,
                )
            };
            _mm512_storeu_si512(
                out.as_mut_ptr().cast(),
                _mm512_permutex2var_epi64(first, order(0), second),
            );
            _mm512_storeu_si512(
                out.as_mut_ptr().add(16).cast(),
                _mm512_permutex2var_epi64(first, order(4), second),
            );
            out
        }
    }

    /// Eight packs, a word each.
    #[inline(always)]
    unsafe fn load(p: *const u32) -> __m512i {
        unsafe { _mm512_cvtepu32_epi64(_mm256_loadu_si256(p.cast())) }
    }

    #[inline(always)]
    pub fn products(a: &[u32; PACKS], b: &[u32; PACKS], c: &[u32; PACKS]) -> [u64; PACKS] {
        unsafe {
            let ones = _mm512_set1_epi64(RMFE.ones as i64);
            let mut out = [0u64; PACKS];
            for g in 0..4 {
                let (za, zb, zc) = (
                    load(a.as_ptr().add(8 * g)),
                    load(b.as_ptr().add(8 * g)),
                    load(c.as_ptr().add(8 * g)),
                );
                let linear = _mm512_xor_si512(za, zc);
                let even = _mm512_xor_si512(
                    _mm512_clmulepi64_epi128(zb, zc, 0x00),
                    _mm512_clmulepi64_epi128(linear, ones, 0x00),
                );
                let odd = _mm512_xor_si512(
                    _mm512_clmulepi64_epi128(zb, zc, 0x11),
                    _mm512_clmulepi64_epi128(linear, ones, 0x01),
                );
                _mm512_storeu_si512(out.as_mut_ptr().add(8 * g).cast(), _mm512_unpacklo_epi64(even, odd));
            }
            out
        }
    }

    /// Byte `k` of the embedding of each pack of `v`, in the low byte of the pack's 16 bits.
    #[inline(always)]
    unsafe fn embedding_byte(v: __m512i, k: usize) -> __m512i {
        unsafe {
            let lo = _mm512_gf2p8affine_epi64_epi8(v, _mm512_set1_epi64(MATRICES[0][k]), 0);
            let hi = _mm512_gf2p8affine_epi64_epi8(v, _mm512_set1_epi64(MATRICES[1][k]), 0);
            _mm512_and_si512(
                _mm512_xor_si512(lo, _mm512_srli_epi16(hi, 8)),
                _mm512_set1_epi16(0x00ff),
            )
        }
    }

    /// The packs of eight consecutive positions, embedded: `out[q]` holds pack `q` of position
    /// `i` in word `i`. The positions' words are transposed first, so a register holds one word
    /// of each, and a pack is then a field of every word alike.
    #[inline(always)]
    unsafe fn embed8(positions: *const u64, out: &mut [__m512i; PACKS]) {
        unsafe {
            let a: [__m512i; 8] = std::array::from_fn(|i| _mm512_loadu_si512(positions.add(BLOCK_WORDS * i).cast()));
            let b: [__m512i; 8] = std::array::from_fn(|i| {
                if i % 2 == 0 {
                    _mm512_unpacklo_epi64(a[i], a[i + 1])
                } else {
                    _mm512_unpackhi_epi64(a[i - 1], a[i])
                }
            });
            let (low, high) = (
                |x, y| _mm512_shuffle_i64x2::<0b10_00_10_00>(x, y),
                |x, y| _mm512_shuffle_i64x2::<0b11_01_11_01>(x, y),
            );
            // Words `t` and `t + 4` of positions `4m ..`, pairs of positions to a lane.
            let c: [__m512i; 8] = std::array::from_fn(|i| {
                let (m, t) = (i / 4, i % 4);
                let (x, y) = (b[4 * m + t % 2], b[4 * m + 2 + t % 2]);
                if t < 2 { low(x, y) } else { high(x, y) }
            });
            let words = [
                low(c[0], c[4]),
                low(c[1], c[5]),
                low(c[2], c[6]),
                low(c[3], c[7]),
                high(c[0], c[4]),
                high(c[1], c[5]),
                high(c[2], c[6]),
                high(c[3], c[7]),
            ];
            let zero = _mm512_setzero_si512();
            for (w, &v) in words.iter().enumerate() {
                let low = _mm512_or_si512(embedding_byte(v, 0), _mm512_slli_epi16(embedding_byte(v, 1), 8));
                let high = embedding_byte(v, 2);
                // Per lane, the four packs of its even word, then of its odd one.
                let (even, odd) = (_mm512_unpacklo_epi16(low, high), _mm512_unpackhi_epi16(low, high));
                let (first, second) = (_mm512_unpacklo_epi32(even, odd), _mm512_unpackhi_epi32(even, odd));
                out[4 * w] = _mm512_unpacklo_epi32(first, zero);
                out[4 * w + 1] = _mm512_unpackhi_epi32(first, zero);
                out[4 * w + 2] = _mm512_unpacklo_epi32(second, zero);
                out[4 * w + 3] = _mm512_unpackhi_epi32(second, zero);
            }
        }
    }

    /// [`extend_group`] on registers, each of eight positions' values.
    #[inline(always)]
    unsafe fn extend8(v: &[__m512i], out: &mut [__m512i; MIXED]) {
        unsafe {
            let x = |a: [__m512i; 4], b: [__m512i; 4]| -> [__m512i; 4] {
                std::array::from_fn(|l| _mm512_xor_si512(a[l], b[l]))
            };
            let q = |k: usize| -> [__m512i; 4] { std::array::from_fn(|l| v[4 * k + l]) };
            let (w4, w5) = (x(q(0), q(1)), x(q(2), q(3)));
            let w = [q(0), q(1), q(2), q(3), w4, w5, x(q(0), q(2)), x(q(1), q(3)), x(w4, w5)];
            for (k, w) in w[4..].iter().enumerate() {
                out[4 * k..][..4].copy_from_slice(w);
            }
            for (k, w) in w.iter().enumerate() {
                let low = x([w[0], w[2], w[0], w[1]], [w[1], w[3], w[2], w[3]]);
                out[20 + 4 * k..][..4].copy_from_slice(&low);
                out[56 + k] = _mm512_xor_si512(low[0], low[1]);
            }
        }
    }

    /// [`skip_row`] over every row and slice of a block, eight slices at a time: each register
    /// holds one value of eight positions, so the extension is a sum of registers and each slot's
    /// products are a register's lanes, weighted by eight positions' weights at once.
    pub struct SkipBlock {
        /// Per slot, the even and odd positions' sums of each partial product.
        acc: Vec<[__m512i; 6]>,
        packs: [[__m512i; PACKS]; 5],
        extended: [[__m512i; MIXED]; 5],
        /// The weights by word: word `k` of position `j` at `k * BITS + j`.
        weights: Vec<u64>,
    }

    impl SkipBlock {
        pub fn new() -> Box<Self> {
            let zero = unsafe { _mm512_setzero_si512() };
            Box::new(Self {
                acc: vec![[zero; 6]; 2 * MIXED],
                packs: [[zero; PACKS]; 5],
                extended: [[zero; MIXED]; 5],
                weights: vec![0; 3 * BITS],
            })
        }

        /// Sum a block, the position weights as elements.
        pub fn run(&mut self, block: &[u64], weights: &[[u64; 3]]) {
            assert!(block.len() >= BITS * BLOCK_WORDS && weights.len() >= BITS);
            for (j, w) in weights[..BITS].iter().enumerate() {
                for (k, &w) in w.iter().enumerate() {
                    self.weights[k * BITS + j] = w;
                }
            }
            // SAFETY: the features are enabled at compile time, and every position read is in
            // the block, every weight in the table.
            unsafe {
                self.acc.fill([_mm512_setzero_si512(); 6]);
                for r in 0..5 {
                    for z in (0..64).step_by(8) {
                        let js = row_positions(r, z);
                        for (packs, &j) in self.packs.iter_mut().zip(&js) {
                            embed8(block.as_ptr().add(BLOCK_WORDS * j), packs);
                        }
                        let w: [[__m512i; 3]; 5] = std::array::from_fn(|x| {
                            std::array::from_fn(|k| {
                                _mm512_loadu_si512(self.weights.as_ptr().add(k * BITS + js[x]).cast())
                            })
                        });
                        for half in 0..2 {
                            for (extended, packs) in self.extended.iter_mut().zip(&self.packs) {
                                extend8(&packs[GROUP * half..][..GROUP], extended);
                            }
                            for i in 0..MIXED {
                                let e: [__m512i; 5] = std::array::from_fn(|x| self.extended[x][i]);
                                let mut sums = [_mm512_setzero_si512(); 6];
                                for x in 0..5 {
                                    let (b, c) = (e[(x + 1) % 5], e[(x + 2) % 5]);
                                    let even = _mm512_clmulepi64_epi128(b, c, 0x00);
                                    let odd = _mm512_clmulepi64_epi128(b, c, 0x11);
                                    for k in 0..3 {
                                        let (s, w) = (&mut sums[2 * k..], w[x][k]);
                                        s[0] = _mm512_xor_si512(s[0], _mm512_clmulepi64_epi128(even, w, 0x00));
                                        s[1] = _mm512_xor_si512(s[1], _mm512_clmulepi64_epi128(odd, w, 0x10));
                                    }
                                }
                                let acc = &mut self.acc[slot(half, i)];
                                for (acc, sum) in acc.iter_mut().zip(sums) {
                                    *acc = _mm512_xor_si512(*acc, sum);
                                }
                            }
                        }
                    }
                }
            }
        }

        /// The three partial products of slot `i`.
        pub fn get(&self, i: usize) -> [u128; 3] {
            std::array::from_fn(|k| {
                let mut lanes = [[0u128; 4]; 2];
                for (lanes, &acc) in lanes.iter_mut().zip(&self.acc[i][2 * k..2 * k + 2]) {
                    // SAFETY: four 128-bit lanes to a register.
                    unsafe { _mm512_storeu_si512(lanes.as_mut_ptr().cast(), acc) };
                }
                lanes.as_flattened().iter().fold(0, |a, &b| a ^ b)
            })
        }
    }

    /// The six sums are summed across their lanes together: two registers' lanes interleave into
    /// one, which takes two shuffles where each register alone would leave the vector unit.
    #[inline(always)]
    pub fn fold_groups(e: &[u32; PACKS], weights: &[[u64; GROUP]; 3]) -> [[u128; 3]; 2] {
        unsafe {
            // `acc[3 * half + k]`, four lanes to sum.
            let mut acc = [_mm512_setzero_si512(); 6];
            for g in 0..PACKS / 8 {
                let ze = load(e.as_ptr().add(8 * g));
                for k in 0..3 {
                    let zw = _mm512_loadu_si512(weights[k].as_ptr().add(8 * (g % 2)).cast());
                    let sum = &mut acc[3 * (g / 2) + k];
                    *sum = _mm512_xor_si512(*sum, _mm512_clmulepi64_epi128(ze, zw, 0x00));
                    *sum = _mm512_xor_si512(*sum, _mm512_clmulepi64_epi128(ze, zw, 0x11));
                }
            }
            // Lanes `a0 + a2, a1 + a3, b0 + b2, b1 + b3`.
            let pair = |a: __m512i, b: __m512i| {
                _mm512_xor_si512(
                    _mm512_shuffle_i64x2::<0b01_00_01_00>(a, b),
                    _mm512_shuffle_i64x2::<0b11_10_11_10>(a, b),
                )
            };
            // Of two pairs, the four sums.
            let (t, u) = (pair(acc[0], acc[1]), pair(acc[2], acc[3]));
            let four = _mm512_xor_si512(
                _mm512_shuffle_i64x2::<0b10_00_10_00>(t, u),
                _mm512_shuffle_i64x2::<0b11_01_11_01>(t, u),
            );
            // Of the last pair, the two sums in lanes 0 and 2.
            let v = pair(acc[4], acc[5]);
            let two = _mm512_xor_si512(v, _mm512_shuffle_i64x2::<0b10_11_00_01>(v, v));
            let (mut a, mut b) = ([0u128; 4], [0u128; 4]);
            _mm512_storeu_si512(a.as_mut_ptr().cast(), four);
            _mm512_storeu_si512(b.as_mut_ptr().cast(), two);
            [[a[0], a[1], a[2]], [a[3], b[0], b[2]]]
        }
    }
}

/// Compiled only where its features are, so its kernels are safe to call. The embedding is
/// NEON's nibble lookups; the products are a register of [`Vector`](crate::clmul::Vector) lanes, two packs to a lane.
#[cfg(all(
    target_arch = "x86_64",
    target_feature = "avx2",
    target_feature = "pclmulqdq",
    not(target_feature = "avx512f")
))]
mod avx2 {
    use core::arch::x86_64::*;

    use super::*;
    use crate::clmul::{V, Vector};

    /// The 32 packs of a block position, embedded, four to a register.
    #[inline(always)]
    fn embed_vectors(words: &[u64; BLOCK_WORDS]) -> [__m128i; 8] {
        // SAFETY: the loads are of the tables and the eight words.
        unsafe {
            let t: [__m256i; 12] =
                std::array::from_fn(|i| _mm256_broadcastsi128_si256(_mm_loadu_si128(NIBBLES[i].as_ptr().cast())));
            let mask = _mm256_set1_epi8(0x0f);
            let (low_byte, high_byte) = (_mm256_set1_epi16(0x00ff), _mm256_set1_epi16(0xff00u16 as i16));
            let mut out = [_mm_setzero_si128(); 8];
            for half in 0..2 {
                let v = _mm256_loadu_si256(words.as_ptr().add(4 * half).cast());
                // A pack's low byte holds its nibbles 0 and 1, its high byte nibbles 2 and 3.
                let nibbles = [
                    _mm256_and_si256(v, mask),
                    _mm256_and_si256(_mm256_srli_epi16(v, 4), mask),
                ];
                // Byte `k` of the embedding of each byte, read as a pack's low byte or as its high one.
                let look = |k: usize, high: usize| {
                    _mm256_xor_si256(
                        _mm256_shuffle_epi8(t[4 * k + 2 * high], nibbles[0]),
                        _mm256_shuffle_epi8(t[4 * k + 2 * high + 1], nibbles[1]),
                    )
                };
                let low = _mm256_or_si256(
                    _mm256_and_si256(_mm256_xor_si256(look(0, 0), _mm256_srli_epi16(look(0, 1), 8)), low_byte),
                    _mm256_and_si256(
                        _mm256_xor_si256(_mm256_slli_epi16(look(1, 0), 8), look(1, 1)),
                        high_byte,
                    ),
                );
                let high = _mm256_and_si256(_mm256_xor_si256(look(2, 0), _mm256_srli_epi16(look(2, 1), 8)), low_byte);
                // Per lane, its four low packs, then its four high ones.
                let (first, second) = (_mm256_unpacklo_epi16(low, high), _mm256_unpackhi_epi16(low, high));
                out[4 * half] = _mm256_castsi256_si128(first);
                out[4 * half + 1] = _mm256_castsi256_si128(second);
                out[4 * half + 2] = _mm256_extracti128_si256::<1>(first);
                out[4 * half + 3] = _mm256_extracti128_si256::<1>(second);
            }
            out
        }
    }

    #[inline(always)]
    pub fn embed(words: &[u64; BLOCK_WORDS]) -> [u32; PACKS] {
        let mut out = [0u32; PACKS];
        for (i, v) in embed_vectors(words).into_iter().enumerate() {
            // SAFETY: four packs at `4 * i`.
            unsafe { _mm_storeu_si128(out.as_mut_ptr().add(4 * i).cast(), v) };
        }
        out
    }

    /// NEON's [`extend_group`] on the four vectors of a group: a vector's low mixed points are
    /// two shuffles, and its lane sum is returned for the last one, which [`embed_extend`] stores
    /// with the other group's.
    #[inline(always)]
    unsafe fn extend_vectors(v: &[__m128i], out: *mut u32) -> __m128i {
        unsafe {
            let (w4, w5) = (_mm_xor_si128(v[0], v[1]), _mm_xor_si128(v[2], v[3]));
            let w = [
                v[0],
                v[1],
                v[2],
                v[3],
                w4,
                w5,
                _mm_xor_si128(v[0], v[2]),
                _mm_xor_si128(v[1], v[3]),
                _mm_xor_si128(w4, w5),
            ];
            for (k, &w) in w[4..].iter().enumerate() {
                _mm_storeu_si128(out.add(4 * k).cast(), w);
            }
            // Lanes `0 + 1, 2 + 3, 0 + 2, 1 + 3`.
            let low: [__m128i; 9] = std::array::from_fn(|k| {
                _mm_xor_si128(
                    _mm_shuffle_epi32::<0b01_00_10_00>(w[k]),
                    _mm_shuffle_epi32::<0b11_10_11_01>(w[k]),
                )
            });
            for (k, &l) in low.iter().enumerate() {
                _mm_storeu_si128(out.add(20 + 4 * k).cast(), l);
            }
            // Lanes 0 and 1 of a vector's low mixed points add to its lane sum: two vectors at a time.
            let pair = |a: __m128i, b: __m128i| {
                let z = _mm_unpacklo_epi32(a, b);
                _mm_xor_si128(z, _mm_unpackhi_epi64(z, z))
            };
            for k in (0..8).step_by(4) {
                let (p, q) = (pair(low[k], low[k + 1]), pair(low[k + 2], low[k + 3]));
                _mm_storeu_si128(out.add(56 + k).cast(), _mm_unpacklo_epi64(p, q));
            }
            low[8]
        }
    }

    #[inline(always)]
    pub fn embed_extend(words: &[u64; BLOCK_WORDS], out: &mut [u32; SLOTS]) {
        let e = embed_vectors(words);
        // SAFETY: each group's outputs lie in `out`.
        unsafe {
            let last0 = extend_vectors(&e[..4], out.as_mut_ptr());
            let last1 = extend_vectors(&e[4..], out.as_mut_ptr().add(64));
            let z = _mm_unpacklo_epi32(last0, last1);
            _mm_storel_epi64(
                out.as_mut_ptr().add(128).cast(),
                _mm_xor_si128(z, _mm_unpackhi_epi64(z, z)),
            );
        }
    }

    #[inline(always)]
    pub fn products(a: &[u32; PACKS], b: &[u32; PACKS], c: &[u32; PACKS]) -> [u64; PACKS] {
        let ones = V::splat(RMFE.ones as u64);
        let mut out = [0u64; PACKS];
        for q in (0..PACKS).step_by(2 * V::N) {
            // SAFETY: `2 * N` packs at `q`, and as many words.
            unsafe {
                let (za, zb, zc) = (
                    V::load_packs(a.as_ptr().add(q)),
                    V::load_packs(b.as_ptr().add(q)),
                    V::load_packs(c.as_ptr().add(q)),
                );
                let linear = za.xor(zc);
                let even = zb.clmul::<0x00>(zc).xor(linear.clmul::<0x00>(ones));
                let odd = zb.clmul::<0x11>(zc).xor(linear.clmul::<0x11>(ones));
                V::store(out.as_mut_ptr().add(q), even.unpacklo(odd));
            }
        }
        out
    }

    /// `2 * N` slots at a time, their sums over the row kept in registers. A slot's product lies
    /// in the low word of its lane, which multiplies the weights as it is. The padding slots past
    /// the last whole register are skipped: nothing reads their sums.
    #[inline(always)]
    pub fn skip_row(acc: &mut SkipAcc, e: &[[u32; SLOTS]; 5], weights: [&[u64; 3]; 5]) {
        let w: [[V; 3]; 5] = std::array::from_fn(|x| std::array::from_fn(|k| V::splat(weights[x][k])));
        for p in (0..2 * MIXED).step_by(2 * V::N) {
            // SAFETY: `p + 2 * N` is at most `SLOTS`.
            let z: [V; 5] = std::array::from_fn(|x| unsafe { V::load_packs(e[x].as_ptr().add(p)) });
            let mut sums = [[V::zero(); 2]; 3];
            for x in 0..5 {
                let (zb, zc) = (z[(x + 1) % 5], z[(x + 2) % 5]);
                let products = [zb.clmul::<0x00>(zc), zb.clmul::<0x11>(zc)];
                for (k, sums) in sums.iter_mut().enumerate() {
                    for (sum, product) in sums.iter_mut().zip(products) {
                        *sum = sum.xor(product.clmul::<0x00>(w[x][k]));
                    }
                }
            }
            // Slot `p + h + 2 * l` is lane `l` of `sums[.][h]`, and those lanes lie side by side.
            for (acc, sums) in acc.0.iter_mut().zip(sums) {
                for (h, sum) in sums.into_iter().enumerate() {
                    let slot = acc[2 * (p / 8) + h].0[(p % 8) / 2..].as_mut_ptr().cast::<u64>();
                    // SAFETY: `N` lanes from `(p % 8) / 2`, a multiple of `N`.
                    unsafe { V::store(slot, V::load(slot).xor(sum)) };
                }
            }
        }
    }

    #[inline(always)]
    pub fn fold_groups(e: &[u32; PACKS], weights: &[[u64; GROUP]; 3]) -> [[u128; 3]; 2] {
        std::array::from_fn(|half| {
            let mut acc = [V::zero(); 3];
            for q in (0..GROUP).step_by(2 * V::N) {
                // SAFETY: `2 * N` packs and weights at `q`.
                unsafe {
                    let ze = V::load_packs(e.as_ptr().add(GROUP * half + q));
                    for (acc, weights) in acc.iter_mut().zip(weights) {
                        let zw = V::load(weights.as_ptr().add(q));
                        *acc = acc.xor(ze.clmul::<0x00>(zw)).xor(ze.clmul::<0x11>(zw));
                    }
                }
            }
            acc.map(V::sum)
        })
    }
}

/// Compiled only where its feature is, so its kernels are safe to call.
#[cfg(all(target_arch = "aarch64", target_feature = "aes"))]
mod neon {
    use core::arch::aarch64::*;
    use core::mem::transmute;

    use primitives::field::gf2_64::aarch64::{
        pmull, pmull_hi as mul_hi_scheduled, pmull_hi_asm as mul_hi, pmull_lo_asm as mul_lo,
    };

    use super::*;

    /// A linear map is the sum of its nibbles' images, so each byte of sixteen embeddings is four
    /// table lookups.
    #[inline(always)]
    pub fn embed(words: &[u64; BLOCK_WORDS]) -> [u32; PACKS] {
        unsafe {
            let p = NIBBLES.as_ptr().cast::<u8>();
            let t = [
                vld1q_u8(p),
                vld1q_u8(p.add(16)),
                vld1q_u8(p.add(32)),
                vld1q_u8(p.add(48)),
                vld1q_u8(p.add(64)),
                vld1q_u8(p.add(80)),
                vld1q_u8(p.add(96)),
                vld1q_u8(p.add(112)),
                vld1q_u8(p.add(128)),
                vld1q_u8(p.add(144)),
                vld1q_u8(p.add(160)),
                vld1q_u8(p.add(176)),
            ];
            let mask = vdupq_n_u8(0x0f);
            let mut out = [0u32; PACKS];
            for half in 0..2 {
                // Pack `q` is bytes `2q` and `2q + 1`: the low bytes and the high bytes of sixteen.
                let bytes = vld2q_u8(words.as_ptr().cast::<u8>().add(32 * half));
                let nibbles = [
                    vandq_u8(bytes.0, mask),
                    vshrq_n_u8(bytes.0, 4),
                    vandq_u8(bytes.1, mask),
                    vshrq_n_u8(bytes.1, 4),
                ];
                let byte = |k: usize| {
                    let look = |n: usize| vqtbl1q_u8(t[4 * k + n], nibbles[n]);
                    veorq_u8(veorq_u8(look(0), look(1)), veorq_u8(look(2), look(3)))
                };
                let (b0, b1, b2) = (byte(0), byte(1), byte(2));
                let zero = vdupq_n_u8(0);
                let (lo, hi) = (vzip1q_u8(b0, b1), vzip2q_u8(b0, b1));
                let (top_lo, top_hi) = (vzip1q_u8(b2, zero), vzip2q_u8(b2, zero));
                let dst = out.as_mut_ptr().add(16 * half);
                for (i, (l, h)) in [(lo, top_lo), (hi, top_hi)].into_iter().enumerate() {
                    let (l, h) = (vreinterpretq_u16_u8(l), vreinterpretq_u16_u8(h));
                    vst1q_u32(dst.add(8 * i), vreinterpretq_u32_u16(vzip1q_u16(l, h)));
                    vst1q_u32(dst.add(8 * i + 4), vreinterpretq_u32_u16(vzip2q_u16(l, h)));
                }
            }
            out
        }
    }

    /// Two packs, a lane each.
    #[inline(always)]
    unsafe fn load(p: *const u32) -> uint64x2_t {
        unsafe { vmovl_u32(vld1_u32(p)) }
    }

    /// [`extend_group`] on the four vectors of a group, the values staying in registers: a
    /// vector's low mixed points are two table lookups, and its lane sum is returned for the last
    /// one, which [`embed_extend`] stores with the other group's.
    #[inline(always)]
    unsafe fn extend_vectors(v: [uint32x4_t; 4], out: *mut u32) -> uint32x4_t {
        const FIRST: [u8; 16] = [0, 1, 2, 3, 8, 9, 10, 11, 0, 1, 2, 3, 4, 5, 6, 7];
        const SECOND: [u8; 16] = [4, 5, 6, 7, 12, 13, 14, 15, 8, 9, 10, 11, 12, 13, 14, 15];
        unsafe {
            let (first, second) = (vld1q_u8(FIRST.as_ptr()), vld1q_u8(SECOND.as_ptr()));
            let (w4, w5) = (veorq_u32(v[0], v[1]), veorq_u32(v[2], v[3]));
            let w = [
                v[0],
                v[1],
                v[2],
                v[3],
                w4,
                w5,
                veorq_u32(v[0], v[2]),
                veorq_u32(v[1], v[3]),
                veorq_u32(w4, w5),
            ];
            for (k, &w) in w[4..].iter().enumerate() {
                vst1q_u32(out.add(4 * k), w);
            }
            let low: [uint32x4_t; 9] = std::array::from_fn(|k| {
                let b = vreinterpretq_u8_u32(w[k]);
                vreinterpretq_u32_u8(veorq_u8(vqtbl1q_u8(b, first), vqtbl1q_u8(b, second)))
            });
            for (k, &l) in low.iter().enumerate() {
                vst1q_u32(out.add(20 + 4 * k), l);
            }
            // Lanes 0 and 1 of a vector's low mixed points add to its lane sum: two vectors at a time.
            let pair = |a: uint32x4_t, b: uint32x4_t| {
                let z = vzip1q_u32(a, b);
                veorq_u32(z, vextq_u32::<2>(z, z))
            };
            for k in (0..8).step_by(4) {
                let (p, q) = (pair(low[k], low[k + 1]), pair(low[k + 2], low[k + 3]));
                vst1q_u32(
                    out.add(56 + k),
                    vreinterpretq_u32_u64(vzip1q_u64(vreinterpretq_u64_u32(p), vreinterpretq_u64_u32(q))),
                );
            }
            low[8]
        }
    }

    #[inline(always)]
    pub fn embed_extend(words: &[u64; BLOCK_WORDS], out: &mut [u32; SLOTS]) {
        unsafe {
            let e = embed(words);
            let v = |half: usize| -> [uint32x4_t; 4] {
                std::array::from_fn(|k| vld1q_u32(e.as_ptr().add(16 * half + 4 * k)))
            };
            let last0 = extend_vectors(v(0), out.as_mut_ptr());
            let last1 = extend_vectors(v(1), out.as_mut_ptr().add(64));
            let z = vzip1q_u32(last0, last1);
            vst1_u32(
                out.as_mut_ptr().add(128),
                vget_low_u32(veorq_u32(z, vextq_u32::<2>(z, z))),
            );
        }
    }

    /// The low lanes' product through the intrinsics, as [`mul_hi_scheduled`] is, for [`skip_row`]:
    /// its products are the bound there, and the compiler schedules them better around the rest of
    /// the loop than written-out ones.
    #[inline(always)]
    unsafe fn mul_lo_scheduled(a: uint64x2_t, b: uint64x2_t) -> uint64x2_t {
        unsafe { pmull(vgetq_lane_u64(a, 0), vgetq_lane_u64(b, 0)) }
    }

    #[inline(always)]
    pub fn products(a: &[u32; PACKS], b: &[u32; PACKS], c: &[u32; PACKS]) -> [u64; PACKS] {
        unsafe {
            let ones = vdupq_n_u64(RMFE.ones as u64);
            let mut out = [0u64; PACKS];
            for q in (0..PACKS).step_by(2) {
                let (za, zb, zc) = (
                    load(a.as_ptr().add(q)),
                    load(b.as_ptr().add(q)),
                    load(c.as_ptr().add(q)),
                );
                let linear = veorq_u64(za, zc);
                let even = veorq_u64(mul_lo(zb, zc), mul_lo(linear, ones));
                let odd = veorq_u64(mul_hi(zb, zc), mul_hi(linear, ones));
                vst1q_u64(out.as_mut_ptr().add(q), vzip1q_u64(even, odd));
            }
            out
        }
    }

    /// Two slots at a time, their sums over the row kept in registers. The padding slots are
    /// skipped: [`extend`] never writes them, and nothing reads their sums.
    #[inline(always)]
    pub fn skip_row(acc: &mut SkipAcc, e: &[[u32; SLOTS]; 5], weights: [&[u64; 3]; 5]) {
        unsafe {
            let w: [[uint64x2_t; 3]; 5] = std::array::from_fn(|x| std::array::from_fn(|k| vdupq_n_u64(weights[x][k])));
            for p in (0..2 * MIXED).step_by(2) {
                let z: [uint64x2_t; 5] = std::array::from_fn(|x| load(e[x].as_ptr().add(p)));
                let mut sums = [[vdupq_n_u64(0); 2]; 3];
                for x in 0..5 {
                    let (zb, zc) = (z[(x + 1) % 5], z[(x + 2) % 5]);
                    let pair = vzip1q_u64(mul_lo_scheduled(zb, zc), mul_hi_scheduled(zb, zc));
                    for k in 0..3 {
                        sums[k][0] = veorq_u64(sums[k][0], mul_lo_scheduled(pair, w[x][k]));
                        sums[k][1] = veorq_u64(sums[k][1], mul_hi_scheduled(pair, w[x][k]));
                    }
                }
                for (k, sums) in sums.iter().enumerate() {
                    for (h, &sum) in sums.iter().enumerate() {
                        let i = p + h;
                        let slot = (&mut acc.0[k][2 * (i / 8) + i % 2].0[(i % 8) / 2] as *mut u128).cast::<u64>();
                        vst1q_u64(slot, veorq_u64(vld1q_u64(slot), sum));
                    }
                }
            }
        }
    }

    #[inline(always)]
    pub fn fold_groups(e: &[u32; PACKS], weights: &[[u64; GROUP]; 3]) -> [[u128; 3]; 2] {
        unsafe {
            std::array::from_fn(|half| {
                std::array::from_fn(|k| {
                    let mut acc = vdupq_n_u64(0);
                    for q in (0..GROUP).step_by(2) {
                        let (ze, zw) = (
                            load(e.as_ptr().add(GROUP * half + q)),
                            vld1q_u64(weights[k].as_ptr().add(q)),
                        );
                        acc = veorq_u64(acc, veorq_u64(mul_lo(ze, zw), mul_hi(ze, zw)));
                    }
                    transmute::<uint64x2_t, u128>(acc)
                })
            })
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::keccak::BITS;
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

    #[test]
    fn vector_kernels_match_the_portable_ones() {
        let mut rng = Rng::new(32);
        for _ in 0..20 {
            let words: [u64; BLOCK_WORDS] = std::array::from_fn(|_| rng.next_u64());
            let e = embed(&words);
            assert_eq!(e, embed_portable(&words));
            let (b, c) = (
                embed(&std::array::from_fn(|_| rng.next_u64())),
                embed(&std::array::from_fn(|_| rng.next_u64())),
            );
            assert_eq!(products(&e, &b, &c), products_portable(&e, &b, &c));

            let (mut xe, mut xp) = ([0u32; SLOTS], [0u32; SLOTS]);
            embed_extend(&words, &mut xe);
            extend(&embed_portable(&words), &mut xp);
            assert_eq!(xe[..2 * MIXED], xp[..2 * MIXED]);
            let (mut xb, mut xc) = ([0u32; SLOTS], [0u32; SLOTS]);
            extend(&b, &mut xb);
            extend(&c, &mut xc);
            let (mut fast, mut slow) = (SkipAcc::new(), SkipAcc::new());
            let row = [xb, xc, xb, xc, xb];
            let weights: [[u64; 3]; 2] = std::array::from_fn(|_| std::array::from_fn(|_| rng.next_u64()));
            let row_weights = [&weights[0], &weights[1], &weights[0], &weights[1], &weights[0]];
            for _ in 0..2 {
                skip_row(&mut fast, &row, row_weights);
                skip_row_portable(&mut slow, &row, row_weights);
            }
            for slot in 0..SLOTS {
                assert_eq!(fast.get(slot), slow.get(slot));
            }
            let fold: [[u64; GROUP]; 3] = std::array::from_fn(|_| std::array::from_fn(|_| rng.next_u64()));
            assert_eq!(fold_groups(&e, &fold), fold_groups_portable(&e, &fold));
        }
        let block: Vec<u64> = (0..crate::witness::BLOCK_LEN).map(|_| rng.next_u64()).collect();
        let weights: Vec<[u64; 3]> = (0..BITS).map(|_| std::array::from_fn(|_| rng.next_u64())).collect();
        let mut skip = SkipBlock::new();
        skip.run(&block, &weights);
        let expected = skip_block_portable(&block, &weights);
        for (i, expected) in expected.iter().enumerate() {
            assert_eq!(&skip.get(i), expected, "slot {i}");
        }
    }
}
