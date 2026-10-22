//! The bit-level kernels of the layer prover, over one block position at a time: the 32 packs of
//! one bit position of one block.
//!
//! Each has a portable form, an AVX-512 one (AVX-512BW, VPCLMULQDQ, GFNI) and a NEON one (PMULL),
//! which agree bit for bit. The vector forms are compiled only where their features are.

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
    all(target_arch = "aarch64", target_feature = "aes") => {
        use neon as simd;
    }
    _ => {
        mod simd {
            pub use super::{
                embed_extend_portable as embed_extend, embed_portable as embed, fold_group_portable as fold_group,
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

/// `sum over a group's packs of weights[.][q] * e[q]`, as three partial products.
#[inline(always)]
pub fn fold_group(e: &[u32; GROUP], weights: &[[u64; GROUP]; 3]) -> [u128; 3] {
    simd::fold_group(e, weights)
}

pub fn fold_group_portable(e: &[u32; GROUP], weights: &[[u64; GROUP]; 3]) -> [u128; 3] {
    std::array::from_fn(|k| (0..GROUP).fold(0, |acc, q| acc ^ mul_wide(e[q] as u64, weights[k][q])))
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

    pub use super::embed_extend_portable as embed_extend;
    use super::*;

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

    #[inline(always)]
    unsafe fn add(slot: &mut Lanes, x: __m512i) {
        unsafe {
            let p = (slot as *mut Lanes).cast();
            _mm512_store_si512(p, _mm512_xor_si512(_mm512_load_si512(p), x));
        }
    }

    /// The accumulators of a run of patterns stay in registers across the row.
    #[inline(always)]
    pub fn skip_row(acc: &mut SkipAcc, e: &[[u32; SLOTS]; 5], weights: [&[u64; 3]; 5]) {
        unsafe {
            let w: [[__m512i; 3]; 5] =
                std::array::from_fn(|x| std::array::from_fn(|k| _mm512_set1_epi64(weights[x][k] as i64)));
            for g in 0..SLOTS / 8 {
                let z: [__m512i; 5] = std::array::from_fn(|x| load(e[x].as_ptr().add(8 * g)));
                let mut sums = [[_mm512_setzero_si512(); 2]; 3];
                for x in 0..5 {
                    let (zb, zc) = (z[(x + 1) % 5], z[(x + 2) % 5]);
                    let even = _mm512_clmulepi64_epi128(zb, zc, 0x00);
                    let odd = _mm512_clmulepi64_epi128(zb, zc, 0x11);
                    for k in 0..3 {
                        sums[k][0] = _mm512_xor_si512(sums[k][0], _mm512_clmulepi64_epi128(even, w[x][k], 0x00));
                        sums[k][1] = _mm512_xor_si512(sums[k][1], _mm512_clmulepi64_epi128(odd, w[x][k], 0x00));
                    }
                }
                for k in 0..3 {
                    add(&mut acc.0[k][2 * g], sums[k][0]);
                    add(&mut acc.0[k][2 * g + 1], sums[k][1]);
                }
            }
        }
    }

    #[inline(always)]
    pub fn fold_group(e: &[u32; GROUP], weights: &[[u64; GROUP]; 3]) -> [u128; 3] {
        unsafe {
            let mut out = [0u128; 3];
            for k in 0..3 {
                let mut acc = _mm512_setzero_si512();
                for g in 0..GROUP / 8 {
                    let ze = load(e.as_ptr().add(8 * g));
                    let zw = _mm512_loadu_si512(weights[k].as_ptr().add(8 * g).cast());
                    acc = _mm512_xor_si512(acc, _mm512_clmulepi64_epi128(ze, zw, 0x00));
                    acc = _mm512_xor_si512(acc, _mm512_clmulepi64_epi128(ze, zw, 0x11));
                }
                let mut lanes = [0u128; 4];
                _mm512_storeu_si512(lanes.as_mut_ptr().cast(), acc);
                out[k] = lanes[0] ^ lanes[1] ^ lanes[2] ^ lanes[3];
            }
            out
        }
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

    /// Byte `k` of the embedding of each nibble of a pack: table `4 * k + n` is nibble `n`, low
    /// first.
    static NIBBLES: [[u8; 16]; 12] = {
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
    pub fn fold_group(e: &[u32; GROUP], weights: &[[u64; GROUP]; 3]) -> [u128; 3] {
        unsafe {
            std::array::from_fn(|k| {
                let mut acc = vdupq_n_u64(0);
                for q in (0..GROUP).step_by(2) {
                    let (ze, zw) = (load(e.as_ptr().add(q)), vld1q_u64(weights[k].as_ptr().add(q)));
                    acc = veorq_u64(acc, veorq_u64(mul_lo(ze, zw), mul_hi(ze, zw)));
                }
                transmute::<uint64x2_t, u128>(acc)
            })
        }
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
            let group: &[u32; GROUP] = e[..GROUP].try_into().unwrap();
            assert_eq!(fold_group(group, &fold), fold_group_portable(group, &fold));
        }
    }
}
