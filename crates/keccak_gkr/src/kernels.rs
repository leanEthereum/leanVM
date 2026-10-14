//! The bit-level kernels of the layer prover, over one block position at a time: the 32 packs of
//! one bit position of one block.
//!
//! Each has a portable form, an AVX-512 one (AVX-512BW, VPCLMULQDQ, GFNI) and a NEON one (PMULL),
//! which agree bit for bit. The vector forms are compiled only where their features are.

use primitives::field::gf2_64::mul_wide;

use crate::rmfe::RMFE;
use crate::witness::BLOCK_WORDS;

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

/// Extend one group's values on the binary cube to the mixed points of `{0, 1, infinity}^SKIP`:
/// along each variable, the value at infinity is the sum of the two others.
///
/// The binary points are the values themselves, so only the mixed ones are written. They are
/// built a variable at a time: the mixed points of `k` variables are those of the lower half,
/// those of the upper half, then the last variable at infinity over the binary points and over
/// the mixed ones. [`mixed_points`] names each output by its ternary digits.
#[inline(always)]
pub fn extend_group(v: &[u32; GROUP], out: &mut [u32]) {
    let out: &mut [u32; MIXED] = (&mut out[..MIXED]).try_into().expect("65 mixed points");
    // Two variables: the five mixed points of four values.
    #[inline(always)]
    fn quad(v: &[u32], out: &mut [u32]) {
        out[0] = v[0] ^ v[1];
        out[1] = v[2] ^ v[3];
        out[2] = v[0] ^ v[2];
        out[3] = v[1] ^ v[3];
        out[4] = out[0] ^ out[1];
    }
    // Three variables: nineteen, from two runs of four values.
    for half in 0..2 {
        let (v, at) = (&v[8 * half..][..8], 19 * half);
        quad(&v[..4], &mut out[at..]);
        quad(&v[4..], &mut out[at + 5..]);
        for i in 0..4 {
            out[at + 10 + i] = v[i] ^ v[4 + i];
        }
        for i in 0..5 {
            out[at + 14 + i] = out[at + i] ^ out[at + 5 + i];
        }
    }
    for i in 0..8 {
        out[38 + i] = v[i] ^ v[8 + i];
    }
    for i in 0..19 {
        out[46 + i] = out[i] ^ out[19 + i];
    }
}

/// The ternary index of each output of [`extend_group`]: variable `k`'s point is its `k`-th
/// digit, with infinity as 2.
pub fn mixed_points() -> [usize; MIXED] {
    // The ternary index of a binary assignment.
    let binary = |i: usize, k: usize| (0..k).fold(0, |acc, d| acc + (i >> d & 1) * 3usize.pow(d as u32));
    let mut points = vec![2usize];
    for k in 1..SKIP {
        let top = 3usize.pow(k as u32);
        let mut next: Vec<usize> = points.clone();
        next.extend(points.iter().map(|p| p + top));
        next.extend((0..1 << k).map(|i| binary(i, k) + 2 * top));
        next.extend(points.iter().map(|p| p + 2 * top));
        points = next;
    }
    points.try_into().expect("65 mixed points")
}

/// Both groups of a block position: group `h`'s mixed points fill slots `65 * h ..`.
#[inline(always)]
pub fn extend(packs: &[u32; PACKS], out: &mut [u32; SLOTS]) {
    let (lo, hi) = packs.split_at(GROUP);
    extend_group(lo.try_into().unwrap(), &mut out[..MIXED]);
    extend_group(hi.try_into().unwrap(), &mut out[MIXED..2 * MIXED]);
}

/// The 32 packs of a block position, embedded.
#[inline(always)]
pub fn embed(words: &[u64; BLOCK_WORDS]) -> [u32; PACKS] {
    #[cfg(all(
        target_arch = "x86_64",
        target_feature = "avx512f",
        target_feature = "avx512bw",
        target_feature = "vpclmulqdq",
        target_feature = "gfni"
    ))]
    // SAFETY: the features are enabled at compile time.
    unsafe {
        x86::embed(words)
    }
    #[cfg(all(target_arch = "aarch64", target_feature = "aes"))]
    // SAFETY: the feature is enabled at compile time.
    unsafe {
        neon::embed(words)
    }
    #[cfg(not(any(
        all(
            target_arch = "x86_64",
            target_feature = "avx512f",
            target_feature = "avx512bw",
            target_feature = "vpclmulqdq",
            target_feature = "gfni"
        ),
        all(target_arch = "aarch64", target_feature = "aes")
    )))]
    embed_portable(words)
}

pub fn embed_portable(words: &[u64; BLOCK_WORDS]) -> [u32; PACKS] {
    std::array::from_fn(|q| RMFE.embed((words[q / 4] >> (16 * (q % 4))) as u16))
}

/// The unprojected `chi` of 32 packs: `ones * (a + c) + b * c`.
#[inline(always)]
pub fn products(a: &[u32; PACKS], b: &[u32; PACKS], c: &[u32; PACKS]) -> [u64; PACKS] {
    #[cfg(all(
        target_arch = "x86_64",
        target_feature = "avx512f",
        target_feature = "avx512bw",
        target_feature = "vpclmulqdq",
        target_feature = "gfni"
    ))]
    // SAFETY: the features are enabled at compile time.
    unsafe {
        x86::products(a, b, c)
    }
    #[cfg(all(target_arch = "aarch64", target_feature = "aes"))]
    // SAFETY: the feature is enabled at compile time.
    unsafe {
        neon::products(a, b, c)
    }
    #[cfg(not(any(
        all(
            target_arch = "x86_64",
            target_feature = "avx512f",
            target_feature = "avx512bw",
            target_feature = "vpclmulqdq",
            target_feature = "gfni"
        ),
        all(target_arch = "aarch64", target_feature = "aes")
    )))]
    products_portable(a, b, c)
}

pub fn products_portable(a: &[u32; PACKS], b: &[u32; PACKS], c: &[u32; PACKS]) -> [u64; PACKS] {
    let ones = RMFE.ones as u64;
    std::array::from_fn(|q| (mul_wide(ones, (a[q] ^ c[q]) as u64) ^ mul_wide(b[q] as u64, c[q] as u64)) as u64)
}

/// One row of five positions, which `chi` mixes cyclically: for every pattern,
/// `acc[p] += sum over x of weights[x] * e[x + 1][p] * e[x + 2][p]`.
#[inline(always)]
pub fn skip_row(acc: &mut SkipAcc, e: &[[u32; SLOTS]; 5], weights: [&[u64; 3]; 5]) {
    #[cfg(all(
        target_arch = "x86_64",
        target_feature = "avx512f",
        target_feature = "avx512bw",
        target_feature = "vpclmulqdq",
        target_feature = "gfni"
    ))]
    // SAFETY: the features are enabled at compile time.
    unsafe {
        x86::skip_row(acc, e, weights)
    }
    #[cfg(all(target_arch = "aarch64", target_feature = "aes"))]
    // SAFETY: the feature is enabled at compile time.
    unsafe {
        neon::skip_row(acc, e, weights)
    }
    #[cfg(not(any(
        all(
            target_arch = "x86_64",
            target_feature = "avx512f",
            target_feature = "avx512bw",
            target_feature = "vpclmulqdq",
            target_feature = "gfni"
        ),
        all(target_arch = "aarch64", target_feature = "aes")
    )))]
    skip_row_portable(acc, e, weights)
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
    #[cfg(all(
        target_arch = "x86_64",
        target_feature = "avx512f",
        target_feature = "avx512bw",
        target_feature = "vpclmulqdq",
        target_feature = "gfni"
    ))]
    // SAFETY: the features are enabled at compile time.
    unsafe {
        x86::fold_group(e, weights)
    }
    #[cfg(all(target_arch = "aarch64", target_feature = "aes"))]
    // SAFETY: the feature is enabled at compile time.
    unsafe {
        neon::fold_group(e, weights)
    }
    #[cfg(not(any(
        all(
            target_arch = "x86_64",
            target_feature = "avx512f",
            target_feature = "avx512bw",
            target_feature = "vpclmulqdq",
            target_feature = "gfni"
        ),
        all(target_arch = "aarch64", target_feature = "aes")
    )))]
    fold_group_portable(e, weights)
}

pub fn fold_group_portable(e: &[u32; GROUP], weights: &[[u64; GROUP]; 3]) -> [u128; 3] {
    std::array::from_fn(|k| (0..GROUP).fold(0, |acc, q| acc ^ mul_wide(e[q] as u64, weights[k][q])))
}

#[cfg(all(
    target_arch = "x86_64",
    target_feature = "avx512f",
    target_feature = "avx512bw",
    target_feature = "vpclmulqdq",
    target_feature = "gfni"
))]
mod x86 {
    use core::arch::x86_64::*;
    use std::sync::LazyLock;

    use super::*;

    /// The matrices sending a pack's low and high byte to each byte of its embedding. An affine
    /// byte map reads output bit `t` off matrix byte `7 - t`.
    static MATRICES: LazyLock<[[i64; 3]; 2]> = LazyLock::new(|| {
        std::array::from_fn(|half| {
            std::array::from_fn(|k| {
                let mut matrix = 0u64;
                for t in 0..8 {
                    let row = (0..8).fold(0u64, |row, i| {
                        row | ((RMFE.emb[8 * half + i] >> (8 * k + t) & 1) as u64) << i
                    });
                    matrix |= row << (8 * (7 - t));
                }
                matrix as i64
            })
        })
    });

    #[inline(always)]
    pub unsafe fn embed(words: &[u64; BLOCK_WORDS]) -> [u32; PACKS] {
        unsafe {
            let m = &*MATRICES;
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
    pub unsafe fn products(a: &[u32; PACKS], b: &[u32; PACKS], c: &[u32; PACKS]) -> [u64; PACKS] {
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
    pub unsafe fn skip_row(acc: &mut SkipAcc, e: &[[u32; SLOTS]; 5], weights: [&[u64; 3]; 5]) {
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
    pub unsafe fn fold_group(e: &[u32; GROUP], weights: &[[u64; GROUP]; 3]) -> [u128; 3] {
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

#[cfg(all(target_arch = "aarch64", target_feature = "aes"))]
mod neon {
    use core::arch::aarch64::*;
    use core::mem::transmute;
    use std::sync::LazyLock;

    use super::*;

    /// Byte `k` of the embedding of each nibble of a pack: table `4 * k + n` is nibble `n`, low
    /// first.
    static NIBBLES: LazyLock<[[u8; 16]; 12]> = LazyLock::new(|| {
        std::array::from_fn(|i| {
            let (k, n) = (i / 4, i % 4);
            std::array::from_fn(|v| {
                let e = (0..4)
                    .filter(|t| v >> t & 1 == 1)
                    .fold(0, |e, t| e ^ RMFE.emb[4 * n + t]);
                (e >> (8 * k)) as u8
            })
        })
    });

    /// A linear map is the sum of its nibbles' images, so each byte of sixteen embeddings is four
    /// table lookups.
    #[inline(always)]
    pub unsafe fn embed(words: &[u64; BLOCK_WORDS]) -> [u32; PACKS] {
        unsafe {
            let t: [uint8x16_t; 12] = std::array::from_fn(|i| vld1q_u8(NIBBLES[i].as_ptr()));
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

    /// The product of the low lanes, and of the high lanes.
    #[inline(always)]
    unsafe fn mul_lo(a: uint64x2_t, b: uint64x2_t) -> uint64x2_t {
        unsafe { transmute::<u128, uint64x2_t>(vmull_p64(vgetq_lane_u64(a, 0), vgetq_lane_u64(b, 0))) }
    }

    #[inline(always)]
    unsafe fn mul_hi(a: uint64x2_t, b: uint64x2_t) -> uint64x2_t {
        unsafe { transmute::<u128, uint64x2_t>(vmull_high_p64(vreinterpretq_p64_u64(a), vreinterpretq_p64_u64(b))) }
    }

    #[inline(always)]
    pub unsafe fn products(a: &[u32; PACKS], b: &[u32; PACKS], c: &[u32; PACKS]) -> [u64; PACKS] {
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

    /// Two slots at a time, their sums over the row kept in registers.
    #[inline(always)]
    pub unsafe fn skip_row(acc: &mut SkipAcc, e: &[[u32; SLOTS]; 5], weights: [&[u64; 3]; 5]) {
        unsafe {
            let w: [[uint64x2_t; 3]; 5] = std::array::from_fn(|x| std::array::from_fn(|k| vdupq_n_u64(weights[x][k])));
            for p in (0..SLOTS).step_by(2) {
                let z: [uint64x2_t; 5] = std::array::from_fn(|x| load(e[x].as_ptr().add(p)));
                let mut sums = [[vdupq_n_u64(0); 2]; 3];
                for x in 0..5 {
                    let (zb, zc) = (z[(x + 1) % 5], z[(x + 2) % 5]);
                    let pair = vzip1q_u64(mul_lo(zb, zc), mul_hi(zb, zc));
                    for k in 0..3 {
                        sums[k][0] = veorq_u64(sums[k][0], mul_lo(pair, w[x][k]));
                        sums[k][1] = veorq_u64(sums[k][1], mul_hi(pair, w[x][k]));
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
    pub unsafe fn fold_group(e: &[u32; GROUP], weights: &[[u64; GROUP]; 3]) -> [u128; 3] {
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
        let mut out = [0u32; MIXED];
        extend_group(&v, &mut out);
        let points = mixed_points();
        let mut seen = [false; TERNARY];
        for (slot, &p) in points.iter().enumerate() {
            // A digit at infinity sums both points of its variable.
            let digits: [usize; SKIP] = std::array::from_fn(|k| p / 3usize.pow(k as u32) % 3);
            assert!(digits.contains(&2) && !seen[p]);
            seen[p] = true;
            let expected = (0..GROUP)
                .filter(|q| (0..SKIP).all(|k| digits[k] == 2 || digits[k] == q >> k & 1))
                .fold(0, |acc, q| acc ^ v[q]);
            assert_eq!(out[slot], expected, "slot {slot}");
        }
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
