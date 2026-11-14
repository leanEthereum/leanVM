//! The lanes in vector registers, with VPCLMULQDQ: four elements to a ZMM register with AVX-512, two to a YMM
//! register with AVX2. An element keeps its memory layout, `[c0, c1]` in one 128-bit lane, so loads and stores are
//! plain moves, and every product and reduction stays inside its 128-bit lane: only the mixed product's spread of
//! the `K` operand and [`clmul8`]'s interleave cross lanes.
//!
//! The kernels below are written once over the register type `V` and the few width-specific moves in `v`.

use crate::field::gf2_64::reduce;
use crate::field::{F64, F128};

/// 128-bit lanes in a register.
const W: usize = size_of::<V>() / 16;
/// Registers in eight `E` elements, or eight 128-bit products.
const R: usize = 8 / W;
/// Registers in eight `K` elements.
const Q: usize = R / 2;

/// Eight `K` elements, in memory order.
#[derive(Clone, Copy, Debug)]
pub struct F64x8([V; Q]);

/// Eight `E` elements, in memory order: lane `j` of register `r` is element `W * r + j`.
#[derive(Clone, Copy, Debug)]
pub struct F128x8([V; R]);

/// Eight unreduced `E` sums: register `r` holds the 128-bit coefficients of `y^0` and of `y^1` of the elements
/// [`F128x8`]'s register `r` holds, lane by lane.
#[derive(Clone, Copy, Debug)]
pub struct Acc8([[V; 2]; R]);

#[inline(always)]
fn clmul<const I: i32>(a: V, b: V) -> V {
    v::clmul::<I>(a, b)
}

/// `g(spill)` per top nibble `n` of a high word, in every 128-bit lane: `spill = n ^ n>>1 ^ n>>3` are the bits
/// `g(hi) = hi * (x^4 + x^3 + x + 1)` pushes past x^63, and `g(spill)` fits a byte.
const G_SPILL: [u8; 16] = {
    let mut t = [0u8; 16];
    let mut n = 0;
    while n < 16 {
        let spill = n ^ (n >> 1) ^ (n >> 3);
        t[n] = (spill ^ (spill << 1) ^ (spill << 3) ^ (spill << 4)) as u8;
        n += 1;
    }
    t
};

/// Qword `i` reduced: `lo[i] + hi[i] * x^64` modulo the base polynomial, as [`reduce`] computes it.
///
/// `lo ^ g(hi) ^ g(spill)`, with `g(h) = z ^ z<<3` for `z = h ^ h<<1`, and `g(spill)` one in-lane byte lookup on the
/// top nibble of `hi`.
#[inline(always)]
fn reduce_qwords(lo: V, hi: V) -> V {
    let z = v::xor(hi, v::shl::<1>(hi));
    let g_spill = v::lookup(G_SPILL, v::shr::<60>(hi));
    v::xor(v::xor(lo, z), v::xor(v::shl::<3>(z), g_spill))
}

/// `[d0, d1]` per 128-bit lane, each a coefficient's 128-bit polynomial, reduced to `[c0, c1]`.
#[inline(always)]
fn reduce_pair([d0, d1]: [V; 2]) -> V {
    reduce_qwords(v::unpacklo(d0, d1), v::unpackhi(d0, d1))
}

/// The y-folded Karatsuba product, lane by lane: with `p0 = a0 b0`, `p1 = a1 b1`, `p01 = (a0 + a1)(b0 + b1)` and
/// `y^2 = x y + 1`, the coefficients are `d0 = p0 + p1` and `d1 = p01 + p0 + p1 + x p1`. Both qwords of `a + swap(a)`
/// hold `a0 + a1`, so every product reads one qword of each operand's 128-bit lane.
#[inline(always)]
fn karatsuba(a: V, b: V) -> [V; 2] {
    let (p0, p1) = (clmul::<0x00>(a, b), clmul::<0x11>(a, b));
    let p01 = clmul::<0x00>(v::xor(a, v::swap(a)), v::xor(b, v::swap(b)));
    let d0 = v::xor(p0, p1);
    [d0, v::xor(v::xor(p01, d0), v::times_x(p1))]
}

/// One product, the scalar [`F128`] multiply: [`karatsuba`] and [`reduce_pair`] on a single 128-bit lane.
#[inline(always)]
pub(crate) fn mul(a: F128, b: F128) -> F128 {
    use core::arch::x86_64::*;
    // SAFETY: the module's cfg enables vpclmulqdq and avx2, which imply pclmulqdq and ssse3; each transmute is of 16
    // plain bytes.
    unsafe {
        let (a, b) = (
            core::mem::transmute::<F128, __m128i>(a),
            core::mem::transmute::<F128, __m128i>(b),
        );
        let sum = |x| _mm_xor_si128(x, _mm_shuffle_epi32::<0x4E>(x));
        let (p0, p1) = (_mm_clmulepi64_si128::<0x00>(a, b), _mm_clmulepi64_si128::<0x11>(a, b));
        let p01 = _mm_clmulepi64_si128::<0x00>(sum(a), sum(b));
        let times_x = _mm_or_si128(_mm_slli_epi64::<1>(p1), _mm_slli_si128::<8>(_mm_srli_epi64::<63>(p1)));
        let d0 = _mm_xor_si128(p0, p1);
        let d1 = _mm_xor_si128(_mm_xor_si128(p01, d0), times_x);
        let (lo, hi) = (_mm_unpacklo_epi64(d0, d1), _mm_unpackhi_epi64(d0, d1));
        let z = _mm_xor_si128(hi, _mm_slli_epi64::<1>(hi));
        let g_spill = _mm_shuffle_epi8(
            core::mem::transmute::<[u8; 16], __m128i>(G_SPILL),
            _mm_srli_epi64::<60>(hi),
        );
        let c = _mm_xor_si128(_mm_xor_si128(lo, z), _mm_xor_si128(_mm_slli_epi64::<3>(z), g_spill));
        core::mem::transmute::<__m128i, F128>(c)
    }
}

/// The eight carry-less products `a[i] * b[i]`, each 128 bits.
#[inline(always)]
pub fn clmul8(a: [u64; 8], b: [u64; 8]) -> [u128; 8] {
    // SAFETY: both sides of each transmute are plain bits of one size.
    let (a, b) = unsafe {
        (
            core::mem::transmute::<[u64; 8], [V; Q]>(a),
            core::mem::transmute::<[u64; 8], [V; Q]>(b),
        )
    };
    let mut out = [v::zero(); R];
    for q in 0..Q {
        [out[2 * q], out[2 * q + 1]] = v::interleave(clmul::<0x00>(a[q], b[q]), clmul::<0x11>(a[q], b[q]));
    }
    // SAFETY: as above.
    unsafe { core::mem::transmute::<[V; R], [u128; 8]>(out) }
}

/// The low 64 bits of the eight carry-less products `a[i] * b[i]`: the even and odd products' low qwords, unpacked
/// in place.
#[inline(always)]
pub fn clmul8_low(a: [u64; 8], b: [u64; 8]) -> [u64; 8] {
    // SAFETY: both sides of each transmute are plain bits of one size.
    let (a, b) = unsafe {
        (
            core::mem::transmute::<[u64; 8], [V; Q]>(a),
            core::mem::transmute::<[u64; 8], [V; Q]>(b),
        )
    };
    let out: [V; Q] = core::array::from_fn(|q| v::unpacklo(clmul::<0x00>(a[q], b[q]), clmul::<0x11>(a[q], b[q])));
    // SAFETY: as above.
    unsafe { core::mem::transmute::<[V; Q], [u64; 8]>(out) }
}

impl F64x8 {
    pub const ZERO: Self = Self([v::ZERO; Q]);

    #[inline(always)]
    pub fn splat(k: F64) -> Self {
        Self([v::splat(k.0, k.0); Q])
    }

    #[inline(always)]
    pub fn from_array(k: &[F64; 8]) -> Self {
        // SAFETY: both sides are plain bits of one size.
        Self(unsafe { core::mem::transmute::<[F64; 8], [V; Q]>(*k) })
    }

    #[inline(always)]
    pub fn to_array(self) -> [F64; 8] {
        // SAFETY: both sides are plain bits of one size.
        unsafe { core::mem::transmute::<[V; Q], [F64; 8]>(self.0) }
    }

    #[inline(always)]
    pub(super) fn xor(self, rhs: Self) -> Self {
        Self(core::array::from_fn(|q| v::xor(self.0[q], rhs.0[q])))
    }

    /// The even elements' products in one register and the odd ones' in another, then the reduction puts them back
    /// in memory order.
    #[inline(always)]
    pub(super) fn product(self, rhs: Self) -> Self {
        Self(core::array::from_fn(|q| {
            let (a, b) = (self.0[q], rhs.0[q]);
            reduce_pair([clmul::<0x00>(a, b), clmul::<0x11>(a, b)])
        }))
    }
}

impl F128x8 {
    pub const ZERO: Self = Self([v::ZERO; R]);

    #[inline(always)]
    pub fn splat(e: F128) -> Self {
        Self([v::splat(e.c0, e.c1); R])
    }

    #[inline(always)]
    pub fn from_array(e: &[F128; 8]) -> Self {
        // SAFETY: both sides are plain bits of one size.
        Self(unsafe { core::mem::transmute::<[F128; 8], [V; R]>(*e) })
    }

    #[inline(always)]
    pub fn to_array(self) -> [F128; 8] {
        // SAFETY: both sides are plain bits of one size.
        unsafe { core::mem::transmute::<[V; R], [F128; 8]>(self.0) }
    }

    /// The eight products, unreduced: three carry-less multiplications per register.
    #[inline(always)]
    pub fn mul_unreduced(self, rhs: Self) -> Acc8 {
        Acc8(core::array::from_fn(|r| karatsuba(self.0[r], rhs.0[r])))
    }

    /// The eight mixed products `self[i] * k[i]`.
    #[inline(always)]
    pub fn mul_base(self, k: F64x8) -> Self {
        self.mul_base_unreduced(k).reduce()
    }

    /// The eight mixed products `self[i] * k[i]`, unreduced: two carry-less multiplications per register, each
    /// coefficient against `k[i]`, spread over both qwords of element `i`'s lane.
    #[inline(always)]
    pub fn mul_base_unreduced(self, k: F64x8) -> Acc8 {
        let k = v::spread(k.0);
        Acc8(core::array::from_fn(|r| {
            [clmul::<0x00>(self.0[r], k[r]), clmul::<0x11>(self.0[r], k[r])]
        }))
    }

    #[inline(always)]
    pub(super) fn xor(self, rhs: Self) -> Self {
        Self(core::array::from_fn(|r| v::xor(self.0[r], rhs.0[r])))
    }

    #[inline(always)]
    pub(super) fn product(self, rhs: Self) -> Self {
        self.mul_unreduced(rhs).reduce()
    }
}

impl Acc8 {
    pub const ZERO: Self = Self([[v::ZERO; 2]; R]);

    /// Every lane reduced.
    #[inline(always)]
    pub fn reduce(self) -> F128x8 {
        F128x8(self.0.map(reduce_pair))
    }

    /// The sum of the eight lanes, reduced once.
    #[inline(always)]
    pub fn sum(self) -> F128 {
        let [d0, d1] = self
            .0
            .into_iter()
            .reduce(|s, x| [v::xor(s[0], x[0]), v::xor(s[1], x[1])])
            .unwrap();
        let [c0, c1] = [d0, d1].map(|d| reduce(v::lane_sum(d)));
        F128::new(c0, c1)
    }

    #[inline(always)]
    pub(super) fn xor(self, rhs: Self) -> Self {
        Self(core::array::from_fn(|r| {
            [v::xor(self.0[r][0], rhs.0[r][0]), v::xor(self.0[r][1], rhs.0[r][1])]
        }))
    }
}

/// The moves that depend on the register width. The cfg that compiles this module enables every intrinsic here.
#[cfg(all(target_feature = "avx512f", target_feature = "avx512bw"))]
mod v {
    use super::{Q, R};
    use core::arch::x86_64::*;

    pub type V = __m512i;
    // SAFETY: an all-zero bit pattern is a valid vector.
    pub const ZERO: V = unsafe { core::mem::zeroed() };

    #[inline(always)]
    pub fn zero() -> V {
        ZERO
    }

    /// `[lo, hi]` in every 128-bit lane.
    #[inline(always)]
    pub fn splat(lo: u64, hi: u64) -> V {
        // SAFETY: the module's cfg enables avx512f.
        unsafe {
            _mm512_set_epi64(
                hi as i64, lo as i64, hi as i64, lo as i64, hi as i64, lo as i64, hi as i64, lo as i64,
            )
        }
    }

    #[inline(always)]
    pub fn xor(a: V, b: V) -> V {
        // SAFETY: the module's cfg enables avx512f.
        unsafe { _mm512_xor_si512(a, b) }
    }

    #[inline(always)]
    pub fn clmul<const I: i32>(a: V, b: V) -> V {
        // SAFETY: the module's cfg enables avx512f and vpclmulqdq.
        unsafe { _mm512_clmulepi64_epi128::<I>(a, b) }
    }

    #[inline(always)]
    pub fn shl<const N: u32>(a: V) -> V {
        // SAFETY: the module's cfg enables avx512f.
        unsafe { _mm512_slli_epi64::<N>(a) }
    }

    #[inline(always)]
    pub fn shr<const N: u32>(a: V) -> V {
        // SAFETY: the module's cfg enables avx512f.
        unsafe { _mm512_srli_epi64::<N>(a) }
    }

    /// Each byte `b < 16` replaced by `table[b]`.
    #[inline(always)]
    pub fn lookup(table: [u8; 16], b: V) -> V {
        // SAFETY: the module's cfg enables avx512f and avx512bw; the transmute is of 16 plain bytes.
        unsafe {
            _mm512_shuffle_epi8(
                _mm512_broadcast_i32x4(core::mem::transmute::<[u8; 16], __m128i>(table)),
                b,
            )
        }
    }

    /// The qwords of each 128-bit lane swapped.
    #[inline(always)]
    pub fn swap(a: V) -> V {
        // SAFETY: the module's cfg enables avx512f.
        unsafe { _mm512_shuffle_epi32::<0x4E>(a) }
    }

    /// `x * p` for each 128-bit lane `p` of degree at most 126: a one-bit shift across the qwords.
    #[inline(always)]
    pub fn times_x(p: V) -> V {
        // SAFETY: the module's cfg enables avx512f and avx512bw.
        unsafe {
            _mm512_or_si512(
                _mm512_slli_epi64::<1>(p),
                _mm512_bslli_epi128::<8>(_mm512_srli_epi64::<63>(p)),
            )
        }
    }

    #[inline(always)]
    pub fn unpacklo(a: V, b: V) -> V {
        // SAFETY: the module's cfg enables avx512f.
        unsafe { _mm512_unpacklo_epi64(a, b) }
    }

    #[inline(always)]
    pub fn unpackhi(a: V, b: V) -> V {
        // SAFETY: the module's cfg enables avx512f.
        unsafe { _mm512_unpackhi_epi64(a, b) }
    }

    /// The XOR of the 128-bit lanes.
    #[inline(always)]
    pub fn lane_sum(a: V) -> u128 {
        // SAFETY: the module's cfg enables avx512f; the transmute is of 16 plain bytes.
        unsafe {
            let h = _mm256_xor_si256(_mm512_castsi512_si256(a), _mm512_extracti64x4_epi64::<1>(a));
            core::mem::transmute(_mm_xor_si128(
                _mm256_castsi256_si128(h),
                _mm256_extracti128_si256::<1>(h),
            ))
        }
    }

    /// Eight `K` elements spread one to a 128-bit lane, in both its qwords: lane `j` of register `r` is `k[4r + j]`.
    #[inline(always)]
    pub fn spread(k: [V; Q]) -> [V; R] {
        // SAFETY: the module's cfg enables avx512f.
        unsafe {
            [
                _mm512_permutexvar_epi64(_mm512_setr_epi64(0, 0, 1, 1, 2, 2, 3, 3), k[0]),
                _mm512_permutexvar_epi64(_mm512_setr_epi64(4, 4, 5, 5, 6, 6, 7, 7), k[0]),
            ]
        }
    }

    /// Products of the even qwords and of the odd ones, one per 128-bit lane, in memory order over two registers.
    #[inline(always)]
    pub fn interleave(even: V, odd: V) -> [V; 2] {
        // SAFETY: the module's cfg enables avx512f.
        unsafe {
            [
                _mm512_permutex2var_epi64(even, _mm512_setr_epi64(0, 1, 8, 9, 2, 3, 10, 11), odd),
                _mm512_permutex2var_epi64(even, _mm512_setr_epi64(4, 5, 12, 13, 6, 7, 14, 15), odd),
            ]
        }
    }
}

/// The moves that depend on the register width. The cfg that compiles this module enables every intrinsic here.
#[cfg(not(all(target_feature = "avx512f", target_feature = "avx512bw")))]
mod v {
    use super::{Q, R};
    use core::arch::x86_64::*;

    pub type V = __m256i;
    // SAFETY: an all-zero bit pattern is a valid vector.
    pub const ZERO: V = unsafe { core::mem::zeroed() };

    #[inline(always)]
    pub fn zero() -> V {
        ZERO
    }

    /// `[lo, hi]` in every 128-bit lane.
    #[inline(always)]
    pub fn splat(lo: u64, hi: u64) -> V {
        // SAFETY: the module's cfg enables avx2.
        unsafe { _mm256_set_epi64x(hi as i64, lo as i64, hi as i64, lo as i64) }
    }

    #[inline(always)]
    pub fn xor(a: V, b: V) -> V {
        // SAFETY: the module's cfg enables avx2.
        unsafe { _mm256_xor_si256(a, b) }
    }

    #[inline(always)]
    pub fn clmul<const I: i32>(a: V, b: V) -> V {
        // SAFETY: the module's cfg enables avx2 and vpclmulqdq.
        unsafe { _mm256_clmulepi64_epi128::<I>(a, b) }
    }

    #[inline(always)]
    pub fn shl<const N: i32>(a: V) -> V {
        // SAFETY: the module's cfg enables avx2.
        unsafe { _mm256_slli_epi64::<N>(a) }
    }

    #[inline(always)]
    pub fn shr<const N: i32>(a: V) -> V {
        // SAFETY: the module's cfg enables avx2.
        unsafe { _mm256_srli_epi64::<N>(a) }
    }

    /// Each byte `b < 16` replaced by `table[b]`.
    #[inline(always)]
    pub fn lookup(table: [u8; 16], b: V) -> V {
        // SAFETY: the module's cfg enables avx2; the transmute is of 16 plain bytes.
        unsafe {
            _mm256_shuffle_epi8(
                _mm256_broadcastsi128_si256(core::mem::transmute::<[u8; 16], __m128i>(table)),
                b,
            )
        }
    }

    /// The qwords of each 128-bit lane swapped.
    #[inline(always)]
    pub fn swap(a: V) -> V {
        // SAFETY: the module's cfg enables avx2.
        unsafe { _mm256_shuffle_epi32::<0x4E>(a) }
    }

    /// `x * p` for each 128-bit lane `p` of degree at most 126: a one-bit shift across the qwords.
    #[inline(always)]
    pub fn times_x(p: V) -> V {
        // SAFETY: the module's cfg enables avx2.
        unsafe {
            _mm256_or_si256(
                _mm256_slli_epi64::<1>(p),
                _mm256_bslli_epi128::<8>(_mm256_srli_epi64::<63>(p)),
            )
        }
    }

    #[inline(always)]
    pub fn unpacklo(a: V, b: V) -> V {
        // SAFETY: the module's cfg enables avx2.
        unsafe { _mm256_unpacklo_epi64(a, b) }
    }

    #[inline(always)]
    pub fn unpackhi(a: V, b: V) -> V {
        // SAFETY: the module's cfg enables avx2.
        unsafe { _mm256_unpackhi_epi64(a, b) }
    }

    /// The XOR of the 128-bit lanes.
    #[inline(always)]
    pub fn lane_sum(a: V) -> u128 {
        // SAFETY: the module's cfg enables avx2; the transmute is of 16 plain bytes.
        unsafe {
            core::mem::transmute(_mm_xor_si128(
                _mm256_castsi256_si128(a),
                _mm256_extracti128_si256::<1>(a),
            ))
        }
    }

    /// Eight `K` elements spread one to a 128-bit lane, in both its qwords: lane `j` of register `r` is `k[2r + j]`.
    #[inline(always)]
    pub fn spread(k: [V; Q]) -> [V; R] {
        // SAFETY: the module's cfg enables avx2.
        unsafe {
            [
                _mm256_permute4x64_epi64::<0x50>(k[0]),
                _mm256_permute4x64_epi64::<0xFA>(k[0]),
                _mm256_permute4x64_epi64::<0x50>(k[1]),
                _mm256_permute4x64_epi64::<0xFA>(k[1]),
            ]
        }
    }

    /// Products of the even qwords and of the odd ones, one per 128-bit lane, in memory order over two registers.
    #[inline(always)]
    pub fn interleave(even: V, odd: V) -> [V; 2] {
        // SAFETY: the module's cfg enables avx2.
        unsafe {
            [
                _mm256_permute2x128_si256::<0x20>(even, odd),
                _mm256_permute2x128_si256::<0x31>(even, odd),
            ]
        }
    }
}

use v::V;
