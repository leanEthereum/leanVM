// Credits: Plonky3 (https://github.com/Plonky3/Plonky3) (MIT and Apache-2.0 licenses).

use alloc::vec::Vec;
use core::arch::x86_64::*;
use core::fmt::Debug;
use core::iter::{Product, Sum};
use core::mem::transmute;
use core::ops::{Add, AddAssign, Div, DivAssign, Mul, MulAssign, Neg, Sub, SubAssign};

use field::interleave::{interleave_u64, interleave_u128, interleave_u256};
use field::op_assign_macros::{
    impl_add_assign, impl_add_base_field, impl_div_methods, impl_mul_base_field, impl_mul_methods, impl_packed_value,
    impl_rng, impl_sub_assign, impl_sub_base_field, impl_sum_prod_base_field, ring_sum,
};
use field::{
    Algebra, Field, InjectiveMonomial, PackedField, PackedFieldPow2, PackedValue, PermutationMonomial,
    PrimeCharacteristicRing, PrimeField64, impl_packed_field_pow_2,
};
use rand::Rng;
use rand::distr::{Distribution, StandardUniform};
use utils::reconstitute_from_base;

use crate::helpers::exp_10540996611094048183;
use crate::{Goldilocks, P};

const WIDTH: usize = 8;

/// Vectorized AVX512 implementation of `Goldilocks` arithmetic.
#[derive(Copy, Clone, Debug, Default, PartialEq, Eq)]
#[repr(transparent)] // Needed to make `transmute`s safe.
#[must_use]
pub struct PackedGoldilocksAVX512(pub [Goldilocks; WIDTH]);

impl PackedGoldilocksAVX512 {
    /// Get an arch-specific vector representing the packed values.
    #[inline]
    #[must_use]
    pub(crate) fn to_vector(self) -> __m512i {
        unsafe { transmute(self) }
    }

    /// Make a packed field vector from an arch-specific vector.
    ///
    /// Goldilocks elements may be arbitrary u64s, so this is always safe.
    #[inline]
    pub(crate) fn from_vector(vector: __m512i) -> Self {
        unsafe { transmute(vector) }
    }

    /// Copy `value` to all positions in a packed vector. `const` version of `From<Goldilocks>`.
    #[inline]
    const fn broadcast(value: Goldilocks) -> Self {
        Self([value; WIDTH])
    }
}

impl From<Goldilocks> for PackedGoldilocksAVX512 {
    fn from(x: Goldilocks) -> Self {
        Self::broadcast(x)
    }
}

impl Add for PackedGoldilocksAVX512 {
    type Output = Self;
    #[inline]
    fn add(self, rhs: Self) -> Self {
        Self::from_vector(add(self.to_vector(), rhs.to_vector()))
    }
}

impl Sub for PackedGoldilocksAVX512 {
    type Output = Self;
    #[inline]
    fn sub(self, rhs: Self) -> Self {
        Self::from_vector(sub(self.to_vector(), rhs.to_vector()))
    }
}

impl Neg for PackedGoldilocksAVX512 {
    type Output = Self;
    #[inline]
    fn neg(self) -> Self {
        Self::from_vector(neg(self.to_vector()))
    }
}

impl Mul for PackedGoldilocksAVX512 {
    type Output = Self;
    #[inline]
    fn mul(self, rhs: Self) -> Self {
        Self::from_vector(mul(self.to_vector(), rhs.to_vector()))
    }
}

impl_add_assign!(PackedGoldilocksAVX512);
impl_sub_assign!(PackedGoldilocksAVX512);
impl_mul_methods!(PackedGoldilocksAVX512);
ring_sum!(PackedGoldilocksAVX512);
impl_rng!(PackedGoldilocksAVX512);

impl PrimeCharacteristicRing for PackedGoldilocksAVX512 {
    type PrimeSubfield = Goldilocks;

    const ZERO: Self = Self::broadcast(Goldilocks::ZERO);
    const ONE: Self = Self::broadcast(Goldilocks::ONE);
    const TWO: Self = Self::broadcast(Goldilocks::TWO);
    const NEG_ONE: Self = Self::broadcast(Goldilocks::NEG_ONE);

    #[inline]
    fn from_prime_subfield(f: Self::PrimeSubfield) -> Self {
        f.into()
    }

    #[inline]
    fn halve(&self) -> Self {
        Self::from_vector(halve(self.to_vector()))
    }

    #[inline]
    fn square(&self) -> Self {
        Self::from_vector(square(self.to_vector()))
    }

    #[inline]
    fn zero_vec(len: usize) -> Vec<Self> {
        // SAFETY: this is a repr(transparent) wrapper around an array.
        unsafe { reconstitute_from_base(Goldilocks::zero_vec(len * WIDTH)) }
    }

    // Deferred multiply-accumulate protocol (plan_spec h3 §1.2-§1.5, §2).
    //
    // Accumulator layout: [L, H, W, K], one zmm each:
    //   L = wrapping sum of term lows;  K = count of L-wraps (each worth 2^64)
    //   H = wrapping sum of term highs; W = count of H-wraps (each worth 2^128)
    // so the represented value is V = L + (H + K)*2^64 + W*2^128.
    //
    // Subtraction is NOT-based: adding (~t_hi, ~t_lo) contributes
    // 2^128 - 1 - t = -t - (2^32 + 1) (mod P), since 2^128 = -2^32. Each sub
    // therefore leaves a constant deficit of (2^32 + 1), repaid once at finish
    // via `n_sub` (T1 protocol contract).
    //
    // The separate K counter is mandatory: folding the lo-carry into t_hi via a
    // masked +1 is only safe for t_hi <= 2^64 - 2 (true for raw products) but NOT
    // for NOT-ed terms, where ~t_hi = 2^64 - 1 whenever t_hi = 0 — and zero
    // products are reachable in real eval tables (plan §1.4: correctness over
    // cleverness).
    //
    // Finish (plan §1.3): merge K into H (carry into W), then one folding step
    //   V = L + H'_lo*eps - (H'_hi + W*2^32)   (mod P)
    // using 2^64 = eps, 2^96 = -1, 2^128 = -2^32, with the same
    // sub_no_double/add_no_double tail as `reduce128` below. Bounds (§1.5):
    // the T1 contract caps accumulation at 5*2^20 terms, so W, K < 2^23 and
    // s = H'_hi + W*2^32 < 2^32 + 2^55 < P (tail precondition).

    #[inline]
    fn unreduced_mul(a: Self, b: Self) -> [Self; 4] {
        let (hi, lo) = mul64_64(a.to_vector(), b.to_vector());
        [Self::from_vector(lo), Self::from_vector(hi), Self::ZERO, Self::ZERO]
    }

    #[inline]
    fn lazy_acc_zero() -> [Self; 4] {
        [Self::ZERO; 4]
    }

    #[inline]
    fn lazy_acc_add(acc: [Self; 4], t: [Self; 4]) -> [Self; 4] {
        unsafe {
            let (l, h, w, k) = (
                acc[0].to_vector(),
                acc[1].to_vector(),
                acc[2].to_vector(),
                acc[3].to_vector(),
            );
            let (t_lo, t_hi) = (t[0].to_vector(), t[1].to_vector());
            let one = _mm512_set1_epi64(1);

            let l2 = _mm512_add_epi64(l, t_lo);
            let carry_l = _mm512_cmplt_epu64_mask(l2, t_lo);
            let k2 = _mm512_mask_add_epi64(k, carry_l, k, one);

            let h2 = _mm512_add_epi64(h, t_hi);
            let carry_h = _mm512_cmplt_epu64_mask(h2, t_hi);
            let w2 = _mm512_mask_add_epi64(w, carry_h, w, one);

            [
                Self::from_vector(l2),
                Self::from_vector(h2),
                Self::from_vector(w2),
                Self::from_vector(k2),
            ]
        }
    }

    #[inline]
    fn lazy_acc_sub(acc: [Self; 4], t: [Self; 4]) -> [Self; 4] {
        unsafe {
            // NOT both halves (vpternlogq imm 0x55 = NOT a), then add as usual.
            let t_lo = t[0].to_vector();
            let t_hi = t[1].to_vector();
            let nt_lo = _mm512_ternarylogic_epi64::<0x55>(t_lo, t_lo, t_lo);
            let nt_hi = _mm512_ternarylogic_epi64::<0x55>(t_hi, t_hi, t_hi);
            Self::lazy_acc_add(
                acc,
                [
                    Self::from_vector(nt_lo),
                    Self::from_vector(nt_hi),
                    Self::ZERO,
                    Self::ZERO,
                ],
            )
        }
    }

    #[inline]
    fn lazy_acc_finish(acc: [Self; 4], n_sub: u64) -> Self {
        unsafe {
            let (l, h, w, k) = (
                acc[0].to_vector(),
                acc[1].to_vector(),
                acc[2].to_vector(),
                acc[3].to_vector(),
            );
            let one = _mm512_set1_epi64(1);

            // Merge the lo-wrap counter into H, carrying into W.
            let h2 = _mm512_add_epi64(h, k);
            let carry = _mm512_cmplt_epu64_mask(h2, k);
            let w2 = _mm512_mask_add_epi64(w, carry, w, one);

            #[cfg(debug_assertions)]
            {
                let w_arr: [u64; WIDTH] = transmute(w2);
                let k_arr: [u64; WIDTH] = transmute(k);
                for i in 0..WIDTH {
                    debug_assert!(
                        w_arr[i] < (1 << 23) && k_arr[i] < (1 << 23),
                        "lazy accumulator wrap counters out of §1.5 bound"
                    );
                }
            }

            // One folding step: V = L + H'_lo*eps - (H'_hi + W*2^32)  (mod P).
            let e = _mm512_mul_epu32(h2, EPSILON);
            let s = _mm512_add_epi64(_mm512_srli_epi64::<32>(h2), _mm512_slli_epi64::<32>(w2));
            let t0 = sub_no_double_overflow_64_64(l, s);
            let r = add_no_double_overflow_64_64(t0, e);
            let r = Self::from_vector(r);

            if n_sub == 0 {
                r
            } else {
                // Repay the NOT deficit: n_sub * (2^32 + 1), n_sub < 2^23 so no overflow.
                let deficit = Goldilocks::new(n_sub * ((1u64 << 32) + 1));
                r + Self::broadcast(deficit)
            }
        }
    }
}

impl_add_base_field!(PackedGoldilocksAVX512, Goldilocks);
impl_sub_base_field!(PackedGoldilocksAVX512, Goldilocks);
impl_mul_base_field!(PackedGoldilocksAVX512, Goldilocks);
impl_div_methods!(PackedGoldilocksAVX512, Goldilocks);
impl_sum_prod_base_field!(PackedGoldilocksAVX512, Goldilocks);

impl Algebra<Goldilocks> for PackedGoldilocksAVX512 {}

impl InjectiveMonomial<7> for PackedGoldilocksAVX512 {}

impl PermutationMonomial<7> for PackedGoldilocksAVX512 {
    fn injective_exp_root_n(&self) -> Self {
        exp_10540996611094048183(*self)
    }
}

impl_packed_value!(PackedGoldilocksAVX512, Goldilocks, WIDTH);

unsafe impl PackedField for PackedGoldilocksAVX512 {
    type Scalar = Goldilocks;
}

impl_packed_field_pow_2!(
    PackedGoldilocksAVX512;
    [
        (1, interleave_u64),
        (2, interleave_u128),
        (4, interleave_u256),
    ],
    WIDTH
);

const FIELD_ORDER: __m512i = unsafe { transmute([Goldilocks::ORDER_U64; WIDTH]) };
const EPSILON: __m512i = unsafe { transmute([Goldilocks::ORDER_U64.wrapping_neg(); WIDTH]) };

#[inline]
unsafe fn canonicalize(x: __m512i) -> __m512i {
    // For `x < ORDER`, `x - ORDER` underflows to a huge u64, so `min` picks the
    // original. For `x >= ORDER`, `x - ORDER` is the canonical form (smaller),
    // so `min` picks it. One sub + one min instead of cmpge + masked sub.
    unsafe { _mm512_min_epu64(x, _mm512_sub_epi64(x, FIELD_ORDER)) }
}

/// Compute `x + y mod P`. Result may be > P.
///
/// # Safety
/// Caller must ensure `x + y < 2^64 + P`.
#[inline]
unsafe fn add_no_double_overflow_64_64(x: __m512i, y: __m512i) -> __m512i {
    unsafe {
        let res_wrapped = _mm512_add_epi64(x, y);
        let mask = _mm512_cmplt_epu64_mask(res_wrapped, y);
        _mm512_mask_sub_epi64(res_wrapped, mask, res_wrapped, FIELD_ORDER)
    }
}

/// Compute `x - y mod P`. Result may be > P.
///
/// # Safety
/// Caller must ensure `x - y > -P`.
#[inline]
unsafe fn sub_no_double_overflow_64_64(x: __m512i, y: __m512i) -> __m512i {
    unsafe {
        let mask = _mm512_cmplt_epu64_mask(x, y);
        let res_wrapped = _mm512_sub_epi64(x, y);
        _mm512_mask_add_epi64(res_wrapped, mask, res_wrapped, FIELD_ORDER)
    }
}

#[inline]
fn add(x: __m512i, y: __m512i) -> __m512i {
    unsafe { add_no_double_overflow_64_64(x, canonicalize(y)) }
}

#[inline]
fn sub(x: __m512i, y: __m512i) -> __m512i {
    unsafe { sub_no_double_overflow_64_64(x, canonicalize(y)) }
}

#[inline]
fn neg(y: __m512i) -> __m512i {
    unsafe { _mm512_sub_epi64(FIELD_ORDER, canonicalize(y)) }
}

/// Halve a vector of Goldilocks field elements.
#[inline(always)]
pub(crate) fn halve(input: __m512i) -> __m512i {
    // For val in [0, P): val even -> val/2 = val>>1; val odd -> (val+P)/2 = (val>>1) + (P+1)/2.
    unsafe {
        const ONE: __m512i = unsafe { transmute([1_i64; 8]) };
        let half = _mm512_set1_epi64(P.div_ceil(2) as i64);

        let least_bit = _mm512_test_epi64_mask(input, ONE);
        let t = _mm512_srli_epi64::<1>(input);
        _mm512_mask_add_epi64(t, least_bit, t, half)
    }
}

#[allow(clippy::useless_transmute)]
const LO_32_BITS_MASK: __mmask16 = unsafe { transmute(0b0101010101010101u16) };

/// Full 64x64 -> 128 multiplication, returning `(hi, lo)`.
#[inline]
fn mul64_64(x: __m512i, y: __m512i) -> (__m512i, __m512i) {
    unsafe {
        let x_hi = _mm512_castps_si512(_mm512_movehdup_ps(_mm512_castsi512_ps(x)));
        let y_hi = _mm512_castps_si512(_mm512_movehdup_ps(_mm512_castsi512_ps(y)));

        let mul_ll = _mm512_mul_epu32(x, y);
        let mul_lh = _mm512_mul_epu32(x, y_hi);
        let mul_hl = _mm512_mul_epu32(x_hi, y);
        let mul_hh = _mm512_mul_epu32(x_hi, y_hi);

        let mul_ll_hi = _mm512_srli_epi64::<32>(mul_ll);
        let t0 = _mm512_add_epi64(mul_hl, mul_ll_hi);
        let t0_lo = _mm512_and_si512(t0, EPSILON);
        let t0_hi = _mm512_srli_epi64::<32>(t0);
        let t1 = _mm512_add_epi64(mul_lh, t0_lo);
        let t2 = _mm512_add_epi64(mul_hh, t0_hi);
        let t1_hi = _mm512_srli_epi64::<32>(t1);
        let res_hi = _mm512_add_epi64(t2, t1_hi);

        let t1_lo = _mm512_castps_si512(_mm512_moveldup_ps(_mm512_castsi512_ps(t1)));
        let res_lo = _mm512_mask_blend_epi32(LO_32_BITS_MASK, t1_lo, mul_ll);

        (res_hi, res_lo)
    }
}

/// Full 64-bit squaring.
#[inline]
fn square64(x: __m512i) -> (__m512i, __m512i) {
    unsafe {
        let x_hi = _mm512_castps_si512(_mm512_movehdup_ps(_mm512_castsi512_ps(x)));

        let mul_ll = _mm512_mul_epu32(x, x);
        let mul_lh = _mm512_mul_epu32(x, x_hi);
        let mul_hh = _mm512_mul_epu32(x_hi, x_hi);

        let mul_ll_hi = _mm512_srli_epi64::<33>(mul_ll);
        let t0 = _mm512_add_epi64(mul_lh, mul_ll_hi);
        let t0_hi = _mm512_srli_epi64::<31>(t0);
        let res_hi = _mm512_add_epi64(mul_hh, t0_hi);

        let mul_lh_lo = _mm512_slli_epi64::<33>(mul_lh);
        let res_lo = _mm512_add_epi64(mul_ll, mul_lh_lo);

        (res_hi, res_lo)
    }
}

/// Reduce a 128-bit value (high, low) modulo `P`. Result may be > P.
#[inline]
fn reduce128(x: (__m512i, __m512i)) -> __m512i {
    unsafe {
        let (hi0, lo0) = x;

        let hi_hi0 = _mm512_srli_epi64::<32>(hi0);

        // 2^96 = -1 mod P.
        let lo1 = sub_no_double_overflow_64_64(lo0, hi_hi0);

        // Bottom 32 bits of hi0 times 2^64 = 2^32 - 1 mod P.
        let t1 = _mm512_mul_epu32(hi0, EPSILON);

        add_no_double_overflow_64_64(lo1, t1)
    }
}

#[inline]
fn mul(x: __m512i, y: __m512i) -> __m512i {
    reduce128(mul64_64(x, y))
}

#[inline]
fn square(x: __m512i) -> __m512i {
    reduce128(square64(x))
}

// =========================================================================
// SIMD-vectorized Poseidon1 MDS multiplication
// =========================================================================
//
// Computes the width-8 circulant MDS matrix-vector product entirely in
// `__m512i` registers, with delayed reduction. Each output is
// `sum_j MDS_ROW[(j-i) mod 8] * state[j]`. Coefficients are in
// {1, 3, 4, 7, 8, 9} (max 9), so per-term products fit in u68 and sums of
// 8 terms fit comfortably in u71.
//
// We multiply via two 32x32 `_mm512_mul_epu32` calls (low half and high
// half of state), which exploits that the constants fit in 4 bits (so the
// "high 32 bits" operand of mul_epu32 is zero by construction). Sums of
// the low and high halves are accumulated separately into u64s, then we
// assemble the (hi, lo) u128 pair and call `reduce128`.

use crate::poseidon1::{MDS8_ROW, POSEIDON1_WIDTH};

/// Add a known-canonical `Goldilocks` scalar to a packed state, skipping the
/// `canonicalize` that the generic `Add` applies to its right-hand side.
///
/// # Safety contract
/// The caller must guarantee that `c.value < P`. Otherwise `x + c` may exceed
/// `2^64 + P` and the wrap-detection in `add_no_double_overflow_64_64` will
/// produce a wrong result. Round constants pulled from
/// `GOLDILOCKS_POSEIDON1_RC_8` satisfy this trivially.
#[inline(always)]
pub(crate) fn add_canonical_scalar(x: PackedGoldilocksAVX512, c: Goldilocks) -> PackedGoldilocksAVX512 {
    unsafe {
        let c_vec = PackedGoldilocksAVX512::from(c).to_vector();
        PackedGoldilocksAVX512::from_vector(add_no_double_overflow_64_64(x.to_vector(), c_vec))
    }
}

/// Compute the `I`-th output of the width-8 circulant MDS matrix-vector product.
///
/// `I` is a const generic so that each instantiation is a distinct function
/// from LLVM's perspective — otherwise LLVM rolls all 8 output computations
/// back into a loop, serializing them and bouncing state through stack memory.
#[inline(always)]
unsafe fn mds_output<const I: usize>(s: &[__m512i; 8], s_hi: &[__m512i; 8]) -> __m512i {
    unsafe {
        let mut sum_ll = _mm512_setzero_si512();
        let mut sum_hl = _mm512_setzero_si512();
        // Row I of the circulant matrix is `MDS8_ROW` rotated right by I.
        // The j loop is fully unrolled by LLVM since both bounds and indices
        // are compile-time constants.
        let mut j = 0;
        while j < 8 {
            let c = MDS8_ROW[(j + 8 - I) % 8];
            let c_vec = _mm512_set1_epi64(c);
            sum_ll = _mm512_add_epi64(sum_ll, _mm512_mul_epu32(s[j], c_vec));
            sum_hl = _mm512_add_epi64(sum_hl, _mm512_mul_epu32(s_hi[j], c_vec));
            j += 1;
        }

        // Total = sum_ll + (sum_hl << 32). Compose into (hi, lo) u128.
        // sum_ll < 2^39, sum_hl < 2^39, so sum_hl >> 32 < 2^7.
        let sum_hl_shifted = _mm512_slli_epi64::<32>(sum_hl);
        let lo = _mm512_add_epi64(sum_ll, sum_hl_shifted);
        // Detect unsigned overflow: lo < sum_hl_shifted iff the add wrapped.
        let carry_mask = _mm512_cmplt_epu64_mask(lo, sum_hl_shifted);
        let hi_no_carry = _mm512_srli_epi64::<32>(sum_hl);
        let hi = _mm512_mask_add_epi64(hi_no_carry, carry_mask, hi_no_carry, _mm512_set1_epi64(1));

        reduce128((hi, lo))
    }
}

/// SIMD MDS multiplication for the width-8 circulant Poseidon1 matrix.
///
/// Takes/returns by value so the caller can keep state in named SSA scalars
/// (zmm registers) rather than indexing through a `&mut [P; 8]` (which forces
/// the array through the stack). Each of the 8 outputs is computed by a
/// distinct const-generic instantiation of `mds_output`, preventing LLVM
/// from re-rolling them.
///
/// Note: an `avx512ifma` variant of this (using `vpmadd52luq` to fuse the
/// mul-add accumulation) was tried and measured ~15% *slower* on Zen 4 — the
/// fused IFMA op runs on the multiplier port at no better throughput than
/// `vpmuludq`, while the `vpaddq` it replaces was happily dual-issuing on the
/// add ports. Kept the `vpmuludq + vpaddq` form.
#[inline(always)]
pub fn mds_mul_simd(state: [PackedGoldilocksAVX512; POSEIDON1_WIDTH]) -> [PackedGoldilocksAVX512; POSEIDON1_WIDTH] {
    unsafe {
        let s: [__m512i; 8] = [
            state[0].to_vector(),
            state[1].to_vector(),
            state[2].to_vector(),
            state[3].to_vector(),
            state[4].to_vector(),
            state[5].to_vector(),
            state[6].to_vector(),
            state[7].to_vector(),
        ];
        // Precompute the high 32 bits of every state slot once.
        let s_hi: [__m512i; 8] = [
            _mm512_srli_epi64::<32>(s[0]),
            _mm512_srli_epi64::<32>(s[1]),
            _mm512_srli_epi64::<32>(s[2]),
            _mm512_srli_epi64::<32>(s[3]),
            _mm512_srli_epi64::<32>(s[4]),
            _mm512_srli_epi64::<32>(s[5]),
            _mm512_srli_epi64::<32>(s[6]),
            _mm512_srli_epi64::<32>(s[7]),
        ];

        [
            PackedGoldilocksAVX512::from_vector(mds_output::<0>(&s, &s_hi)),
            PackedGoldilocksAVX512::from_vector(mds_output::<1>(&s, &s_hi)),
            PackedGoldilocksAVX512::from_vector(mds_output::<2>(&s, &s_hi)),
            PackedGoldilocksAVX512::from_vector(mds_output::<3>(&s, &s_hi)),
            PackedGoldilocksAVX512::from_vector(mds_output::<4>(&s, &s_hi)),
            PackedGoldilocksAVX512::from_vector(mds_output::<5>(&s, &s_hi)),
            PackedGoldilocksAVX512::from_vector(mds_output::<6>(&s, &s_hi)),
            PackedGoldilocksAVX512::from_vector(mds_output::<7>(&s, &s_hi)),
        ]
    }
}

#[cfg(test)]
mod tests {
    use super::{Goldilocks, PackedGoldilocksAVX512, WIDTH};

    const SPECIAL_VALS: [Goldilocks; WIDTH] = Goldilocks::new_array([
        0xFFFF_FFFF_0000_0001,
        0xFFFF_FFFF_0000_0000,
        0xFFFF_FFFE_FFFF_FFFF,
        0xFFFF_FFFF_FFFF_FFFF,
        0x0000_0000_0000_0000,
        0x0000_0000_0000_0001,
        0x0000_0000_0000_0002,
        0x0FFF_FFFF_F000_0000,
    ]);

    #[test]
    fn pack_round_trip() {
        let p = PackedGoldilocksAVX512(SPECIAL_VALS);
        let v = p.to_vector();
        assert_eq!(PackedGoldilocksAVX512::from_vector(v).0, SPECIAL_VALS);
    }
}
