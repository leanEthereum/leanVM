//! The lanes in NEON registers, with PMULL: one `E` element to a register, `[c0, c1]`, and two `K` elements. A
//! carry-less multiply issues about as fast as an XOR here, so a product is the four-multiply schoolbook, which
//! needs no shuffle to form `a0 + a1`, and a reduction is two more multiplies by `x^64 = x^4 + x^3 + x + 1`. Every
//! operand stays in vector registers from load to store.

use core::arch::aarch64::*;
use core::mem::transmute;

use crate::field::gf2_64::R64;
use crate::field::{F64, F128};

type V = uint64x2_t;

/// Eight `K` elements, two to a register.
#[derive(Clone, Copy, Debug)]
pub struct F64x8([V; 4]);

/// Eight `E` elements, one to a register.
#[derive(Clone, Copy, Debug)]
pub struct F128x8([V; 8]);

/// Eight unreduced `E` sums: per element, the 128-bit coefficients of `y^0` and of `y^1`.
#[derive(Clone, Copy, Debug)]
pub struct Acc8([[V; 2]; 8]);

// SAFETY: an all-zero bit pattern is a valid vector.
const ZERO: V = unsafe { core::mem::zeroed() };

/// The 128-bit carry-less product of the low qwords.
#[inline(always)]
fn lo(a: V, b: V) -> V {
    // SAFETY: the module's cfg enables aes; both sides of the transmute are 128 plain bits.
    unsafe { transmute::<u128, V>(vmull_p64(vgetq_lane_u64::<0>(a), vgetq_lane_u64::<0>(b))) }
}

/// The 128-bit carry-less product of the high qwords.
#[inline(always)]
fn hi(a: V, b: V) -> V {
    // SAFETY: the module's cfg enables aes; both sides of the transmute are 128 plain bits.
    unsafe { transmute::<u128, V>(vmull_high_p64(vreinterpretq_p64_u64(a), vreinterpretq_p64_u64(b))) }
}

#[inline(always)]
fn xor(a: V, b: V) -> V {
    // SAFETY: NEON is part of the aarch64 baseline.
    unsafe { veorq_u64(a, b) }
}

#[inline(always)]
fn xor3(a: V, b: V, c: V) -> V {
    #[cfg(target_feature = "sha3")]
    // SAFETY: the cfg enables sha3, which carries EOR3.
    unsafe {
        veor3q_u64(a, b, c)
    }
    #[cfg(not(target_feature = "sha3"))]
    xor(a, xor(b, c))
}

/// `x * p` for a 128-bit polynomial `p` of degree at most 126: a one-bit shift across the qwords.
#[inline(always)]
fn times_x(p: V) -> V {
    // SAFETY: NEON is part of the aarch64 baseline.
    unsafe { vorrq_u64(vshlq_n_u64::<1>(p), vextq_u64::<1>(ZERO, vshrq_n_u64::<63>(p))) }
}

/// One 128-bit coefficient `lo + hi * x^64` reduced into the low qword: `hi * 0x1B = [a, s]` with `s` of at most
/// four bits, `s * 0x1B = [b, 0]`, and the result `lo + a + b`.
#[inline(always)]
fn reduce_lane(d: V) -> V {
    // SAFETY: NEON is part of the aarch64 baseline.
    let r = unsafe { vdupq_n_u64(R64) };
    let t = hi(d, r);
    xor3(d, t, hi(t, r))
}

/// An element's two coefficients reduced, as its register `[c0, c1]`.
#[inline(always)]
fn reduce_pair([d0, d1]: [V; 2]) -> V {
    // SAFETY: NEON is part of the aarch64 baseline.
    unsafe { vzip1q_u64(reduce_lane(d0), reduce_lane(d1)) }
}

/// The y-folded schoolbook product: with `y^2 = x y + 1`, `d0 = a0 b0 + a1 b1` and `d1 = a0 b1 + a1 b0 + x a1 b1`.
#[inline(always)]
fn schoolbook(a: V, b: V) -> [V; 2] {
    // SAFETY: NEON is part of the aarch64 baseline.
    let swapped = unsafe { vextq_u64::<1>(a, a) };
    let (m00, m11) = (lo(a, b), hi(a, b));
    let (m10, m01) = (lo(swapped, b), hi(swapped, b));
    [xor(m00, m11), xor3(m01, m10, times_x(m11))]
}

/// The eight carry-less products `a[i] * b[i]`, each 128 bits.
#[inline(always)]
pub fn clmul8(a: [u64; 8], b: [u64; 8]) -> [u128; 8] {
    let (a, b) = (F64x8::from_array(&a.map(F64)).0, F64x8::from_array(&b.map(F64)).0);
    let p: [[V; 2]; 4] = core::array::from_fn(|q| [lo(a[q], b[q]), hi(a[q], b[q])]);
    // SAFETY: both sides are plain bits of one size.
    unsafe { transmute::<[[V; 2]; 4], [u128; 8]>(p) }
}

impl F64x8 {
    pub const ZERO: Self = Self([ZERO; 4]);

    #[inline(always)]
    pub fn splat(k: F64) -> Self {
        // SAFETY: NEON is part of the aarch64 baseline.
        Self([unsafe { vdupq_n_u64(k.0) }; 4])
    }

    #[inline(always)]
    pub fn from_array(k: &[F64; 8]) -> Self {
        // SAFETY: both sides are plain bits of one size.
        Self(unsafe { transmute::<[F64; 8], [V; 4]>(*k) })
    }

    #[inline(always)]
    pub fn to_array(self) -> [F64; 8] {
        // SAFETY: both sides are plain bits of one size.
        unsafe { transmute::<[V; 4], [F64; 8]>(self.0) }
    }

    #[inline(always)]
    pub(super) fn xor(self, rhs: Self) -> Self {
        Self(core::array::from_fn(|q| xor(self.0[q], rhs.0[q])))
    }

    #[inline(always)]
    pub(super) fn product(self, rhs: Self) -> Self {
        Self(core::array::from_fn(|q| {
            let (a, b) = (self.0[q], rhs.0[q]);
            reduce_pair([lo(a, b), hi(a, b)])
        }))
    }
}

impl F128x8 {
    pub const ZERO: Self = Self([ZERO; 8]);

    #[inline(always)]
    pub fn splat(e: F128) -> Self {
        // SAFETY: both sides are plain bits of one size.
        Self([unsafe { transmute::<F128, V>(e) }; 8])
    }

    #[inline(always)]
    pub fn from_array(e: &[F128; 8]) -> Self {
        // SAFETY: both sides are plain bits of one size.
        Self(unsafe { transmute::<[F128; 8], [V; 8]>(*e) })
    }

    #[inline(always)]
    pub fn to_array(self) -> [F128; 8] {
        // SAFETY: both sides are plain bits of one size.
        unsafe { transmute::<[V; 8], [F128; 8]>(self.0) }
    }

    /// The eight products, unreduced: four carry-less multiplications each.
    #[inline(always)]
    pub fn mul_unreduced(self, rhs: Self) -> Acc8 {
        Acc8(core::array::from_fn(|i| schoolbook(self.0[i], rhs.0[i])))
    }

    /// The eight mixed products `self[i] * k[i]`.
    #[inline(always)]
    pub fn mul_base(self, k: F64x8) -> Self {
        self.mul_base_unreduced(k).reduce()
    }

    /// The eight mixed products `self[i] * k[i]`, unreduced: each coefficient against `k[i]`, spread over both
    /// qwords.
    #[inline(always)]
    pub fn mul_base_unreduced(self, k: F64x8) -> Acc8 {
        Acc8(core::array::from_fn(|i| {
            // SAFETY: NEON is part of the aarch64 baseline.
            let k = unsafe {
                match i % 2 {
                    0 => vdupq_laneq_u64::<0>(k.0[i / 2]),
                    _ => vdupq_laneq_u64::<1>(k.0[i / 2]),
                }
            };
            [lo(self.0[i], k), hi(self.0[i], k)]
        }))
    }

    #[inline(always)]
    pub(super) fn xor(self, rhs: Self) -> Self {
        Self(core::array::from_fn(|i| xor(self.0[i], rhs.0[i])))
    }

    #[inline(always)]
    pub(super) fn product(self, rhs: Self) -> Self {
        self.mul_unreduced(rhs).reduce()
    }
}

impl Acc8 {
    pub const ZERO: Self = Self([[ZERO; 2]; 8]);

    /// Every lane reduced.
    #[inline(always)]
    pub fn reduce(self) -> F128x8 {
        F128x8(core::array::from_fn(|i| reduce_pair(self.0[i])))
    }

    /// The sum of the eight lanes, reduced once.
    #[inline(always)]
    pub fn sum(self) -> F128 {
        let s = self
            .0
            .into_iter()
            .reduce(|s, x| [xor(s[0], x[0]), xor(s[1], x[1])])
            .unwrap();
        // SAFETY: both sides are plain bits of one size.
        unsafe { transmute::<V, F128>(reduce_pair(s)) }
    }

    #[inline(always)]
    pub(super) fn xor(self, rhs: Self) -> Self {
        Self(core::array::from_fn(|i| {
            [xor(self.0[i][0], rhs.0[i][0]), xor(self.0[i][1], rhs.0[i][1])]
        }))
    }
}
