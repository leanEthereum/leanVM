//! Four lanes of products in YMM registers, for a machine with AVX2 but no AVX-512: the 256-bit
//! counterpart of the AVX-512 `x8`'s `F64x8`, `F128x8` and `Mixed8` for the leaf builder, and the
//! halves of the eight-lane `f128x8` types. Without VPCLMULQDQ a 256-bit carry-less product is two
//! 128-bit ones.

use core::arch::x86_64::*;
use core::ops::{Add, BitXor, BitXorAssign, Mul};

use super::gf2_64::F64;
use super::gf2_64x2::x86_64::{fold, reduce_halves256 as reduce_halves, times_x256};
use super::gf2_64x2::{F128, F128Unreduced};

/// Four `K` elements in one register.
#[derive(Clone, Copy, Debug)]
#[repr(transparent)]
pub struct F64x4(__m256i);

/// Four `E` elements; register `k` is coefficient `k` of lanes `0..4`.
#[derive(Clone, Copy, Debug)]
#[repr(transparent)]
pub struct F128x4(pub(super) [__m256i; 2]);

/// Per-lane unreduced sums of products, the even lanes' 128-bit partials apart from the odd ones'.
#[derive(Clone, Copy, Debug)]
pub struct Mixed4 {
    even: [__m256i; 2],
    odd: [__m256i; 2],
}

/// The sum over lanes of unreduced products, y-folded: per coefficient, two 128-bit partials.
#[derive(Clone, Copy, Debug)]
pub struct Sum4([__m256i; 2]);

#[inline(always)]
fn xor(a: __m256i, b: __m256i) -> __m256i {
    // SAFETY: the module's cfg enables avx2.
    unsafe { _mm256_xor_si256(a, b) }
}

/// `vpclmulqdq` with immediate `I`: in each 128-bit lane, the product of the qwords `I` picks, bit 0 in `a` and bit 4 in
/// `b`.
#[inline(always)]
pub fn clmul<const I: i32>(a: __m256i, b: __m256i) -> __m256i {
    #[cfg(target_feature = "vpclmulqdq")]
    // SAFETY: the cfg enables vpclmulqdq.
    return unsafe { _mm256_clmulepi64_epi128::<I>(a, b) };
    #[cfg(not(target_feature = "vpclmulqdq"))]
    // SAFETY: the module's cfg enables avx2 and pclmulqdq.
    unsafe {
        let lane = |a: __m128i, b: __m128i| _mm_clmulepi64_si128::<I>(a, b);
        _mm256_set_m128i(
            lane(_mm256_extracti128_si256::<1>(a), _mm256_extracti128_si256::<1>(b)),
            lane(_mm256_castsi256_si128(a), _mm256_castsi256_si128(b)),
        )
    }
}

/// The y-folded Karatsuba product of the even or the odd lanes.
#[inline(always)]
fn karatsuba<const I: i32>(a: [__m256i; 2], b: [__m256i; 2]) -> [__m256i; 2] {
    let (m0, m1) = (clmul::<I>(a[0], b[0]), clmul::<I>(a[1], b[1]));
    let m01 = clmul::<I>(xor(a[0], a[1]), xor(b[0], b[1]));
    // SAFETY: the module's cfg enables avx2.
    fold(m0, m1, m01, xor, |p| unsafe { times_x256(p) })
}

impl F64x4 {
    #[inline(always)]
    pub fn new(k: [F64; 4]) -> Self {
        Self::load(&k)
    }

    #[inline(always)]
    pub fn load(k: &[F64; 4]) -> Self {
        // SAFETY: the module's cfg enables avx2; the array is four qwords.
        Self(unsafe { _mm256_loadu_si256(k.as_ptr().cast()) })
    }

    #[inline(always)]
    pub fn splat(k: F64) -> Self {
        // SAFETY: the module's cfg enables avx2.
        Self(unsafe { _mm256_set1_epi64x(k.0 as i64) })
    }

    pub fn to_array(self) -> [F64; 4] {
        // SAFETY: both are 32 bytes.
        unsafe { std::mem::transmute(self.0) }
    }
}

impl Add for F64x4 {
    type Output = Self;
    #[inline(always)]
    fn add(self, rhs: Self) -> Self {
        Self(xor(self.0, rhs.0))
    }
}

impl Mul for F64x4 {
    type Output = Self;
    #[inline(always)]
    fn mul(self, rhs: Self) -> Self {
        // SAFETY: the module's cfg enables avx2.
        Self(unsafe { reduce_halves(clmul::<0x00>(self.0, rhs.0), clmul::<0x11>(self.0, rhs.0)) })
    }
}

impl F128x4 {
    #[inline(always)]
    pub fn splat(e: F128) -> Self {
        // SAFETY: the module's cfg enables avx2.
        unsafe { Self([_mm256_set1_epi64x(e.c0 as i64), _mm256_set1_epi64x(e.c1 as i64)]) }
    }

    /// Four consecutive elements.
    #[inline(always)]
    pub fn load(e: &[F128; 4]) -> Self {
        let plane = |c: fn(&F128) -> u64| {
            // SAFETY: the module's cfg enables avx2.
            unsafe { _mm256_set_epi64x(c(&e[3]) as i64, c(&e[2]) as i64, c(&e[1]) as i64, c(&e[0]) as i64) }
        };
        Self([plane(|e| e.c0), plane(|e| e.c1)])
    }

    /// The lanes as four consecutive elements.
    #[inline(always)]
    pub fn store(self, dst: &mut [F128; 4]) {
        // SAFETY: both are 32 bytes.
        let [c0, c1] = self.0.map(|v| unsafe { std::mem::transmute::<__m256i, [u64; 4]>(v) });
        *dst = std::array::from_fn(|i| F128::new(c0[i], c1[i]));
    }

    pub fn to_array(self) -> [F128; 4] {
        let mut out = [F128::ZERO; 4];
        self.store(&mut out);
        out
    }

    /// The four lane-wise products, unreduced.
    #[inline(always)]
    pub fn mul_unreduced(self, rhs: Self) -> Mixed4 {
        Mixed4 {
            even: karatsuba::<0x00>(self.0, rhs.0),
            odd: karatsuba::<0x11>(self.0, rhs.0),
        }
    }

    /// The lane-wise products, summed over the lanes and left unreduced. Karatsuba's products are summed
    /// before their one fold.
    #[inline(always)]
    pub fn mul_sum(self, rhs: Self) -> Sum4 {
        let both = |x: __m256i, y: __m256i| xor(clmul::<0x00>(x, y), clmul::<0x11>(x, y));
        let ([a0, a1], [b0, b1]) = (self.0, rhs.0);
        let (m0, m1, m01) = (both(a0, b0), both(a1, b1), both(xor(a0, a1), xor(b0, b1)));
        // SAFETY: the module's cfg enables avx2.
        Sum4(fold(m0, m1, m01, xor, |p| unsafe { times_x256(p) }))
    }
}

impl Mul for F128x4 {
    type Output = Self;
    #[inline(always)]
    fn mul(self, rhs: Self) -> Self {
        self.mul_unreduced(rhs).reduce()
    }
}

impl Sum4 {
    // SAFETY: an all-zero bit pattern is a valid `__m256i`.
    pub const ZERO: Self = Self(unsafe { std::mem::zeroed() });

    /// The lane sum, reduced.
    #[inline]
    pub fn reduce(self) -> F128 {
        let coeffs = self.0.map(|v| {
            // SAFETY: both are 32 bytes.
            let w: [u64; 4] = unsafe { std::mem::transmute(v) };
            [w[0] ^ w[2], w[1] ^ w[3]]
        });
        F128Unreduced::from_coeffs(coeffs).reduce()
    }
}

impl BitXorAssign for Sum4 {
    #[inline(always)]
    fn bitxor_assign(&mut self, rhs: Self) {
        self.0 = std::array::from_fn(|k| xor(self.0[k], rhs.0[k]));
    }
}

impl BitXor for Sum4 {
    type Output = Self;
    #[inline(always)]
    fn bitxor(mut self, rhs: Self) -> Self {
        self ^= rhs;
        self
    }
}

/// The embedding of the base field.
impl From<F64x4> for F128x4 {
    #[inline(always)]
    fn from(k: F64x4) -> Self {
        // SAFETY: the module's cfg enables avx2.
        Self([k.0, unsafe { _mm256_setzero_si256() }])
    }
}

impl Add for F128x4 {
    type Output = Self;
    #[inline(always)]
    fn add(self, rhs: Self) -> Self {
        Self(std::array::from_fn(|k| xor(self.0[k], rhs.0[k])))
    }
}

impl Mixed4 {
    // SAFETY: an all-zero bit pattern is a valid `__m256i`.
    pub const ZERO: Self = Self {
        even: unsafe { std::mem::zeroed() },
        odd: unsafe { std::mem::zeroed() },
    };

    /// Add `c[i] · k[i]` to lane `i`.
    #[inline(always)]
    pub fn add(&mut self, c: F128x4, k: F64x4) {
        for i in 0..2 {
            self.even[i] = xor(self.even[i], clmul::<0x00>(c.0[i], k.0));
            self.odd[i] = xor(self.odd[i], clmul::<0x11>(c.0[i], k.0));
        }
    }

    /// The sum of the four lanes, reduced once.
    #[inline]
    pub fn sum(self) -> F128 {
        let coeffs = std::array::from_fn(|i| {
            let v = xor(self.even[i], self.odd[i]);
            // SAFETY: the module's cfg enables avx2, and a vector and two qwords hold the same bits.
            unsafe {
                std::mem::transmute::<__m128i, [u64; 2]>(_mm_xor_si128(
                    _mm256_castsi256_si128(v),
                    _mm256_extracti128_si256::<1>(v),
                ))
            }
        });
        F128Unreduced::from_coeffs(coeffs).reduce()
    }

    #[inline(always)]
    pub fn reduce(self) -> F128x4 {
        // SAFETY: the module's cfg enables avx2.
        F128x4(std::array::from_fn(|i| unsafe {
            reduce_halves(self.even[i], self.odd[i])
        }))
    }
}

impl BitXorAssign for Mixed4 {
    #[inline(always)]
    fn bitxor_assign(&mut self, rhs: Self) {
        for i in 0..2 {
            self.even[i] = xor(self.even[i], rhs.even[i]);
            self.odd[i] = xor(self.odd[i], rhs.odd[i]);
        }
    }
}

/// Two `E` elements in one register as they lie in memory: 128-bit lane `i` is `[c0, c1]` of element `i`.
///
/// Products keep this layout from load to store, where the plane form of [`F128x4`] transposes on both sides.
#[derive(Clone, Copy, Debug)]
#[repr(transparent)]
pub struct F128x2(__m256i);

/// Two `K` elements in one register, each repeated across its 128-bit lane, so that it meets either coefficient of
/// the [`F128x2`] lane it multiplies.
#[derive(Clone, Copy, Debug)]
#[repr(transparent)]
pub struct F64x2(__m256i);

/// A [`F128x2`] multiplier with `c0 + c1` of each lane in its low qword, the operand Karatsuba's middle product reads.
#[derive(Clone, Copy, Debug)]
pub struct Mul2 {
    v: __m256i,
    s: __m256i,
}

/// Unreduced sums of [`F128x2`] products: the Karatsuba partials `a0 b0`, `a1 b1` and `(a0 + a1)(b0 + b1)` of each
/// lane, y-folded once at the reduction.
#[derive(Clone, Copy, Debug)]
pub struct Prod2 {
    p0: __m256i,
    p1: __m256i,
    p01: __m256i,
}

/// Unreduced sums of mixed products `e * k`: the coefficients of `y^0` and `y^1` of each lane.
#[derive(Clone, Copy, Debug)]
pub struct Mixed2 {
    d0: __m256i,
    d1: __m256i,
}

/// `[c1, c0]` of each lane: the two qwords swapped.
#[inline(always)]
fn swap_qwords(v: __m256i) -> __m256i {
    // SAFETY: the module's cfg enables avx2.
    unsafe { _mm256_shuffle_epi32::<0x4E>(v) }
}

/// The 128-bit lanes `vperm2i128` picks with immediate `I`: per half of the result, `0..=3` names `a.lo`, `a.hi`,
/// `b.lo`, `b.hi`, and bit 3 zeroes it.
#[inline(always)]
fn select<const I: i32>(a: __m256i, b: __m256i) -> __m256i {
    // SAFETY: the module's cfg enables avx2.
    unsafe { _mm256_permute2x128_si256::<I>(a, b) }
}

impl F128x2 {
    pub const ZERO: Self = Self(
        // SAFETY: an all-zero bit pattern is a valid `__m256i`.
        unsafe { std::mem::zeroed() },
    );

    #[inline(always)]
    pub fn load(e: &[F128; 2]) -> Self {
        // SAFETY: the module's cfg enables avx2; two elements are 32 bytes.
        Self(unsafe { _mm256_loadu_si256(e.as_ptr().cast()) })
    }

    #[inline(always)]
    pub fn store(self, dst: &mut [F128; 2]) {
        // SAFETY: the module's cfg enables avx2; two elements are 32 bytes.
        unsafe { _mm256_storeu_si256(dst.as_mut_ptr().cast(), self.0) }
    }

    #[inline(always)]
    pub fn new(lo: F128, hi: F128) -> Self {
        // SAFETY: the module's cfg enables avx2.
        Self(unsafe { _mm256_set_epi64x(hi.c1 as i64, hi.c0 as i64, lo.c1 as i64, lo.c0 as i64) })
    }

    #[inline(always)]
    pub fn splat(e: F128) -> Self {
        Self::new(e, e)
    }

    /// The lanes [`select`] picks from `a` and `b` with immediate `I`.
    #[inline(always)]
    pub fn select<const I: i32>(a: Self, b: Self) -> Self {
        Self(select::<I>(a.0, b.0))
    }

    /// The coefficients `c0` of two pairs of lanes, then their coefficients `c1`, in lane order.
    #[inline(always)]
    pub fn limbs(a: Self, b: Self) -> (F64x4, F64x4) {
        // SAFETY: the module's cfg enables avx2.
        unsafe {
            (
                F64x4(_mm256_permute4x64_epi64::<0xD8>(_mm256_unpacklo_epi64(a.0, b.0))),
                F64x4(_mm256_permute4x64_epi64::<0xD8>(_mm256_unpackhi_epi64(a.0, b.0))),
            )
        }
    }

    /// This pair as a multiplier.
    #[inline(always)]
    pub fn factor(self) -> Mul2 {
        Mul2 {
            v: self.0,
            s: xor(self.0, swap_qwords(self.0)),
        }
    }

    /// The lane-wise products by `m`, unreduced.
    #[inline(always)]
    pub fn mul_unreduced(self, m: Mul2) -> Prod2 {
        let s = xor(self.0, swap_qwords(self.0));
        Prod2 {
            p0: clmul::<0x00>(self.0, m.v),
            p1: clmul::<0x11>(self.0, m.v),
            p01: clmul::<0x00>(s, m.s),
        }
    }

    /// The lane-wise mixed products by `k`, unreduced.
    #[inline(always)]
    pub fn mul_base_unreduced(self, k: F64x2) -> Mixed2 {
        // Immediate 0x01 multiplies the high qword of the first operand by the low qword of the second.
        Mixed2 {
            d0: clmul::<0x00>(self.0, k.0),
            d1: clmul::<0x01>(self.0, k.0),
        }
    }
}

impl Add for F128x2 {
    type Output = Self;
    #[inline(always)]
    fn add(self, rhs: Self) -> Self {
        Self(xor(self.0, rhs.0))
    }
}

/// The embedding of the base field.
impl From<F64x2> for F128x2 {
    #[inline(always)]
    fn from(k: F64x2) -> Self {
        // SAFETY: the module's cfg enables avx2.
        Self(unsafe { _mm256_blend_epi32::<0xCC>(k.0, _mm256_setzero_si256()) })
    }
}

impl F64x2 {
    #[inline(always)]
    pub fn new(lo: F64, hi: F64) -> Self {
        // SAFETY: the module's cfg enables avx2.
        Self(unsafe { _mm256_set_epi64x(hi.0 as i64, hi.0 as i64, lo.0 as i64, lo.0 as i64) })
    }

    #[inline(always)]
    pub fn splat(k: F64) -> Self {
        Self::new(k, k)
    }

    /// The lanes [`select`] picks from `a` and `b` with immediate `I`.
    #[inline(always)]
    pub fn select<const I: i32>(a: Self, b: Self) -> Self {
        Self(select::<I>(a.0, b.0))
    }
}

impl Add for F64x2 {
    type Output = Self;
    #[inline(always)]
    fn add(self, rhs: Self) -> Self {
        Self(xor(self.0, rhs.0))
    }
}

impl F64x4 {
    /// Lanes `0, 1` and lanes `2, 3`, each as a [`F64x2`].
    #[inline(always)]
    pub fn spread(self) -> [F64x2; 2] {
        // SAFETY: the module's cfg enables avx2.
        unsafe {
            [
                F64x2(_mm256_permute4x64_epi64::<0x50>(self.0)),
                F64x2(_mm256_permute4x64_epi64::<0xFA>(self.0)),
            ]
        }
    }

    #[inline(always)]
    pub fn store(self, dst: &mut [F64; 4]) {
        // SAFETY: the module's cfg enables avx2; four qwords are 32 bytes.
        unsafe { _mm256_storeu_si256(dst.as_mut_ptr().cast(), self.0) }
    }
}

impl Prod2 {
    /// Both lanes reduced.
    #[inline(always)]
    pub fn reduce(self) -> F128x2 {
        // SAFETY: the module's cfg enables avx2.
        let [d0, d1] = fold(self.p0, self.p1, self.p01, xor, |p| unsafe { times_x256(p) });
        // SAFETY: the module's cfg enables avx2.
        F128x2(unsafe { reduce_halves(d0, d1) })
    }
}

impl BitXorAssign for Prod2 {
    #[inline(always)]
    fn bitxor_assign(&mut self, rhs: Self) {
        self.p0 = xor(self.p0, rhs.p0);
        self.p1 = xor(self.p1, rhs.p1);
        self.p01 = xor(self.p01, rhs.p01);
    }
}

impl Mixed2 {
    /// Both lanes reduced.
    #[inline(always)]
    pub fn reduce(self) -> F128x2 {
        // SAFETY: the module's cfg enables avx2.
        F128x2(unsafe { reduce_halves(self.d0, self.d1) })
    }
}

impl BitXorAssign for Mixed2 {
    #[inline(always)]
    fn bitxor_assign(&mut self, rhs: Self) {
        self.d0 = xor(self.d0, rhs.d0);
        self.d1 = xor(self.d1, rhs.d1);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::test_rng::Rng;

    #[test]
    fn lanes_match_scalar() {
        let mut rng = Rng::new(23);
        for _ in 0..200 {
            let (c, d, e) = (rng.ext(), rng.ext(), rng.ext());
            let mut k: [F64; 4] = std::array::from_fn(|_| F64(rng.ext().c0));
            k[2] = F64(u64::MAX);
            let l: [F64; 4] = std::array::from_fn(|_| F64(rng.ext().c1));
            let mut acc = Mixed4::ZERO;
            acc.add(F128x4::splat(c), F64x4::load(&k));
            acc.add(F128x4::splat(d), F64x4::new(k) * F64x4::load(&l));
            let want = std::array::from_fn(|i| c.mul_base(k[i]) + d.mul_base(k[i] * l[i]) + e);
            assert_eq!((acc.reduce() + F128x4::splat(e)).to_array(), want);
            assert_eq!((F64x4::load(&k) * F64x4::splat(l[0])).to_array(), k.map(|k| k * l[0]));
        }
    }

    #[test]
    fn products_match_scalar() {
        let mut rng = Rng::new(29);
        for _ in 0..200 {
            let mut a: [F128; 4] = std::array::from_fn(|_| rng.ext());
            let b: [F128; 4] = std::array::from_fn(|_| rng.ext());
            a[1] = F128::new(u64::MAX, u64::MAX);
            a[3] = F128::new(1 << 63, 1 << 63);
            let (va, vb) = (F128x4::load(&a), F128x4::load(&b));
            assert_eq!(va.to_array(), a);
            assert_eq!((va + vb).to_array(), std::array::from_fn(|i| a[i] + b[i]));
            assert_eq!(
                va.mul_unreduced(vb).reduce().to_array(),
                std::array::from_fn(|i| a[i] * b[i])
            );
            let mut acc = va.mul_unreduced(vb);
            acc ^= vb.mul_unreduced(va);
            acc ^= va.mul_unreduced(va);
            assert_eq!(acc.sum(), (0..4).map(|i| a[i] * a[i]).sum());
            let k: [F64; 4] = std::array::from_fn(|_| F64(rng.next_u64()));
            assert_eq!(F128x4::from(F64x4::new(k)).to_array(), k.map(F128::from));
        }
    }

    #[test]
    fn pairs_match_scalar() {
        let arr = |v: F128x2| {
            let mut out = [F128::ZERO; 2];
            v.store(&mut out);
            out
        };
        let mut rng = Rng::new(31);
        for _ in 0..200 {
            let (a, b, c, d): ([F128; 2], [F128; 2], [F128; 2], [F128; 2]) = (
                [rng.ext(), F128::new(u64::MAX, 1 << 63)],
                [rng.ext(), rng.ext()],
                [rng.ext(), rng.ext()],
                [rng.ext(), rng.ext()],
            );
            let k: [F64; 4] = std::array::from_fn(|_| F64(rng.next_u64()));
            let (va, vb, vc, vd) = (F128x2::load(&a), F128x2::load(&b), F128x2::load(&c), F128x2::load(&d));
            let mut acc = va.mul_unreduced(vb.factor());
            acc ^= vc.mul_unreduced(vd.factor());
            assert_eq!(arr(acc.reduce()), std::array::from_fn(|i| a[i] * b[i] + c[i] * d[i]));
            let [k01, k23] = F64x4::load(&k).spread();
            let mut mixed = va.mul_base_unreduced(k01);
            mixed ^= vb.mul_base_unreduced(k23);
            let want = std::array::from_fn(|i| a[i].mul_base(k[i]) + b[i].mul_base(k[2 + i]) + F128::from(k[i]));
            assert_eq!(arr(mixed.reduce() + F128x2::from(k01)), want);
            assert_eq!(arr(F128x2::select::<0x21>(va, vb)), [a[1], b[0]]);
            let (lo, hi) = F128x2::limbs(va, vb);
            assert_eq!(lo.to_array(), [a[0].c0, a[1].c0, b[0].c0, b[1].c0].map(F64));
            assert_eq!(hi.to_array(), [a[0].c1, a[1].c1, b[0].c1, b[1].c1].map(F64));
            let mut stored = [F64::ZERO; 4];
            F64x4::load(&k).store(&mut stored);
            assert_eq!(stored, k);
            assert_eq!(
                arr(F128x2::new(a[0], a[1]) + F128x2::splat(c[0])),
                [a[0] + c[0], a[1] + c[0]]
            );
            let sum = F64x2::new(k[0], k[1]) + F64x2::select::<0x01>(F64x2::splat(k[2]), F64x2::splat(k[2]));
            assert_eq!(arr(F128x2::from(sum)), [k[0] + k[2], k[1] + k[2]].map(F128::from));
        }
    }
}
