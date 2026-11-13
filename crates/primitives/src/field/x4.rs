//! Four lanes of products in YMM registers, for a machine with VPCLMULQDQ but no AVX-512: the
//! 256-bit counterpart of the AVX-512 `x8`'s `F64x8`, `F128x8` and `Mixed8` for the leaf builder,
//! and the halves of the eight-lane `f128x8` types.

use core::arch::x86_64::*;
use core::ops::{Add, BitXorAssign, Mul};

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

#[inline(always)]
fn xor(a: __m256i, b: __m256i) -> __m256i {
    // SAFETY: the module's cfg enables avx2.
    unsafe { _mm256_xor_si256(a, b) }
}

/// The products of the even lanes (`I = 0x00`) or the odd ones (`I = 0x11`) of two registers.
#[inline(always)]
fn clmul<const I: i32>(a: __m256i, b: __m256i) -> __m256i {
    // SAFETY: the module's cfg enables vpclmulqdq.
    unsafe { _mm256_clmulepi64_epi128::<I>(a, b) }
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
        // SAFETY: the module's cfg enables avx2 and vpclmulqdq.
        Self(unsafe {
            reduce_halves(
                _mm256_clmulepi64_epi128::<0x00>(self.0, rhs.0),
                _mm256_clmulepi64_epi128::<0x11>(self.0, rhs.0),
            )
        })
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
}
