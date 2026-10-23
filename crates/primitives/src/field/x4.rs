//! Four lanes of mixed products `c · k`, `c ∈ E` and `k ∈ K`, in YMM registers, for a machine
//! with VPCLMULQDQ but no AVX-512: the 256-bit counterpart of the AVX-512 `x8`'s `F64x8` and
//! `Mixed8`, which is all the leaf builder needs.

use core::arch::x86_64::*;
use core::ops::Mul;

use super::gf2_64::F64;
use super::gf2_64x3::F192;
use super::gf2_64x3::x86_64::reduce_lanes256;

/// Four `K` elements in one register.
#[derive(Clone, Copy, Debug)]
pub struct F64x4(__m256i);

/// An `E` element in every lane: register `k` holds coefficient `k`.
#[derive(Clone, Copy, Debug)]
pub struct Splat4([__m256i; 3]);

/// Per-lane unreduced sums of mixed products, the even lanes' 128-bit partials apart from the odd ones'.
#[derive(Clone, Copy, Debug)]
pub struct Mixed4 {
    even: [__m256i; 3],
    odd: [__m256i; 3],
}

#[inline(always)]
fn xor(a: __m256i, b: __m256i) -> __m256i {
    // SAFETY: the module's cfg enables avx2.
    unsafe { _mm256_xor_si256(a, b) }
}

/// Qword `i` is the reduction of lane `i`'s 128-bit partial, `even` holding lanes 0 and 2, `odd` 1 and 3.
#[inline(always)]
fn reduce_halves(even: __m256i, odd: __m256i) -> __m256i {
    // SAFETY: the module's cfg enables avx2.
    unsafe { reduce_lanes256(_mm256_unpacklo_epi64(even, odd), _mm256_unpackhi_epi64(even, odd)) }
}

impl F64x4 {
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

impl Splat4 {
    #[inline(always)]
    pub fn new(e: F192) -> Self {
        // SAFETY: the module's cfg enables avx2.
        unsafe {
            Self([
                _mm256_set1_epi64x(e.c0 as i64),
                _mm256_set1_epi64x(e.c1 as i64),
                _mm256_set1_epi64x(e.c2 as i64),
            ])
        }
    }
}

impl Mixed4 {
    // SAFETY: an all-zero bit pattern is a valid `__m256i`.
    pub const ZERO: Self = Self {
        even: unsafe { std::mem::zeroed() },
        odd: unsafe { std::mem::zeroed() },
    };

    /// Add `c · k[i]` to lane `i`.
    #[inline(always)]
    pub fn add(&mut self, c: Splat4, k: F64x4) {
        for i in 0..3 {
            // SAFETY: the module's cfg enables avx2 and vpclmulqdq. Immediate bit 4 picks
            // the scalar's odd qword; the splat is the same in both.
            unsafe {
                self.even[i] = xor(self.even[i], _mm256_clmulepi64_epi128::<0x00>(c.0[i], k.0));
                self.odd[i] = xor(self.odd[i], _mm256_clmulepi64_epi128::<0x10>(c.0[i], k.0));
            }
        }
    }

    /// Each lane's sum, reduced, plus `constant`.
    #[inline(always)]
    pub fn reduce(self, constant: F192) -> [F192; 4] {
        // SAFETY: both are 32 bytes.
        let [c0, c1, c2] = std::array::from_fn(|i| unsafe {
            std::mem::transmute::<__m256i, [u64; 4]>(reduce_halves(self.even[i], self.odd[i]))
        });
        std::array::from_fn(|i| F192::new(c0[i], c1[i], c2[i]) + constant)
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
            acc.add(Splat4::new(c), F64x4::load(&k));
            acc.add(Splat4::new(d), F64x4::load(&k) * F64x4::load(&l));
            let want = std::array::from_fn(|i| c.mul_base(k[i]) + d.mul_base(k[i] * l[i]) + e);
            assert_eq!(acc.reduce(e), want);
            assert_eq!((F64x4::load(&k) * F64x4::splat(l[0])).to_array(), k.map(|k| k * l[0]));
        }
    }
}
