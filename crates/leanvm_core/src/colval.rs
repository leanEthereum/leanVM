//! Column operations shared by the `F64` joining round and subsequent `F192` rounds.

use primitives::field::{F64, F192, F192Unreduced, mul_base8, mul4};
#[cfg(all(target_arch = "x86_64", target_feature = "vpclmulqdq", target_feature = "avx512f"))]
use primitives::field::{Weights8, dot_base};
use std::ops::{Add, BitXor, BitXorAssign, Mul};

/// A row holding `n` columns, padded with zero columns to whole groups of eight.
pub const fn padded_width(n: usize) -> usize {
    n.next_multiple_of(8)
}

/// Coefficients packed for [`dot_base`], zero-padded to [`padded_width`] columns.
///
/// Against `K` words they are packed as they are. Against `E` values each is
/// `w, y·w, y²·w`, which meet the value's three `K` words: an `E` product is
/// three mixed ones, and the row is read as the words it is stored as.
///
/// AVX-512 only, where [`dot_base`] takes eight columns in six CLMULs; elsewhere a
/// form's linear part stays [`ColVal::dot_unreduced`].
#[cfg(all(target_arch = "x86_64", target_feature = "vpclmulqdq", target_feature = "avx512f"))]
#[derive(Clone, Debug)]
pub struct PackedCoeffs {
    base: Vec<Weights8>,
    ext: Vec<Weights8>,
}

#[cfg(all(target_arch = "x86_64", target_feature = "vpclmulqdq", target_feature = "avx512f"))]
impl PackedCoeffs {
    pub fn new(coeffs: &[F192]) -> Self {
        let mut padded = coeffs.to_vec();
        padded.resize(padded_width(coeffs.len()), F192::ZERO);
        let y2 = F192::Y * F192::Y;
        let ext: Vec<F192> = padded.iter().flat_map(|&w| [w, w * F192::Y, w * y2]).collect();
        let pack = |w: &[F192]| w.as_chunks::<8>().0.iter().map(Weights8::new).collect();
        Self {
            base: pack(&padded),
            ext: pack(&ext),
        }
    }

    /// The padded width a row needs.
    pub const fn width(&self) -> usize {
        8 * self.base.len()
    }
}

/// A value a constraint reads out of a column.
pub trait ColVal: Copy + Send + Sync + Add<Output = Self> + Mul<Output = Self> {
    const ZERO: Self;

    /// Where this column's products XOR-accumulate before the one reduction that
    /// ends a form.
    type Unreduced: Copy + Send + Sync + BitXor<Output = Self::Unreduced> + BitXorAssign;

    /// Times an `E` value: an `η`-power, a bus coefficient, a machine word.
    fn mul_e(self, e: F192) -> F192;

    /// The same product, left for the caller to accumulate.
    fn mul_e_unreduced(self, e: F192) -> Self::Unreduced;

    /// An already-reduced `E` value as an accumulator term; exact, because
    /// reducing a reduced value fixes it.
    fn lift(e: F192) -> Self::Unreduced;

    fn reduce(acc: Self::Unreduced) -> F192;

    /// `Σ coeffs[i]·vals[i]`, unreduced.
    fn dot_unreduced(coeffs: &[F192], vals: &[Self]) -> Self::Unreduced;

    /// The same over packed coefficients; `vals` holds exactly `coeffs.width()` values.
    #[cfg(all(target_arch = "x86_64", target_feature = "vpclmulqdq", target_feature = "avx512f"))]
    fn dot_packed(coeffs: &PackedCoeffs, vals: &[Self]) -> Self::Unreduced;

    /// `vals[i]·e` for eight values at once.
    fn mul_e8(vals: [Self; 8], e: F192) -> [F192; 8];

    /// `constant + Σ coeffs[i]·vals[i]`, one reduction for the whole slice.
    #[inline(always)]
    fn dot(coeffs: &[F192], vals: &[Self], constant: F192) -> F192 {
        Self::reduce(Self::dot_unreduced(coeffs, vals) ^ Self::lift(constant))
    }
}

impl ColVal for F64 {
    const ZERO: Self = Self::ZERO;

    type Unreduced = F192Unreduced;

    #[inline(always)]
    fn mul_e(self, e: F192) -> F192 {
        e.mul_base(self)
    }

    #[inline(always)]
    fn mul_e_unreduced(self, e: F192) -> Self::Unreduced {
        e.mul_base_unreduced(self)
    }

    #[inline(always)]
    fn lift(e: F192) -> Self::Unreduced {
        e.into()
    }

    #[inline(always)]
    fn reduce(acc: Self::Unreduced) -> F192 {
        acc.reduce()
    }

    #[inline(always)]
    fn dot_unreduced(coeffs: &[F192], vals: &[Self]) -> Self::Unreduced {
        coeffs
            .iter()
            .zip(vals)
            .fold(F192Unreduced::ZERO, |acc, (&w, &v)| acc ^ w.mul_base_unreduced(v))
    }

    #[cfg(all(target_arch = "x86_64", target_feature = "vpclmulqdq", target_feature = "avx512f"))]
    #[inline(always)]
    fn dot_packed(coeffs: &PackedCoeffs, vals: &[Self]) -> Self::Unreduced {
        dot_base(&coeffs.base, vals)
    }

    #[inline(always)]
    fn mul_e8(vals: [Self; 8], e: F192) -> [F192; 8] {
        mul_base8(e, vals)
    }
}

impl ColVal for F192 {
    const ZERO: Self = Self::ZERO;

    type Unreduced = F192Unreduced;

    #[inline(always)]
    fn mul_e(self, e: F192) -> F192 {
        self * e
    }

    #[inline(always)]
    fn mul_e_unreduced(self, e: F192) -> Self::Unreduced {
        self.mul_unreduced(e)
    }

    #[inline(always)]
    fn lift(e: F192) -> Self::Unreduced {
        e.into()
    }

    #[inline(always)]
    fn reduce(acc: Self::Unreduced) -> F192 {
        acc.reduce()
    }

    #[inline(always)]
    fn dot_unreduced(coeffs: &[F192], vals: &[Self]) -> Self::Unreduced {
        coeffs
            .iter()
            .zip(vals)
            .fold(F192Unreduced::ZERO, |acc, (&w, &v)| acc ^ w.mul_unreduced(v))
    }

    #[cfg(all(target_arch = "x86_64", target_feature = "vpclmulqdq", target_feature = "avx512f"))]
    #[inline(always)]
    fn dot_packed(coeffs: &PackedCoeffs, vals: &[Self]) -> Self::Unreduced {
        // SAFETY: `F192` is three `u64`s under `repr(C)` and `F64` one under `repr(transparent)`.
        let words = unsafe { std::slice::from_raw_parts(vals.as_ptr().cast::<F64>(), 3 * vals.len()) };
        dot_base(&coeffs.ext, words)
    }

    #[inline(always)]
    fn mul_e8(vals: [Self; 8], e: F192) -> [F192; 8] {
        let lo = mul4([vals[0], vals[1], vals[2], vals[3]], [e; 4]);
        let hi = mul4([vals[4], vals[5], vals[6], vals[7]], [e; 4]);
        [lo[0], lo[1], lo[2], lo[3], hi[0], hi[1], hi[2], hi[3]]
    }
}
