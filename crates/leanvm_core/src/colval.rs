//! Column operations shared by the `F64` joining round and subsequent `F192` rounds.

use primitives::{Field, PrimeCharacteristicRing};

#[cfg(all(target_arch = "x86_64", target_feature = "vpclmulqdq", target_feature = "avx512f"))]
use primitives::dot_base;
use primitives::{F64, F192, mul_base8, mul4};

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
/// Eight-column groups let Plonky3 defer reduction within each mixed dot product.
#[cfg(all(target_arch = "x86_64", target_feature = "vpclmulqdq", target_feature = "avx512f"))]
#[derive(Clone, Debug)]
pub struct PackedCoeffs {
    base: Vec<[F192; 8]>,
    ext: Vec<[F192; 8]>,
}

#[cfg(all(target_arch = "x86_64", target_feature = "vpclmulqdq", target_feature = "avx512f"))]
impl PackedCoeffs {
    pub fn new(coeffs: &[F192]) -> Self {
        let mut padded = coeffs.to_vec();
        padded.resize(padded_width(coeffs.len()), F192::ZERO);
        let y2 = F192::new([F64::ZERO, F64::ONE, F64::ZERO]) * F192::new([F64::ZERO, F64::ONE, F64::ZERO]);
        let ext: Vec<F192> = padded
            .iter()
            .flat_map(|&w| [w, w * F192::new([F64::ZERO, F64::ONE, F64::ZERO]), w * y2])
            .collect();
        let pack = |w: &[F192]| w.as_chunks::<8>().0.to_vec();
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
pub trait ColVal: Field {
    /// Times an `E` value: an `η`-power, a bus coefficient, a machine word.
    fn mul_e(self, e: F192) -> F192;

    /// `Σ coeffs[i]·vals[i]`.
    fn dot_products(coeffs: &[F192], vals: &[Self]) -> F192;

    /// The same over packed coefficients; `vals` holds exactly `coeffs.width()` values.
    #[cfg(all(target_arch = "x86_64", target_feature = "vpclmulqdq", target_feature = "avx512f"))]
    fn dot_packed(coeffs: &PackedCoeffs, vals: &[Self]) -> F192;

    /// `vals[i]·e` for eight values at once.
    fn mul_e8(vals: [Self; 8], e: F192) -> [F192; 8];

    /// `constant + Σ coeffs[i]·vals[i]`.
    #[inline(always)]
    fn dot(coeffs: &[F192], vals: &[Self], constant: F192) -> F192 {
        Self::dot_products(coeffs, vals) + constant
    }
}

impl ColVal for F64 {
    #[inline(always)]
    fn mul_e(self, e: F192) -> F192 {
        e * self
    }

    #[inline(always)]
    fn dot_products(coeffs: &[F192], vals: &[Self]) -> F192 {
        coeffs.iter().zip(vals).fold(F192::ZERO, |acc, (&w, &v)| acc + (w * v))
    }

    #[cfg(all(target_arch = "x86_64", target_feature = "vpclmulqdq", target_feature = "avx512f"))]
    #[inline(always)]
    fn dot_packed(coeffs: &PackedCoeffs, vals: &[Self]) -> F192 {
        dot_base(&coeffs.base, vals)
    }

    #[inline(always)]
    fn mul_e8(vals: [Self; 8], e: F192) -> [F192; 8] {
        mul_base8(e, vals)
    }
}

impl ColVal for F192 {
    #[inline(always)]
    fn mul_e(self, e: F192) -> F192 {
        self * e
    }

    #[inline(always)]
    fn dot_products(coeffs: &[F192], vals: &[Self]) -> F192 {
        coeffs.iter().zip(vals).fold(Self::ZERO, |acc, (&w, &v)| acc + (w * v))
    }

    #[cfg(all(target_arch = "x86_64", target_feature = "vpclmulqdq", target_feature = "avx512f"))]
    #[inline(always)]
    fn dot_packed(coeffs: &PackedCoeffs, vals: &[Self]) -> F192 {
        // SAFETY: Plonky3 represents `Poly192` transparently over `[Poly64; 3]`.
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
