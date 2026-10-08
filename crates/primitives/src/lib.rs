//! Shared primitives: Plonky3 fields, bit transposes, multilinear helpers, and
//! small integer utilities.

pub mod bit_fold;
pub mod bits;
pub use multilinear::{G, PHI_8_TABLE_192, dot_base, g_pow, int_index_mle, mul_base8, mul2, mul4, phi8_192, powers};
#[cfg(all(target_arch = "x86_64", target_feature = "vpclmulqdq", target_feature = "avx2"))]
pub use p3_binary_field::PackedPoly192 as F192x4;
pub use p3_binary_field::{Poly64 as F64, Poly192 as F192, Rijndael8b as F8};
pub use p3_field::extension::HasFrobenius;
pub use p3_field::{Algebra, Field, PackedFieldExtension, PackedValue, PrimeCharacteristicRing};
pub mod hash;
pub mod multilinear;
pub mod stream;

use std::mem::MaybeUninit;

#[cfg(feature = "test-util")]
pub mod test_util;

/// Format an integer with comma-separated groups of three decimal digits.
///
/// Signed and unsigned integers are accepted by reference.
/// A leading sign is preserved.
///
/// ```
/// use primitives::pretty_integer;
///
/// assert_eq!(pretty_integer(&16_769_432), "16,769,432");
/// assert_eq!(pretty_integer(&-12_345), "-12,345");
/// ```
pub fn pretty_integer(value: &(impl ToString + ?Sized)) -> String {
    let raw = value.to_string();
    let (sign, digits) = match raw.as_bytes().first() {
        Some(b'+' | b'-') => raw.split_at(1),
        _ => ("", raw.as_str()),
    };

    // Keep misuse benign: callers are expected to pass integers, but returning
    // the original representation is more useful than mangling another type.
    if !digits.bytes().all(|b| b.is_ascii_digit()) {
        return raw;
    }

    let separators = digits.len().saturating_sub(1) / 3;
    let mut out = String::with_capacity(raw.len() + separators);
    out.push_str(sign);
    for (i, byte) in digits.bytes().enumerate() {
        if i != 0 && (digits.len() - i).is_multiple_of(3) {
            out.push(',');
        }
        out.push(byte as char);
    }
    out
}

/// Format a finite floating-point value with a grouped integer part and at
/// most three meaningful fractional digits. Leading zeroes after the decimal
/// point do not consume that budget, so tiny nonzero values remain visible.
/// The fractional part is rounded and trailing zeroes are omitted; non-finite
/// values retain Rust's standard spelling.
///
/// ```
/// use primitives::pretty_f64;
///
/// assert_eq!(pretty_f64(2.186_834_667), "2.187");
/// assert_eq!(pretty_f64(12_345.6), "12,345.6");
/// ```
pub fn pretty_f64(value: f64) -> String {
    if !value.is_finite() {
        return value.to_string();
    }

    let magnitude = value.abs();
    let precision = if magnitude == 0.0 || magnitude >= 1.0 {
        3
    } else {
        // Keep the first three nonzero-place digits: 0.001234 needs five
        // decimal places, while 0.000000000012345 needs thirteen.
        ((-magnitude.log10().floor()) as usize).saturating_add(2)
    };
    let mut raw = format!("{value:.precision$}");
    while raw.contains('.') && raw.ends_with('0') {
        raw.pop();
    }
    if raw.ends_with('.') {
        raw.pop();
    }
    if raw == "-0" {
        return "0".to_string();
    }

    let (integer, fraction) = raw
        .split_once('.')
        .map_or((raw.as_str(), None), |(integer, fraction)| (integer, Some(fraction)));
    let mut out = pretty_integer(integer);
    if let Some(fraction) = fraction {
        out.push('.');
        out.push_str(fraction);
    }
    out
}

/// `log2` of a power of two (panics otherwise).
pub fn log2_strict_usize(n: usize) -> usize {
    assert!(n.is_power_of_two(), "not a power of two: {n}");
    n.trailing_zeros() as usize
}

/// `ceil(log2(n))`, defined as 0 for `n <= 1`.
pub const fn log2_ceil_usize(n: usize) -> usize {
    if n <= 1 { 0 } else { (n - 1).ilog2() as usize + 1 }
}

/// Unwritten slots viewed as elements, for a kernel typed over elements that writes each slot before reading it.
///
/// - It skips the zero-fill, which would cost one more pass over memory.
/// - The slots become a vector only once every one is written.
/// - A kernel that can take the slots themselves should, and needs no view.
///
/// # Safety
///
/// - Nothing may read a slot through the view before writing it.
/// - The view refers to memory not yet written, which the language leaves open; Miri accepts it while nothing reads it.
///
/// Only plain-data elements are allowed, since a store through the view drops the old value:
///
/// ```compile_fail
/// let mut slots = [std::mem::MaybeUninit::<String>::uninit()];
/// unsafe { primitives::write_only(&mut slots) };
/// ```
pub const unsafe fn write_only<T: Copy>(slots: &mut [MaybeUninit<T>]) -> &mut [T] {
    // SAFETY: a slot has its element's layout, and the caller writes every slot before reading it.
    unsafe { &mut *(slots as *mut [MaybeUninit<T>] as *mut [T]) }
}

#[cfg(test)]
mod formatting_tests {
    use super::{pretty_f64, pretty_integer};

    #[test]
    fn pretty_integer_groups_decimal_digits() {
        assert_eq!(pretty_integer(&0), "0");
        assert_eq!(pretty_integer(&12), "12");
        assert_eq!(pretty_integer(&999), "999");
        assert_eq!(pretty_integer(&1_000), "1,000");
        assert_eq!(pretty_integer(&16_769_432), "16,769,432");
        assert_eq!(
            pretty_integer(&u128::MAX),
            "340,282,366,920,938,463,463,374,607,431,768,211,455"
        );
        assert_eq!(pretty_integer(&-12_345), "-12,345");
        assert_eq!(pretty_integer("+123456"), "+123,456");
    }

    #[test]
    fn pretty_f64_rounds_groups_and_trims() {
        assert_eq!(pretty_f64(2.186_834_667), "2.187");
        assert_eq!(pretty_f64(12_345.678_9), "12,345.679");
        assert_eq!(pretty_f64(12_345.0), "12,345");
        assert_eq!(pretty_f64(-12_345.6), "-12,345.6");
        assert_eq!(pretty_f64(-0.0), "0");
        assert_eq!(pretty_f64(0.000_000_000_012_345), "0.0000000000123");
        assert_eq!(pretty_f64(f64::INFINITY), "inf");
        assert_eq!(pretty_f64(f64::NEG_INFINITY), "-inf");
        assert_eq!(pretty_f64(f64::NAN), "NaN");
    }
}
