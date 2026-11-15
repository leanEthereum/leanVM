//! The stable prover's primitives: the fields and their one SIMD layer ([`field`]), Keccak-256 ([`hash`]), the
//! weighted bit fold ([`bit_fold`]), multilinear helpers ([`multilinear`]), the shared transcript on this field ([`transcript`]), and small integer and slice utilities.

pub mod bit_fold;
pub mod field;
pub mod hash;
pub mod multilinear;
pub mod transcript;

#[cfg(feature = "test-util")]
pub mod test_rng;

/// An integer with its decimal digits in comma-separated groups of three, a leading `-` kept.
///
/// ```
/// use stable_primitives::pretty_integer;
///
/// assert_eq!(pretty_integer(16_769_432), "16,769,432");
/// assert_eq!(pretty_integer(-12_345), "-12,345");
/// ```
pub fn pretty_integer(value: impl ToString) -> String {
    let raw = value.to_string();
    let (sign, digits) = raw.split_at(usize::from(raw.starts_with('-')));
    let mut out = String::from(sign);
    for (i, c) in digits.chars().enumerate() {
        if i != 0 && (digits.len() - i).is_multiple_of(3) {
            out.push(',');
        }
        out.push(c);
    }
    out
}

/// A float with a grouped integer part and at most three meaningful fractional digits, leading zeroes after the
/// point not counted, so tiny nonzero values stay visible; rounded, trailing zeroes trimmed, non-finite values in
/// Rust's spelling.
///
/// ```
/// use stable_primitives::pretty_f64;
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
        ((-magnitude.log10().floor()) as usize).saturating_add(2)
    };
    let raw = format!("{value:.precision$}");
    let raw = if raw.contains('.') {
        raw.trim_end_matches('0').trim_end_matches('.')
    } else {
        &raw
    };
    if raw == "-0" {
        return "0".into();
    }
    match raw.split_once('.') {
        Some((integer, fraction)) => format!("{}.{fraction}", pretty_integer(integer)),
        None => pretty_integer(raw),
    }
}

/// `log2` of a power of two (panics otherwise).
pub fn log2_strict_usize(n: usize) -> usize {
    assert!(n.is_power_of_two(), "not a power of two: {n}");
    n.trailing_zeros() as usize
}

/// `ceil(log2(n))`, defined as 0 for `n <= 1`.
pub fn log2_ceil_usize(n: usize) -> usize {
    if n <= 1 { 0 } else { (n - 1).ilog2() as usize + 1 }
}

/// Plain data: no padding, and every bit pattern is a valid value.
///
/// # Safety
///
/// Implement it only for such types.
pub unsafe trait Plain: Copy {}

// SAFETY: integers.
unsafe impl Plain for u8 {}
unsafe impl Plain for u64 {}
unsafe impl Plain for u128 {}
// SAFETY: an array of plain elements has no padding.
unsafe impl<T: Plain, const N: usize> Plain for [T; N] {}
// SAFETY: `repr(transparent)` over `u64`.
unsafe impl Plain for field::F64 {}
// SAFETY: `repr(C)` over two `u64`.
unsafe impl Plain for field::F128 {}
/// The same bytes as a slice of another plain type.
///
/// # Panics
///
/// If `B` is zero-sized, the slice is misaligned for `B`, or its byte length is not a multiple of `size_of::<B>()`.
pub fn cast_slice<A: Plain, B: Plain>(a: &[A]) -> &[B] {
    let (ptr, bytes) = (a.as_ptr().cast::<B>(), core::mem::size_of_val(a));
    assert!(
        size_of::<B>() != 0 && ptr.is_aligned() && bytes % size_of::<B>() == 0,
        "slice does not cast"
    );
    // SAFETY: both types are plain, so every byte is initialized and any pattern is valid; the checks above
    // cover alignment and length, and the lifetime is the borrow's.
    unsafe { core::slice::from_raw_parts(ptr, bytes / core::mem::size_of::<B>()) }
}

/// [`cast_slice`] of a mutable slice.
pub fn cast_slice_mut<A: Plain, B: Plain>(a: &mut [A]) -> &mut [B] {
    let (ptr, bytes) = (a.as_mut_ptr().cast::<B>(), core::mem::size_of_val(a));
    assert!(
        size_of::<B>() != 0 && ptr.is_aligned() && bytes % size_of::<B>() == 0,
        "slice does not cast"
    );
    // SAFETY: as `cast_slice`, and the borrow is unique.
    unsafe { core::slice::from_raw_parts_mut(ptr, bytes / core::mem::size_of::<B>()) }
}

#[cfg(test)]
mod formatting_tests {
    use super::{pretty_f64, pretty_integer};

    #[test]
    fn pretty_integer_groups_decimal_digits() {
        assert_eq!(pretty_integer(0), "0");
        assert_eq!(pretty_integer(12), "12");
        assert_eq!(pretty_integer(999), "999");
        assert_eq!(pretty_integer(1_000), "1,000");
        assert_eq!(pretty_integer(16_769_432), "16,769,432");
        assert_eq!(
            pretty_integer(u128::MAX),
            "340,282,366,920,938,463,463,374,607,431,768,211,455"
        );
        assert_eq!(pretty_integer(-12_345), "-12,345");
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
