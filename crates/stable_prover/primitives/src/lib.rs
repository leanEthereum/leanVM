//! The stable prover's primitives: the fields and their one SIMD layer ([`field`]), Keccak-256 ([`hash`]), the
//! weighted bit fold ([`bit_fold`]), multilinear helpers ([`multilinear`]), the shared transcript on this field
//! ([`transcript`]), and small integer and slice utilities.

pub mod bit_fold;
pub mod field;
pub mod hash;
pub mod multilinear;
pub mod transcript;

#[cfg(any(test, feature = "test-util"))]
pub mod test_rng;

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
