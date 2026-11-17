//! Shared primitives: field kernels, bit transposes, multilinear helpers, and
//! small integer utilities.

pub mod bit_fold;
pub mod bits;
pub mod field;
pub mod hash;
pub mod multilinear;
#[cfg(all(target_arch = "x86_64", target_feature = "avx512f"))]
pub mod simd;
pub mod stream;
pub mod transcript;

#[cfg(feature = "test-util")]
pub mod test_rng;

/// Whether the prover rebuilds what a later step reads rather than storing it. On x86 the
/// stores' memory traffic costs more than the products that rebuild their contents, and every
/// other target but Apple silicon follows it; on Apple silicon a store-only pass is as cheap as a
/// read, so the prover stores there.
pub const REBUILD_OVER_STORE: bool = !cfg!(all(target_arch = "aarch64", target_os = "macos"));

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
unsafe impl Plain for u32 {}
unsafe impl Plain for u128 {}
// SAFETY: an array of plain elements has no padding.
unsafe impl<T: Plain, const N: usize> Plain for [T; N] {}
// SAFETY: `repr(transparent)` over `u64`.
unsafe impl Plain for field::F64 {}
// SAFETY: `repr(C)` over two `u64`.
unsafe impl Plain for field::F128 {}
// SAFETY: vectors of 16, 32 and 64 bytes with no padding, and every bit pattern is a valid vector.
#[cfg(target_arch = "x86_64")]
unsafe impl Plain for core::arch::x86_64::__m128i {}
#[cfg(target_arch = "x86_64")]
unsafe impl Plain for core::arch::x86_64::__m256i {}
#[cfg(target_arch = "x86_64")]
unsafe impl Plain for core::arch::x86_64::__m512i {}
// SAFETY: vectors of 8 and 16 bytes with no padding, and every bit pattern is a valid vector.
#[cfg(target_arch = "aarch64")]
unsafe impl Plain for core::arch::aarch64::uint32x2_t {}
#[cfg(target_arch = "aarch64")]
unsafe impl Plain for core::arch::aarch64::uint8x16_t {}
#[cfg(target_arch = "aarch64")]
unsafe impl Plain for core::arch::aarch64::uint32x4_t {}
#[cfg(target_arch = "aarch64")]
unsafe impl Plain for core::arch::aarch64::uint64x2_t {}

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

/// The `A` whose bytes start at element `i` of `src`, read unaligned.
#[inline(always)]
pub fn load_at<T: Plain, A: Plain>(src: &[T], i: usize) -> A {
    let rest = &src[i..];
    assert!(size_of::<A>() <= size_of_val(rest));
    // SAFETY: the assert keeps the bytes inside `src`, and any bytes of a `Plain` type are
    // readable and a valid `A`.
    unsafe { rest.as_ptr().cast::<A>().read_unaligned() }
}

/// Write `v` over the bytes from element `i` of `dst` on, unaligned.
#[inline(always)]
pub fn store_at<T: Plain, A: Plain>(dst: &mut [T], i: usize, v: A) {
    let rest = &mut dst[i..];
    assert!(size_of::<A>() <= size_of_val(rest));
    // SAFETY: the assert keeps the bytes inside `dst`, and any bytes are a valid `Plain` value.
    unsafe { rest.as_mut_ptr().cast::<A>().write_unaligned(v) }
}

/// `N` vectors of the given lengths, filled in place by `fill`.
///
/// It skips the zero-fill, which would cost one more pass over memory. Only plain data is allowed, so
/// dropping an element runs no code:
///
/// ```compile_fail
/// unsafe { experimental_primitives::filled_vecs([1], |_: [&mut [String]; 1]| {}) };
/// ```
///
/// # Safety
///
/// `fill` receives one slice per vector of uninitialized elements, and must write every element
/// before it reads it.
#[must_use]
pub unsafe fn filled_vecs<T: Plain, const N: usize>(lens: [usize; N], fill: impl FnOnce([&mut [T]; N])) -> [Vec<T>; N] {
    // SAFETY: `fill` writes each element before reading it, by the caller's contract.
    let mut vs = lens.map(|len| unsafe { uninit_vec(len) });
    fill(vs.each_mut().map(|v| &mut v[..]));
    vs
}

/// One vector of `len` elements, filled in place by `fill`: [`filled_vecs`] with `N = 1`.
///
/// # Safety
///
/// As [`filled_vecs`]: `fill` must write every element before it reads it.
#[must_use]
pub unsafe fn filled_vec<T: Plain>(len: usize, fill: impl FnOnce(&mut [T])) -> Vec<T> {
    // SAFETY: forwarded to the caller's contract.
    let [v] = unsafe { filled_vecs([len], |[s]| fill(s)) };
    v
}

/// A vector of `len` uninitialized elements, for a fill that outlives one scope.
///
/// Prefer [`filled_vec`], which keeps the fill next to the allocation.
///
/// # Safety
///
/// Every element must be written before it is read.
#[must_use]
#[expect(clippy::uninit_vec, reason = "the caller writes every element before reading it")]
pub unsafe fn uninit_vec<T: Plain>(len: usize) -> Vec<T> {
    // Exactly `len` slots, so the vector never reallocates while it is filled.
    let mut v = Vec::with_capacity(len);

    // SAFETY: the capacity holds `len` elements, and the caller writes each one before reading it.
    unsafe { v.set_len(len) };
    v
}
