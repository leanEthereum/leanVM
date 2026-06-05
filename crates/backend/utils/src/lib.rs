use std::{
    hint::unreachable_unchecked,
    mem::{self, MaybeUninit},
    slice,
};

pub mod array_serialization;

pub mod ansi;

mod misc;
pub use misc::*;

mod logs;
pub use logs::*;

/// Computes `log_2(n)`
///
/// # Panics
/// Panics if `n` is not a power of two.
#[must_use]
#[inline]
pub fn log2_strict_usize(n: usize) -> usize {
    let res = n.trailing_zeros();
    assert_eq!(n.wrapping_shr(res), 1, "Not a power of two: {n}");
    // Tell the optimizer about the semantics of `log2_strict`. i.e. it can replace `n` with
    // `1 << res` and vice versa.
    unsafe {
        assume(n == 1 << res);
    }
    res as usize
}

/// Allow the compiler to assume that the given predicate `p` is always `true`.
///
/// # Safety
///
/// Callers must ensure that `p` is true. If this is not the case, the behavior is undefined.
#[inline(always)]
pub unsafe fn assume(p: bool) {
    debug_assert!(p);
    if !p {
        unsafe {
            unreachable_unchecked();
        }
    }
}

/// Returns an iterator over `N` elements of the iterator at a time.
///
/// The chunks do not overlap. If `N` does not divide the length of the
/// iterator, then the last `N-1` elements will be padded with the given default value.
///
/// This is essentially a copy pasted version of the nightly `array_chunks` function.
/// https://doc.rust-lang.org/std/iter/trait.Iterator.html#method.array_chunks
/// Once that is stabilized this and the functions above it should be removed.
#[inline]
pub fn iter_array_chunks_padded<T: Copy, const N: usize>(
    iter: impl IntoIterator<Item = T>,
    default: T, // Needed due to [T; M] not always implementing Default. Can probably be dropped if const generics stabilize.
) -> impl Iterator<Item = [T; N]> {
    let mut iter = iter.into_iter();
    std::iter::from_fn(move || iter_next_chunk_padded(&mut iter, default))
}

/// Pulls `N` items from `iter` and returns them as an array. If the iterator
/// yields fewer than `N` items (but more than `0`), pads by the given default value.
///
/// Since the iterator is passed as a mutable reference and this function calls
/// `next` at most `N` times, the iterator can still be used afterwards to
/// retrieve the remaining items.
///
/// If `iter.next()` panics, all items already yielded by the iterator are
/// dropped.
#[inline]
fn iter_next_chunk_padded<T: Copy, const N: usize>(
    iter: &mut impl Iterator<Item = T>,
    default: T, // Needed due to [T; M] not always implementing Default. Can probably be dropped if const generics stabilize.
) -> Option<[T; N]> {
    let (mut arr, n) = iter_next_chunk_erased::<N, _>(iter);
    (n != 0).then(|| {
        // Fill the rest of the array with default values.
        arr[n..].fill(MaybeUninit::new(default));
        unsafe { mem::transmute_copy::<_, [T; N]>(&arr) }
    })
}

/// A C-style buffered input reader, similar to
/// `core::iter::Iterator::next_chunk()` from nightly.
///
/// Returns an array of `MaybeUninit<T>` and the number of items in the
/// array which have been correctly initialized.
#[inline]
fn iter_next_chunk_erased<const BUFLEN: usize, I: Iterator>(iter: &mut I) -> ([MaybeUninit<I::Item>; BUFLEN], usize)
where
    I::Item: Copy,
{
    let mut buf = [const { MaybeUninit::<I::Item>::uninit() }; BUFLEN];
    let mut i = 0;

    while i < BUFLEN {
        if let Some(c) = iter.next() {
            // Copy the next Item into `buf`.
            unsafe {
                buf.get_unchecked_mut(i).write(c);
                i = i.unchecked_add(1);
            }
        } else {
            // No more items in the iterator.
            break;
        }
    }
    (buf, i)
}

/// Returns `[0, ..., N - 1]`.
#[must_use]
pub const fn indices_arr<const N: usize>() -> [usize; N] {
    let mut indices_arr = [0; N];
    let mut i = 0;
    while i < N {
        indices_arr[i] = i;
        i += 1;
    }
    indices_arr
}

/// Bridge a `std::Vec<T>` to `allocator_api2::Vec<T, Global>` in O(1). `allocator_api2`'s
/// `Global` delegates to the same `std::alloc` global allocator that backs `std::Vec`, so their
/// raw parts are interchangeable.
#[inline]
fn vec_into_global<T>(vec: Vec<T>) -> allocator_api2::vec::Vec<T, allocator_api2::alloc::Global> {
    let mut vec = std::mem::ManuallyDrop::new(vec);
    // SAFETY: raw parts come straight from a valid `Vec`, and `Global` shares its allocator.
    unsafe {
        allocator_api2::vec::Vec::from_raw_parts_in(
            vec.as_mut_ptr(),
            vec.len(),
            vec.capacity(),
            allocator_api2::alloc::Global,
        )
    }
}

/// Inverse of [`vec_into_global`].
#[inline]
fn vec_from_global<T>(vec: allocator_api2::vec::Vec<T, allocator_api2::alloc::Global>) -> Vec<T> {
    let (ptr, len, cap, _global) = vec.into_raw_parts_with_alloc();
    // SAFETY: as `vec_into_global`.
    unsafe { Vec::from_raw_parts(ptr, len, cap) }
}

/// Convert a vector of `BaseArray` elements to a vector of `Base` elements without any
/// reallocations. The `Global`-allocator specialization of [`flatten_to_base_in`].
///
/// # Safety
/// This assumes that `BaseArray` has the same alignment and memory layout as `[Base; N]`.
#[inline]
pub unsafe fn flatten_to_base<Base, BaseArray>(vec: Vec<BaseArray>) -> Vec<Base> {
    // SAFETY: forwarded to the allocator-generic core; the caller upholds its layout contract.
    vec_from_global(unsafe { flatten_to_base_in::<Base, BaseArray, _>(vec_into_global(vec)) })
}

/// Convert a vector of `Base` elements to a vector of `BaseArray` elements. The `Global`-
/// allocator specialization of [`reconstitute_from_base_in`].
///
/// # Safety
/// This assumes that `BaseArray` has the same alignment and memory layout as `[Base; N]`.
#[inline]
pub unsafe fn reconstitute_from_base<Base, BaseArray: Clone>(vec: Vec<Base>) -> Vec<BaseArray> {
    // SAFETY: as above.
    vec_from_global(unsafe { reconstitute_from_base_in::<Base, BaseArray, _>(vec_into_global(vec)) })
}

/// Convert a vector of `BaseArray` elements to a vector of `Base` elements without any
/// reallocations, carrying the backing allocator `A` (e.g. the proving arena) through unchanged.
///
/// # Safety
/// `BaseArray` must have the same alignment and memory layout as `[Base; N]`.
#[inline]
pub unsafe fn flatten_to_base_in<Base, BaseArray, A: allocator_api2::alloc::Allocator>(
    vec: allocator_api2::vec::Vec<BaseArray, A>,
) -> allocator_api2::vec::Vec<Base, A> {
    const {
        assert!(align_of::<Base>() == align_of::<BaseArray>());
        assert!(size_of::<BaseArray>().is_multiple_of(size_of::<Base>()));
    }

    let d = size_of::<BaseArray>() / size_of::<Base>();
    let (ptr, len, cap, alloc) = vec.into_raw_parts_with_alloc();
    unsafe { allocator_api2::vec::Vec::from_raw_parts_in(ptr.cast::<Base>(), len * d, cap * d, alloc) }
}

/// Allocator-preserving [`reconstitute_from_base`] (see [`flatten_to_base_in`]).
///
/// # Safety
/// Same contract as [`reconstitute_from_base`].
#[inline]
pub unsafe fn reconstitute_from_base_in<Base, BaseArray: Clone, A: allocator_api2::alloc::Allocator + Clone>(
    vec: allocator_api2::vec::Vec<Base, A>,
) -> allocator_api2::vec::Vec<BaseArray, A> {
    const {
        assert!(align_of::<Base>() == align_of::<BaseArray>());
        assert!(size_of::<BaseArray>().is_multiple_of(size_of::<Base>()));
    }

    let d = size_of::<BaseArray>() / size_of::<Base>();
    assert!(
        vec.len().is_multiple_of(d),
        "Vector length (got {}) must be a multiple of the extension field dimension ({}).",
        vec.len(),
        d
    );
    let new_len = vec.len() / d;

    if vec.capacity().is_multiple_of(d) {
        let (ptr, _len, cap, alloc) = vec.into_raw_parts_with_alloc();
        unsafe { allocator_api2::vec::Vec::from_raw_parts_in(ptr.cast::<BaseArray>(), new_len, cap / d, alloc) }
    } else {
        // Capacity isn't a clean multiple: copy into a fresh, same-allocator buffer.
        let alloc = vec.allocator().clone();
        let buf_ptr = vec.as_ptr().cast::<BaseArray>();
        let slice_ref = unsafe { slice::from_raw_parts(buf_ptr, new_len) };
        let mut out = allocator_api2::vec::Vec::with_capacity_in(new_len, alloc);
        out.extend_from_slice(slice_ref);
        out
    }
}

/// Try to force Rust to emit a branch.
#[inline(always)]
pub fn branch_hint() {
    #[cfg(any(
        target_arch = "aarch64",
        target_arch = "arm",
        target_arch = "riscv32",
        target_arch = "riscv64",
        target_arch = "x86",
        target_arch = "x86_64",
    ))]
    unsafe {
        core::arch::asm!("", options(nomem, nostack, preserves_flags));
    }
}

#[inline(always)]
pub const fn relatively_prime_u64(mut u: u64, mut v: u64) -> bool {
    if u == 0 || v == 0 {
        return false;
    }
    if (u | v) & 1 == 0 {
        return false;
    }
    u >>= u.trailing_zeros();
    if u == 1 {
        return true;
    }
    while v != 0 {
        v >>= v.trailing_zeros();
        if v == 1 {
            return true;
        }
        if u > v {
            core::mem::swap(&mut u, &mut v);
        }
        v -= u
    }
    false
}

#[inline]
pub fn gcd_inversion_prime_field_32<const FIELD_BITS: u32>(mut a: u32, mut b: u32) -> i64 {
    const {
        assert!(FIELD_BITS <= 32);
    }
    debug_assert!(((1_u64 << FIELD_BITS) - 1) >= b as u64);

    let (mut u, mut v) = (1_i64, 0_i64);

    for _ in 0..(2 * FIELD_BITS - 2) {
        if a & 1 != 0 {
            if a < b {
                (a, b) = (b, a);
                (u, v) = (v, u);
            }
            a -= b;
            u -= v;
        }
        a >>= 1;
        v <<= 1;
    }
    v
}

/// Reinterpret a mutable slice of `BaseArray` elements as a slice of `Base` elements.
///
/// # Safety
///
/// Same requirements as `as_base_slice`.
#[inline]
pub unsafe fn as_base_slice_mut<Base, BaseArray>(buf: &mut [BaseArray]) -> &mut [Base] {
    const {
        assert!(align_of::<Base>() == align_of::<BaseArray>());
        assert!(size_of::<BaseArray>().is_multiple_of(size_of::<Base>()));
    }

    let d = size_of::<BaseArray>() / size_of::<Base>();

    let buf_ptr = buf.as_mut_ptr().cast::<Base>();
    let n = buf.len() * d;
    unsafe { slice::from_raw_parts_mut(buf_ptr, n) }
}

/// Reinterpret a slice of `BaseArray` elements as a slice of `Base` elements
///
/// This is useful to convert `&[F; N]` to `&[F]` or `&[A]` to `&[F]` where
/// `A` has the same size, alignment and memory layout as `[F; N]` for some `N`.
///
/// # Safety
///
/// This is assumes that `BaseArray` has the same alignment and memory layout as `[Base; N]`.
/// As Rust guarantees that arrays elements are contiguous in memory and the alignment of
/// the array is the same as the alignment of its elements, this means that `BaseArray`
/// must have the same alignment as `Base`.
///
/// # Panics
///
/// This panics if the size of `BaseArray` is not a multiple of the size of `Base`.
#[inline]
pub unsafe fn as_base_slice<Base, BaseArray>(buf: &[BaseArray]) -> &[Base] {
    const {
        assert!(align_of::<Base>() == align_of::<BaseArray>());
        assert!(size_of::<BaseArray>().is_multiple_of(size_of::<Base>()));
    }

    let d = size_of::<BaseArray>() / size_of::<Base>();

    let buf_ptr = buf.as_ptr().cast::<Base>();
    let n = buf.len() * d;
    unsafe { slice::from_raw_parts(buf_ptr, n) }
}

/// Computes `ceil(log_2(n))`.
#[must_use]
pub const fn log2_ceil_usize(n: usize) -> usize {
    (usize::BITS - n.saturating_sub(1).leading_zeros()) as usize
}

#[must_use]
pub fn log2_ceil_u64(n: u64) -> u64 {
    (u64::BITS - n.saturating_sub(1).leading_zeros()).into()
}

pub fn pretty_integer(i: usize) -> String {
    // ex: 123456789 -> "123,456,789"
    let s = i.to_string();
    let chars: Vec<char> = s.chars().collect();
    let mut result = String::new();

    for (index, ch) in chars.iter().enumerate() {
        if index > 0 && (chars.len() - index).is_multiple_of(3) {
            result.push(',');
        }
        result.push(*ch);
    }

    result
}
