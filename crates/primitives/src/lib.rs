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

use std::mem::{MaybeUninit, needs_drop};

#[cfg(feature = "test-util")]
pub mod test_rng;

/// Format an integer with comma-separated groups of three decimal digits.
///
/// This accepts every standard signed and unsigned integer type through its
/// [`ToString`] representation. A leading sign is preserved.
///
/// ```
/// use primitives::pretty_integer;
///
/// assert_eq!(pretty_integer(16_769_432), "16,769,432");
/// assert_eq!(pretty_integer(-12_345), "-12,345");
/// ```
pub fn pretty_integer(value: impl ToString) -> String {
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

// SAFETY: integers, and `repr(transparent)` and `repr(C)` structs of them.
unsafe impl Plain for u8 {}
unsafe impl Plain for u64 {}
unsafe impl Plain for u32 {}
unsafe impl Plain for u128 {}
// SAFETY: an array of plain elements has no padding.
unsafe impl<T: Plain, const N: usize> Plain for [T; N] {}
// SAFETY: `repr(transparent)` over `u64`.
unsafe impl Plain for field::F64 {}
// SAFETY: `repr(C)` over three `u64`.
unsafe impl Plain for field::F192 {}
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
/// If the slice is misaligned for `B`, or its byte length is not a multiple of `size_of::<B>()`.
pub fn cast_slice<A: Plain, B: Plain>(a: &[A]) -> &[B] {
    let (ptr, bytes) = (a.as_ptr().cast::<B>(), core::mem::size_of_val(a));
    assert!(
        ptr.is_aligned() && bytes % core::mem::size_of::<B>() == 0,
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
        ptr.is_aligned() && bytes % core::mem::size_of::<B>() == 0,
        "slice does not cast"
    );
    // SAFETY: as `cast_slice`, and the borrow is unique.
    unsafe { core::slice::from_raw_parts_mut(ptr, bytes / core::mem::size_of::<B>()) }
}

/// The `A` whose bytes start at element `i` of `src`, read unaligned.
#[inline(always)]
pub fn load_at<T: Plain, A: Plain>(src: &[T], i: usize) -> A {
    assert!(i.saturating_mul(size_of::<T>()).saturating_add(size_of::<A>()) <= size_of_val(src));
    // SAFETY: the assert keeps the bytes inside `src`, and any bytes of a `Plain` type are
    // readable and a valid `A`.
    unsafe { src.as_ptr().wrapping_add(i).cast::<A>().read_unaligned() }
}

/// Write `v` over the bytes from element `i` of `dst` on, unaligned.
#[inline(always)]
pub fn store_at<T: Plain, A: Plain>(dst: &mut [T], i: usize, v: A) {
    assert!(i.saturating_mul(size_of::<T>()).saturating_add(size_of::<A>()) <= size_of_val(dst));
    // SAFETY: the assert keeps the bytes inside `dst`, and any bytes are a valid `Plain` value.
    unsafe { dst.as_mut_ptr().add(i).cast::<A>().write_unaligned(v) }
}

/// `N` vectors of the given lengths, filled in place by `fill`.
///
/// It skips the zero-fill, which would cost one more pass over memory. Only plain data is allowed, so
/// dropping an element runs no code:
///
/// ```compile_fail
/// unsafe { primitives::filled_vecs([1], |_: [&mut [String]; 1]| {}) };
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

/// Parallel `(0..n).map(build).collect()`.
///
/// - One allocation on the calling thread, filled in place by the workers.
/// - No per-worker vector is allocated, then copied out.
pub fn par_collect<T: Send>(n: usize, build: impl Fn(usize) -> T + Sync) -> Vec<T> {
    // The vector's spare capacity, written slot by slot before the length covers it.
    let mut out = Vec::with_capacity(n);
    let slots = &mut out.spare_capacity_mut()[..n];

    // Track partial initialization only when values require destruction.
    if needs_drop::<T>() {
        let mut initialized = vec![false; n];
        let mut guard = PartialInit {
            slots,
            initialized: &mut initialized,
            armed: true,
        };
        let chunk_size = parallel::recommended_chunk_size(n);
        parallel::chunks_mut2(guard.slots, guard.initialized, chunk_size, |chunk, slots, marks| {
            let base = chunk * chunk_size;
            for (offset, (slot, mark)) in slots.iter_mut().zip(marks).enumerate() {
                slot.write(build(base + offset));
                *mark = true;
            }
        });
        guard.armed = false;
    } else {
        parallel::fill(slots, |i| MaybeUninit::new(build(i)));
    }

    // SAFETY: the dispatch joins and every slot is initialized before it returns successfully.
    unsafe { out.set_len(n) };
    out
}

struct PartialInit<'a, T> {
    slots: &'a mut [MaybeUninit<T>],
    initialized: &'a mut [bool],
    armed: bool,
}

impl<T> Drop for PartialInit<'_, T> {
    fn drop(&mut self) {
        if self.armed {
            // The pool stops all writers before resuming a task panic on this thread.
            for (slot, initialized) in self.slots.iter_mut().zip(self.initialized.iter()) {
                if *initialized {
                    // SAFETY: the mark is set only after this slot has received a valid value.
                    unsafe { slot.assume_init_drop() };
                }
            }
        }
    }
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

#[cfg(test)]
mod collection_tests {
    use super::par_collect;
    use std::panic::{AssertUnwindSafe, catch_unwind};
    use std::sync::atomic::{AtomicUsize, Ordering};

    #[test]
    fn collection_initializes_owned_values() {
        assert!(par_collect::<String>(0, |_| unreachable!()).is_empty());
        let values = par_collect(257, |i| i.to_string());
        for (i, value) in values.iter().enumerate() {
            assert_eq!(*value, i.to_string());
        }
    }

    #[test]
    fn panicking_collection_drops_only_initialized_values() {
        struct Counted<'a> {
            _value: String,
            drops: &'a AtomicUsize,
        }

        impl Drop for Counted<'_> {
            fn drop(&mut self) {
                self.drops.fetch_add(1, Ordering::Relaxed);
            }
        }

        let built = AtomicUsize::new(0);
        let drops = AtomicUsize::new(0);
        let result = catch_unwind(AssertUnwindSafe(|| {
            par_collect(257, |i| {
                assert_ne!(i, 17, "construction failed");
                built.fetch_add(1, Ordering::Relaxed);
                Counted {
                    _value: i.to_string(),
                    drops: &drops,
                }
            })
        }));
        assert!(result.is_err());
        assert!(built.load(Ordering::Relaxed) > 0);
        assert_eq!(built.load(Ordering::Relaxed), drops.load(Ordering::Relaxed));
        assert_eq!(&*par_collect(3, |i| i as u64), &[0, 1, 2]);
    }
}
