//! Shared primitives: field kernels, bit transposes, multilinear helpers, and
//! small integer utilities.

pub mod bits;
pub mod field;
pub mod hash;
pub mod multilinear;
pub mod stream;

use std::mem::{MaybeUninit, needs_drop};
use zk_alloc::{alloc_uninit, assume_init};

#[cfg(feature = "test-util")]
pub mod test_rng;

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

/// Arena-backed parallel `(0..n).map(build).collect()`: one allocation on the
/// calling thread, filled in place by the workers: no per-worker intermediate
/// vectors to allocate and copy out of. This lives here rather than in
/// `zk_alloc` so the allocator itself stays free of a thread-pool dependency.
pub fn par_collect_arena<T: Send>(n: usize, build: impl Fn(usize) -> T + Sync) -> zk_alloc::ArenaVec<T> {
    let mut out = alloc_uninit(n);
    // Track partial initialization only when values require destruction.
    if needs_drop::<T>() {
        let mut initialized = vec![false; n];
        let mut guard = PartialInit {
            slots: &mut out,
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
        parallel::fill(&mut out, |i| MaybeUninit::new(build(i)));
    }
    // SAFETY: the dispatch joins and every slot is initialized before it returns successfully.
    unsafe { assume_init(out) }
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

#[cfg(test)]
mod collection_tests {
    use super::par_collect_arena;
    use std::panic::{AssertUnwindSafe, catch_unwind};
    use std::sync::atomic::{AtomicUsize, Ordering};

    #[test]
    fn collection_initializes_owned_values() {
        assert!(par_collect_arena::<String>(0, |_| unreachable!()).is_empty());
        let values = par_collect_arena(257, |i| i.to_string());
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
            par_collect_arena(257, |i| {
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
        assert_eq!(&*par_collect_arena(3, |i| i as u64), &[0, 1, 2]);
    }
}
