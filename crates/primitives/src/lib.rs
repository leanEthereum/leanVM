//! Shared primitives: field kernels, bit transposes, multilinear helpers, and small integer utilities.

pub mod bit_fold;
pub mod bits;
pub mod field;
pub mod hash;
pub mod multilinear;
pub mod portable;
pub mod stream;

use std::mem::MaybeUninit;

#[cfg(feature = "test-util")]
pub mod test_util;

/// `log2` of a power of two.
///
/// # Panics
///
/// Panics when `n` is not a power of two.
pub const fn log2_strict_usize(n: usize) -> usize {
    assert!(n.is_power_of_two(), "not a power of two");
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
