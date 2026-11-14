//! Copies into buffers written once and read in a later pass: ordinary copies, behind the API the
//! prover's kernels call.

use crate::Plain;

/// A region of copies.
#[derive(Debug, Default)]
pub struct Stream;

impl Stream {
    pub fn new() -> Self {
        Self
    }

    /// Copy `src` over `dst`.
    #[inline]
    pub fn copy<T: Plain>(&self, dst: &mut [T], src: &[T]) {
        dst.copy_from_slice(src);
    }

    /// [`copy`](Self::copy) into a destination that is not yet initialised.
    ///
    /// # Safety
    /// `dst` must be valid for `src.len()` elements and disjoint from `src`.
    #[inline]
    pub unsafe fn copy_uninit<T: Plain>(&self, dst: *mut T, src: &[T]) {
        // SAFETY: forwarded to the caller's obligation.
        unsafe { core::ptr::copy_nonoverlapping(src.as_ptr(), dst, src.len()) }
    }

    /// Copy one value to `dst`.
    ///
    /// # Safety
    /// `dst` must be valid, aligned for `T` and disjoint from `src`.
    #[inline]
    pub unsafe fn copy_lines<T: Plain>(&self, dst: *mut T, src: &T) {
        // SAFETY: forwarded to the caller's obligation.
        unsafe { dst.write(*src) };
    }
}
