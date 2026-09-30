//! Growable buffer backed by the proving arena during a phase and the system allocator otherwise. Size arena-backed buffers up front anyway: growing copies, and the old allocation is only recycled if it clears the arena's reuse floor.

use std::alloc::{Layout, handle_alloc_error};
use std::cmp;
use std::fmt;
use std::marker::PhantomData;
use std::mem::{ManuallyDrop, MaybeUninit, align_of, needs_drop, size_of};
use std::ops::{Deref, DerefMut};
use std::ptr::{self, NonNull};
use std::slice;

use crate::{raw_alloc, raw_dealloc};

/// An owning, growable buffer allocated from the proving arena.
pub struct ArenaVec<T> {
    ptr: NonNull<T>,
    len: usize,
    cap: usize,
    _marker: PhantomData<T>,
}

// SAFETY: `ArenaVec` owns its elements exactly as `Vec` does; the arena imposes
// no additional thread affinity (a slab is bumped only by its owning thread, and
// the resulting pointer is plain memory).
unsafe impl<T: Send> Send for ArenaVec<T> {}
unsafe impl<T: Sync> Sync for ArenaVec<T> {}

impl<T> ArenaVec<T> {
    /// `usize::MAX` stands in for "unbounded" for zero-sized elements, which
    /// never allocate; `0` otherwise.
    const EMPTY_CAP: usize = if size_of::<T>() == 0 { usize::MAX } else { 0 };

    /// An empty buffer. Allocates nothing.
    #[inline]
    #[must_use]
    pub const fn new() -> Self {
        Self {
            ptr: NonNull::dangling(),
            len: 0,
            cap: Self::EMPTY_CAP,
            _marker: PhantomData,
        }
    }

    /// An empty buffer with room for exactly `cap` elements (no over-allocation:
    /// the caller knows the size, and a slab is not a heap to grow into).
    #[inline]
    #[must_use]
    pub fn with_capacity(cap: usize) -> Self {
        let mut v = Self::new();
        if size_of::<T>() != 0 && cap != 0 {
            v.grow_to(cap);
        }
        v
    }

    /// `n` elements, each a clone of `value`, the arena's `vec![value; n]`.
    /// Prefer [`zeroed`](Self::zeroed) when the value is all-zero bytes.
    #[inline]
    #[must_use]
    pub fn filled(value: T, n: usize) -> Self
    where
        T: Clone,
    {
        let mut v = Self::with_capacity(n);
        v.resize(n, value);
        v
    }

    /// `n` zero-filled elements.
    ///
    /// # Safety
    /// The all-zero bit pattern must be a valid, fully initialized `T`, true of
    /// the field types here and their SIMD packings, whose zero is all-zero bytes.
    #[inline]
    #[must_use]
    pub unsafe fn zeroed(n: usize) -> Self {
        let mut v = Self::with_capacity(n);
        // SAFETY: the allocation holds every slot and all-zero is a valid element.
        unsafe {
            ptr::write_bytes(v.as_mut_ptr(), 0u8, n);
            v.set_len(n);
        }
        v
    }

    /// The arena's `slice.to_vec()`.
    #[inline]
    #[must_use]
    pub fn from_slice(slice: &[T]) -> Self
    where
        T: Clone,
    {
        let mut v = Self::with_capacity(slice.len());
        v.extend_from_slice(slice);
        v
    }

    /// `len` slots of uninitialized memory, ready to be filled in place (in
    /// parallel, typically: `ArenaVec` derefs to `&mut [T]`).
    ///
    /// # Safety
    /// Every one of the `len` elements must be written before it is read.
    #[inline]
    #[must_use]
    pub unsafe fn uninitialized(len: usize) -> Self {
        let mut v = Self::with_capacity(len);
        // SAFETY: the caller guarantees all `len` slots are written before read.
        unsafe { v.set_len(len) };
        v
    }

    #[inline]
    #[must_use]
    pub const fn len(&self) -> usize {
        self.len
    }

    #[inline]
    #[must_use]
    pub const fn capacity(&self) -> usize {
        self.cap
    }

    #[inline]
    #[must_use]
    pub const fn is_empty(&self) -> bool {
        self.len == 0
    }

    #[inline]
    #[must_use]
    pub const fn as_ptr(&self) -> *const T {
        self.ptr.as_ptr()
    }

    #[inline]
    pub const fn as_mut_ptr(&mut self) -> *mut T {
        self.ptr.as_ptr()
    }

    #[inline]
    #[must_use]
    pub fn as_slice(&self) -> &[T] {
        self
    }

    /// Set the length without touching the buffer.
    ///
    /// # Safety
    /// `new_len <= capacity()`, and every element below `new_len` must be
    /// initialized.
    #[inline]
    pub unsafe fn set_len(&mut self, new_len: usize) {
        debug_assert!(new_len <= self.cap);
        self.len = new_len;
    }

    /// Make room for `additional` more elements, doubling to keep repeated
    /// [`push`](Self::push) amortized.
    #[inline]
    pub fn reserve(&mut self, additional: usize) {
        if size_of::<T>() == 0 {
            return; // capacity is conceptually unbounded for zero-sized types
        }
        let required = self.len.checked_add(additional).expect("ArenaVec capacity overflow");
        if required > self.cap {
            self.grow_to(cmp::max(required, self.cap.saturating_mul(2)));
        }
    }

    #[inline]
    pub fn push(&mut self, value: T) {
        if self.len == self.cap {
            // Zero-sized types never reach here: their capacity is `usize::MAX`.
            self.grow_to(cmp::max(self.cap.saturating_mul(2), 4));
        }
        // SAFETY: `len < cap` now, so slot `len` is allocated and uninitialized.
        unsafe { self.ptr.as_ptr().add(self.len).write(value) };
        self.len += 1;
    }

    /// Append a clone of every element of `other`.
    #[inline]
    pub fn extend_from_slice(&mut self, other: &[T])
    where
        T: Clone,
    {
        self.reserve(other.len());
        // Bump `len` per element, so a panic mid-clone leaves a consistent buffer
        // whose written clones still drop.
        for x in other {
            // SAFETY: `reserve` guaranteed room for `other.len()` more elements.
            unsafe { self.ptr.as_ptr().add(self.len).write(x.clone()) };
            self.len += 1;
        }
    }

    /// Grow or shrink to `new_len`, cloning `value` into any new slots.
    pub fn resize(&mut self, new_len: usize, value: T)
    where
        T: Clone,
    {
        if new_len > self.len {
            self.reserve(new_len - self.len);
            while self.len < new_len {
                // SAFETY: room reserved above, so `len < new_len <= cap`.
                unsafe { self.ptr.as_ptr().add(self.len).write(value.clone()) };
                self.len += 1;
            }
        } else {
            self.truncate(new_len);
        }
    }

    /// Drop everything past `len`, keeping capacity.
    pub fn truncate(&mut self, len: usize) {
        if len < self.len {
            let dropped = self.len - len;
            // Shorten first, so a panicking `Drop` cannot observe or re-drop the tail.
            self.len = len;
            // SAFETY: `[len, old_len)` were initialized and are now logically gone.
            unsafe {
                ptr::drop_in_place(ptr::slice_from_raw_parts_mut(self.ptr.as_ptr().add(len), dropped));
            }
        }
    }

    /// Decompose into raw parts, leaking the buffer. Inverse of
    /// [`from_raw_parts`](Self::from_raw_parts).
    #[inline]
    #[must_use]
    pub(crate) fn into_raw_parts(self) -> (*mut T, usize, usize) {
        let me = ManuallyDrop::new(self);
        (me.ptr.as_ptr(), me.len, me.cap)
    }

    /// Reassemble from parts produced by [`into_raw_parts`](Self::into_raw_parts)
    /// (or a layout-compatible reinterpretation of them).
    ///
    /// # Safety
    /// `ptr` must be non-null and aligned for `T`, `len <= cap`, and either `ptr`
    /// came from `raw_alloc` for `cap * size_of::<T>()` bytes
    /// at `align_of::<T>()`, or `cap == 0` and `ptr` is dangling-but-aligned.
    /// Exactly one `ArenaVec` may own a given pointer.
    #[inline]
    #[must_use]
    pub(crate) unsafe fn from_raw_parts(ptr: *mut T, len: usize, cap: usize) -> Self {
        Self {
            // SAFETY: the caller guarantees `ptr` is non-null.
            ptr: unsafe { NonNull::new_unchecked(ptr) },
            len,
            cap,
            _marker: PhantomData,
        }
    }

    /// Allocate a fresh `new_cap`-element buffer, move the live elements across,
    /// and release the old one. Only reached for sized `T` with
    /// `new_cap >= len` and `new_cap > 0`.
    fn grow_to(&mut self, new_cap: usize) {
        debug_assert!(size_of::<T>() != 0 && new_cap >= self.len && new_cap > 0);
        let align = align_of::<T>();
        let bytes = new_cap.checked_mul(size_of::<T>()).expect("ArenaVec capacity overflow");
        assert!(bytes <= isize::MAX as usize, "ArenaVec capacity overflow");

        // SAFETY: `align` is a valid power of two and `bytes > 0`.
        let raw = unsafe { raw_alloc(bytes, align) }.cast::<T>();
        let Some(new_ptr) = NonNull::new(raw) else {
            // Matching `Vec`: allocation failure aborts rather than unwinds.
            // SAFETY: `align` is a power of two and `bytes <= isize::MAX`.
            handle_alloc_error(unsafe { Layout::from_size_align_unchecked(bytes, align) });
        };

        if self.cap != 0 {
            // SAFETY: the buffers are distinct and `len` initialized elements move.
            unsafe { ptr::copy_nonoverlapping(self.ptr.as_ptr(), new_ptr.as_ptr(), self.len) };
            // SAFETY: the old buffer came from `raw_alloc` with this size/align.
            unsafe { raw_dealloc(self.ptr.as_ptr().cast::<u8>(), self.cap * size_of::<T>(), align) };
        }
        self.ptr = new_ptr;
        self.cap = new_cap;
    }
}

/// `n` arena-backed slots to be initialized in place, one element at a time.
///
/// The `MaybeUninit` element type is what makes a partial fill expressible: write
/// through the slice, then [`assume_init`] once every slot is set. Prefer
/// [`ArenaVec::uninitialized`] when the fill is a bulk write over `&mut [T]`.
#[inline]
#[must_use]
pub fn alloc_uninit<T>(n: usize) -> ArenaVec<MaybeUninit<T>> {
    // SAFETY: `MaybeUninit<T>` is valid uninitialized, so every slot already
    // holds a valid value of the element type.
    unsafe { ArenaVec::uninitialized(n) }
}

/// Reinterpret a fully written [`alloc_uninit`] buffer as its element type.
///
/// # Safety
/// Every element of `v` must hold an initialized `T`.
#[inline]
#[must_use]
pub unsafe fn assume_init<T>(v: ArenaVec<MaybeUninit<T>>) -> ArenaVec<T> {
    let (ptr, len, cap) = v.into_raw_parts();
    // SAFETY: `MaybeUninit<T>` has the same size and alignment as `T`, so the
    // allocation matches `T`'s layout; the caller guarantees every slot is
    // initialized, and `into_raw_parts` transferred sole ownership.
    unsafe { ArenaVec::from_raw_parts(ptr.cast::<T>(), len, cap) }
}

impl<T> Drop for ArenaVec<T> {
    fn drop(&mut self) {
        // Drop the live elements first. Elided entirely for plain-data `T`.
        if needs_drop::<T>() {
            // SAFETY: `0..len` are initialized.
            unsafe { ptr::drop_in_place(ptr::slice_from_raw_parts_mut(self.ptr.as_ptr(), self.len)) };
        }
        // Release the buffer. Zero-sized types and never-grown vectors own nothing.
        if size_of::<T>() != 0 && self.cap != 0 {
            // SAFETY: the buffer came from `raw_alloc(cap * size, align)`;
            // `raw_dealloc` range-checks arena-vs-system, and an arena pointer is
            // recycled or left to the next phase reset rather than unmapped.
            unsafe {
                raw_dealloc(
                    self.ptr.as_ptr().cast::<u8>(),
                    self.cap * size_of::<T>(),
                    align_of::<T>(),
                );
            }
        }
    }
}

impl<T> Deref for ArenaVec<T> {
    type Target = [T];
    #[inline]
    fn deref(&self) -> &[T] {
        // SAFETY: `ptr` is aligned and `0..len` are initialized. Valid for
        // zero-sized `T` too: a dangling aligned pointer is a sound base for a
        // zero-stride slice.
        unsafe { slice::from_raw_parts(self.ptr.as_ptr(), self.len) }
    }
}

impl<T> DerefMut for ArenaVec<T> {
    #[inline]
    fn deref_mut(&mut self) -> &mut [T] {
        // SAFETY: as `deref`, with unique access.
        unsafe { slice::from_raw_parts_mut(self.ptr.as_ptr(), self.len) }
    }
}

impl<T> Default for ArenaVec<T> {
    #[inline]
    fn default() -> Self {
        Self::new()
    }
}

impl<T: Clone> Clone for ArenaVec<T> {
    fn clone(&self) -> Self {
        Self::from_slice(self)
    }
}

impl<T: fmt::Debug> fmt::Debug for ArenaVec<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Debug::fmt(&**self, f)
    }
}

impl<T: PartialEq> PartialEq for ArenaVec<T> {
    #[inline]
    fn eq(&self, other: &Self) -> bool {
        **self == **other
    }
}

impl<T: PartialEq> PartialEq<[T]> for ArenaVec<T> {
    #[inline]
    fn eq(&self, other: &[T]) -> bool {
        **self == *other
    }
}

impl<T: PartialEq> PartialEq<Vec<T>> for ArenaVec<T> {
    #[inline]
    fn eq(&self, other: &Vec<T>) -> bool {
        **self == **other
    }
}

impl<T: PartialEq> PartialEq<ArenaVec<T>> for Vec<T> {
    #[inline]
    fn eq(&self, other: &ArenaVec<T>) -> bool {
        **self == **other
    }
}

impl<T: Eq> Eq for ArenaVec<T> {}

impl<T> Extend<T> for ArenaVec<T> {
    #[inline]
    fn extend<I: IntoIterator<Item = T>>(&mut self, iter: I) {
        let iter = iter.into_iter();
        self.reserve(iter.size_hint().0);
        for x in iter {
            self.push(x);
        }
    }
}

impl<T> FromIterator<T> for ArenaVec<T> {
    #[inline]
    fn from_iter<I: IntoIterator<Item = T>>(iter: I) -> Self {
        let iter = iter.into_iter();
        let mut v = Self::with_capacity(iter.size_hint().0);
        v.extend(iter);
        v
    }
}

impl<'a, T> IntoIterator for &'a ArenaVec<T> {
    type Item = &'a T;
    type IntoIter = slice::Iter<'a, T>;
    #[inline]
    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

impl<'a, T> IntoIterator for &'a mut ArenaVec<T> {
    type Item = &'a mut T;
    type IntoIter = slice::IterMut<'a, T>;
    #[inline]
    fn into_iter(self) -> Self::IntoIter {
        self.iter_mut()
    }
}
