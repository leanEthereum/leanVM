//! [`ArenaVec<T>`] — a minimal owning vector backed by the proving arena.
//!
//! Allocation goes through [`raw_alloc`](crate::raw_alloc) (arena bump in a phase, else system) and
//! `Drop`/growth through [`raw_dealloc`](crate::raw_dealloc), which picks arena-vs-system by pointer
//! range — the dynamic choice that lets `ArenaVec` carry no allocator type parameter. An `ArenaVec`
//! allocated in a phase is invalidated by the next [`begin_phase`](crate::begin_phase); anything
//! that must outlive a phase uses the system allocator (a plain `Vec`, or an `ArenaVec` built outside a
//! phase).

use std::alloc::handle_alloc_error;
use std::cmp;
use std::fmt;
use std::marker::PhantomData;
use std::mem::{ManuallyDrop, align_of, size_of};
use std::ops::{Deref, DerefMut};
use std::ptr::{self, NonNull};
use std::slice;

use crate::{raw_alloc, raw_dealloc};

/// Owning, growable buffer allocated from the proving arena (see the module docs).
pub struct ArenaVec<T> {
    /// Always aligned and non-null; dangling (and never dereferenced for reads) while `cap == 0`.
    ptr: NonNull<T>,
    len: usize,
    /// Element capacity. For zero-sized `T` this is fixed at `usize::MAX` and no memory is owned.
    cap: usize,
    _marker: PhantomData<T>,
}

unsafe impl<T: Send> Send for ArenaVec<T> {}
unsafe impl<T: Sync> Sync for ArenaVec<T> {}

pub trait OwnedBuffer<T>: DerefMut<Target = [T]> + Sized {
    /// `len` uninitialized elements.
    ///
    /// # Safety
    /// Every element must be written before it is read.
    unsafe fn uninit(len: usize) -> Self;

    /// `len` elements, initialized in place by `fill` — which **must** write all of them.
    #[inline]
    fn build(len: usize, fill: impl FnOnce(&mut [T])) -> Self {
        // SAFETY: `fill` writes every one of the `len` elements before any is read.
        let mut buf = unsafe { Self::uninit(len) };
        fill(&mut buf);
        buf
    }
}

impl<T> OwnedBuffer<T> for Vec<T> {
    #[inline]
    #[allow(clippy::uninit_vec)]
    unsafe fn uninit(len: usize) -> Self {
        let mut v = Vec::with_capacity(len);
        // SAFETY: the `uninit`/`build` contract requires all `len` slots written before read.
        unsafe { v.set_len(len) };
        v
    }
}

impl<T> OwnedBuffer<T> for ArenaVec<T> {
    #[inline]
    unsafe fn uninit(len: usize) -> Self {
        // SAFETY: as above.
        unsafe { Self::uninitialized(len) }
    }
}

impl<T> ArenaVec<T> {
    /// `usize::MAX` capacity stands in for "unbounded" for zero-sized elements (which never
    /// allocate); `0` otherwise.
    const EMPTY_CAP: usize = if size_of::<T>() == 0 { usize::MAX } else { 0 };

    /// A new, empty vector. No allocation.
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

    /// A new, empty vector with room for `cap` elements pre-reserved (exact, no over-allocation).
    #[inline]
    #[must_use]
    pub fn with_capacity(cap: usize) -> Self {
        let mut v = Self::new();
        if size_of::<T>() != 0 && cap != 0 {
            v.realloc_to(cap);
        }
        v
    }

    /// Arena-backed `vec![value; n]`.
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

    /// Arena-backed zero-initialized buffer of length `n`, zeroed with a single `write_bytes`
    /// (`memset`) — far cheaper than [`filled`](Self::filled)'s element-wise clone loop.
    ///
    /// # Safety
    /// `T`'s all-zero bit pattern must be a valid, fully-initialized value of `T` (true for the
    /// Montgomery field types and their SIMD packings, whose `ZERO` is all-zero bytes).
    #[inline]
    #[must_use]
    pub unsafe fn zeroed(n: usize) -> Self {
        // SAFETY: every slot is initialized by the `write_bytes` below before it can be read.
        let mut v = unsafe { Self::uninitialized(n) };
        // SAFETY: `v` owns `n` allocated slots; caller guarantees all-zero is a valid `T`.
        unsafe { ptr::write_bytes(v.as_mut_ptr(), 0u8, n) };
        v
    }

    /// Arena-backed `slice.to_vec()`.
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

    /// `len` uninitialized slots.
    ///
    /// # Safety
    /// Every element must be overwritten before it is read.
    #[inline]
    #[must_use]
    pub unsafe fn uninitialized(len: usize) -> Self {
        let mut v = Self::with_capacity(len);
        // SAFETY: caller guarantees all `len` slots are written before being read.
        unsafe { v.set_len(len) };
        v
    }

    /// Arena-backed parallel `(0..n).map(f).collect()`: fill a vector of length `n` in parallel.
    /// The single allocation happens on the calling thread; workers write disjoint slots.
    #[inline]
    #[must_use]
    pub fn par_collect<F: Fn(usize) -> T + Sync>(n: usize, f: F) -> Self
    where
        T: Send,
    {
        // SAFETY: `par_fill` writes every slot in `0..n` exactly once before any is read.
        let mut v = unsafe { Self::uninitialized(n) };
        parallel::par_fill(&mut v, f);
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

    #[inline]
    pub fn as_mut_slice(&mut self) -> &mut [T] {
        self
    }

    /// Set the length without touching the buffer.
    ///
    /// # Safety
    /// `new_len <= capacity()` and every element in `0..new_len` must be initialized.
    #[inline]
    pub unsafe fn set_len(&mut self, new_len: usize) {
        debug_assert!(new_len <= self.cap);
        self.len = new_len;
    }

    /// Reserve space for at least `additional` more elements (amortized doubling).
    #[inline]
    pub fn reserve(&mut self, additional: usize) {
        if size_of::<T>() == 0 {
            return; // capacity is conceptually unbounded for ZSTs
        }
        let required = self.len.checked_add(additional).expect("ArenaVec capacity overflow");
        if required > self.cap {
            let new_cap = cmp::max(required, self.cap.saturating_mul(2));
            self.realloc_to(new_cap);
        }
    }

    #[inline]
    pub fn push(&mut self, value: T) {
        if self.len == self.cap {
            // ZSTs never reach here (cap == usize::MAX); only sized types grow.
            let new_cap = cmp::max(self.cap.saturating_mul(2), 4);
            self.realloc_to(new_cap);
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
        // Bump `len` per element so a panic mid-clone leaves a consistent vector (written clones drop).
        for x in other {
            // SAFETY: `reserve` guaranteed room for `other.len()` more; `len` stays < `cap`.
            unsafe { self.ptr.as_ptr().add(self.len).write(x.clone()) };
            self.len += 1;
        }
    }

    /// Grow or shrink to `new_len`, filling new slots with clones of `value`.
    pub fn resize(&mut self, new_len: usize, value: T)
    where
        T: Clone,
    {
        if new_len > self.len {
            self.reserve(new_len - self.len);
            while self.len < new_len {
                // SAFETY: room reserved above; `len < new_len <= cap`.
                unsafe { self.ptr.as_ptr().add(self.len).write(value.clone()) };
                self.len += 1;
            }
        } else {
            self.truncate(new_len);
        }
    }

    /// Drop the elements past `len`, keeping capacity.
    pub fn truncate(&mut self, len: usize) {
        if len < self.len {
            let drop_count = self.len - len;
            // Shorten first so a panicking `Drop` can't observe/double-drop the tail.
            self.len = len;
            // SAFETY: `[len, old_len)` were initialized and are now logically removed.
            unsafe {
                ptr::drop_in_place(ptr::slice_from_raw_parts_mut(self.ptr.as_ptr().add(len), drop_count));
            }
        }
    }

    #[inline]
    pub fn clear(&mut self) {
        self.truncate(0);
    }

    /// Decompose into raw parts, leaking the buffer. Inverse of [`from_raw_parts`](Self::from_raw_parts).
    #[inline]
    #[must_use]
    pub fn into_raw_parts(self) -> (*mut T, usize, usize) {
        let me = ManuallyDrop::new(self);
        (me.ptr.as_ptr(), me.len, me.cap)
    }

    /// Reconstruct from parts previously obtained via [`into_raw_parts`](Self::into_raw_parts)
    /// (or a layout-compatible reinterpret thereof).
    ///
    /// # Safety
    /// `ptr` is non-null and aligned for `T`; `len <= cap`; and `ptr` either was returned by
    /// [`raw_alloc`](crate::raw_alloc) for `cap * size_of::<T>()` bytes at `align_of::<T>()`, or
    /// `cap == 0` and `ptr` is dangling-but-aligned. Exactly one `ArenaVec` may own a given pointer.
    #[inline]
    #[must_use]
    pub unsafe fn from_raw_parts(ptr: *mut T, len: usize, cap: usize) -> Self {
        Self {
            // SAFETY: caller guarantees `ptr` is non-null.
            ptr: unsafe { NonNull::new_unchecked(ptr) },
            len,
            cap,
            _marker: PhantomData,
        }
    }

    /// Allocate a fresh `new_cap`-element buffer, move the `len` live elements into it, and free
    /// the old one. Only called for sized `T` with `new_cap >= len` and `new_cap > 0`.
    fn realloc_to(&mut self, new_cap: usize) {
        debug_assert!(size_of::<T>() != 0 && new_cap >= self.len && new_cap > 0);
        let align = align_of::<T>();
        let new_bytes = new_cap.checked_mul(size_of::<T>()).expect("ArenaVec capacity overflow");
        assert!(new_bytes <= isize::MAX as usize, "ArenaVec capacity overflow");

        // SAFETY: `align` is a valid power of two; `new_bytes > 0`.
        let raw = unsafe { raw_alloc(new_bytes, align) }.cast::<T>();
        let Some(new_ptr) = NonNull::new(raw) else {
            // Matches `Vec`: an allocation failure aborts rather than unwinds.
            handle_alloc_error(unsafe { std::alloc::Layout::from_size_align_unchecked(new_bytes, align) });
        };

        if self.cap != 0 {
            // SAFETY: the two buffers are distinct; `len <= old cap` initialized elements move.
            unsafe { ptr::copy_nonoverlapping(self.ptr.as_ptr(), new_ptr.as_ptr(), self.len) };
            // SAFETY: old buffer came from `raw_alloc` with this size/align (range-checked free).
            unsafe { raw_dealloc(self.ptr.as_ptr().cast::<u8>(), self.cap * size_of::<T>(), align) };
        }
        self.ptr = new_ptr;
        self.cap = new_cap;
    }
}

impl<T> Drop for ArenaVec<T> {
    fn drop(&mut self) {
        // Drop the live elements first (no-op for `Copy`/trivial types; the compiler elides it).
        if std::mem::needs_drop::<T>() {
            // SAFETY: `0..len` are initialized.
            unsafe { ptr::drop_in_place(ptr::slice_from_raw_parts_mut(self.ptr.as_ptr(), self.len)) };
        }
        // Free the buffer. ZSTs and never-allocated vectors own nothing.
        if size_of::<T>() != 0 && self.cap != 0 {
            // SAFETY: buffer came from `raw_alloc(cap * size, align)`; `raw_dealloc` range-checks
            // arena-vs-system. Arena pointers free as a no-op (reclaimed at the next phase reset).
            unsafe {
                raw_dealloc(
                    self.ptr.as_ptr().cast::<u8>(),
                    self.cap * size_of::<T>(),
                    align_of::<T>(),
                )
            };
        }
    }
}

impl<T> Deref for ArenaVec<T> {
    type Target = [T];
    #[inline]
    fn deref(&self) -> &[T] {
        // SAFETY: `ptr` is aligned and `0..len` are initialized (valid for ZSTs too: a dangling
        // aligned pointer is a valid base for a zero-byte-stride slice).
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

impl<T> AsRef<[T]> for ArenaVec<T> {
    #[inline]
    fn as_ref(&self) -> &[T] {
        self
    }
}

impl<T> AsMut<[T]> for ArenaVec<T> {
    #[inline]
    fn as_mut(&mut self) -> &mut [T] {
        self
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
        let mut out = Self::with_capacity(self.len);
        out.extend_from_slice(self);
        out
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
