//! Explicit arena allocation for proof buffers.
//!
//! [`ProverAlloc`] (re-exported from `zk-alloc`) is an `allocator_api2` allocator backed by
//! the proving arena. Storing proof data in [`ArenaVec`] lets the arena be used without
//! installing it as the process `#[global_allocator]`; outside a `begin_phase`/`end_phase`
//! window it transparently falls back to the system allocator.

use allocator_api2::vec::Vec as AllocVec;
pub use zk_alloc::ProverAlloc;

/// A `Vec` whose storage comes from the proving arena (or the system allocator when no
/// phase is active). Derefs to `&[T]`, so slice-based APIs accept it unchanged.
pub type ArenaVec<T> = AllocVec<T, ProverAlloc>;

/// Empty `ArenaVec`.
#[inline]
#[must_use]
pub fn arena_vec<T>() -> ArenaVec<T> {
    AllocVec::new_in(ProverAlloc)
}

/// `ArenaVec` with room for `cap` elements pre-reserved.
#[inline]
#[must_use]
pub fn arena_with_capacity<T>(cap: usize) -> ArenaVec<T> {
    AllocVec::with_capacity_in(cap, ProverAlloc)
}

/// Arena-backed `vec![value; n]`.
#[inline]
#[must_use]
pub fn arena_filled<T: Clone>(value: T, n: usize) -> ArenaVec<T> {
    let mut v = arena_with_capacity(n);
    v.resize(n, value);
    v
}

/// Collect an iterator into an `ArenaVec`.
#[inline]
#[must_use]
pub fn arena_collect<T, I: IntoIterator<Item = T>>(iter: I) -> ArenaVec<T> {
    let iter = iter.into_iter();
    let mut v = arena_with_capacity(iter.size_hint().0);
    v.extend(iter);
    v
}

/// Arena-backed `slice.to_vec()`.
#[inline]
#[must_use]
pub fn arena_from_slice<T: Clone>(slice: &[T]) -> ArenaVec<T> {
    let mut v = arena_with_capacity(slice.len());
    v.extend_from_slice(slice);
    v
}

/// Arena-backed [`uninitialized_vec`](crate::uninitialized_vec): `len` uninitialized slots.
///
/// # Safety
/// Every element must be overwritten before it is read.
#[inline]
#[must_use]
pub unsafe fn uninitialized_arena_vec<T>(len: usize) -> ArenaVec<T> {
    let mut v = arena_with_capacity(len);
    // SAFETY: caller guarantees all `len` slots are written before being read.
    unsafe { v.set_len(len) };
    v
}
