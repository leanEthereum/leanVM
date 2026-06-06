//! Explicit arena allocation for proof buffers.
//!
//! [`ArenaVec`] is [`zk_alloc::ArenaVec`]: an owning vector that bumps from the proving arena inside a
//! phase and falls back to the system allocator outside one. `Deref<Target = [T]>` lets it drop
//! into slice-based APIs unchanged.

pub use zk_alloc::ArenaVec;

/// Empty `ArenaVec`.
#[inline]
#[must_use]
pub fn arena_vec<T>() -> ArenaVec<T> {
    ArenaVec::new()
}

/// `ArenaVec` with room for `cap` elements pre-reserved.
#[inline]
#[must_use]
pub fn arena_with_capacity<T>(cap: usize) -> ArenaVec<T> {
    ArenaVec::with_capacity(cap)
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

/// Arena-backed parallel `(0..n).map(f).collect()`: fill an `ArenaVec` of length `n` in parallel.
/// The single allocation happens on the calling thread; workers write disjoint slots.
#[inline]
#[must_use]
pub fn arena_par_collect<T: Send, F: Fn(usize) -> T + Sync>(n: usize, f: F) -> ArenaVec<T> {
    // SAFETY: `par_fill` writes every slot in `0..n` exactly once before any is read.
    let mut v = unsafe { uninitialized_arena_vec(n) };
    parallel::par_fill(&mut v, f);
    v
}
