//! Anonymous `mmap` + `madvise` via `libc`.
//!
//! (Raw inline-asm syscalls when zk-alloc was a `#[global_allocator]`, to avoid `libc` re-entering
//! `malloc`. It no longer is, so `libc` is safe: its internal allocations hit the system allocator,
//! not this arena.)

use std::ptr;

/// `madvise` advice: disable transparent huge pages for the region. Consulted only on Linux
/// (a no-op elsewhere); see [`madvise`].
pub const MADV_NOHUGEPAGE: usize = 15;

/// Reserve `size` bytes of anonymous virtual address space, lazily backed by physical pages.
///
/// # Safety
/// Always safe to call; returns a page-aligned pointer or null on failure, and the caller owns the
/// resulting mapping.
#[inline]
pub unsafe fn mmap_anonymous(size: usize) -> *mut u8 {
    let flags = libc::MAP_PRIVATE | libc::MAP_ANON;
    // MAP_NORESERVE (Linux) keeps the huge sparse reservation from committing swap up front; macOS
    // backs anonymous mappings lazily without it.
    #[cfg(target_os = "linux")]
    let flags = flags | libc::MAP_NORESERVE;
    // SAFETY: a null `addr` lets the kernel pick the placement; `fd` is -1 for an anonymous map.
    let ret = unsafe { libc::mmap(ptr::null_mut(), size, libc::PROT_READ | libc::PROT_WRITE, flags, -1, 0) };
    if ret == libc::MAP_FAILED {
        ptr::null_mut()
    } else {
        ret.cast::<u8>()
    }
}

/// Apply `advice` to `[ptr, ptr + size)`. No-op on non-Linux (the advice values we use are
/// Linux-specific).
///
/// # Safety
/// `ptr`/`size` must describe a live mapping returned by [`mmap_anonymous`].
#[inline]
pub unsafe fn madvise(ptr: *mut u8, size: usize, advice: usize) {
    #[cfg(target_os = "linux")]
    unsafe {
        // SAFETY: the caller guarantees `[ptr, ptr + size)` is a live mapping.
        libc::madvise(ptr.cast::<libc::c_void>(), size, advice as libc::c_int);
    }
    #[cfg(not(target_os = "linux"))]
    {
        let _ = (ptr, size, advice);
    }
}
