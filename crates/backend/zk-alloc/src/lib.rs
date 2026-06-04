//! Bump-pointer arena allocator.
//!
//! One mmap region split into per-thread slabs. Allocation = increment a thread-local
//! pointer; free = no-op. `begin_phase()` resets the arena: each thread's next
//! allocation starts over at the beginning of its slab, overwriting the previous
//! phase's data. Allocations that don't fit (too large, or beyond `MAX_THREADS`) fall
//! back to the system allocator.
//!
//! ```ignore
//! loop {
//!     begin_phase();               // arena ON; slabs reset lazily
//!     let res = heavy_work();      // fast increments
//!     end_phase();                 // arena OFF; new allocations go to System
//!     let copy = res.clone();      // detach from arena before next phase resets it
//! }
//! ```

use std::alloc::{GlobalAlloc, Layout};
use std::cell::Cell;
use std::ptr::NonNull;
use std::sync::Once;
use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering};

use allocator_api2::alloc::{AllocError, Allocator};
use system_info::NUM_THREADS;

mod syscall;

const SLAB_SIZE: usize = 8 << 30; // 8GB
const SLACK: usize = 4; // SLACK absorbs the main thread and any non-rayon helpers.
const MAX_THREADS: usize = NUM_THREADS + SLACK;
const REGION_SIZE: usize = SLAB_SIZE * MAX_THREADS;

#[derive(Debug)]
pub struct ZkAllocator;

/// Incremented by `begin_phase()`. Every thread caches the last value it saw in
/// `ARENA_GEN`; when they differ, the thread resets its allocation cursor to the start
/// of its slab on the next allocation. This is how a single store on the main thread
/// "resets" every other thread's slab without any cross-thread synchronization.
static GENERATION: AtomicUsize = AtomicUsize::new(0);

/// Master switch for the arena. `true` (set by `begin_phase`) routes allocations
/// through the arena; `false` (set by `end_phase`) routes them to the system allocator.
static ARENA_ACTIVE: AtomicBool = AtomicBool::new(false);

/// Process-wide opt-in. Until [`enable_arena`] is called, `begin_phase`/`end_phase` are
/// no-ops and every allocation (global or [`ProverAlloc`]) goes to the system allocator.
///
/// The arena is a single-proving-at-a-time, process-global construct: a `begin_phase`
/// resets every thread's slab, which is only safe when one proving owns the process.
/// Gating activation behind an explicit opt-in keeps incidental `begin_phase` calls (e.g.
/// a benchmark invoked from a multi-test process that never installed the arena) from
/// silently hijacking and corrupting `ProverAlloc` buffers on other threads.
static ARENA_ENGAGED: AtomicBool = AtomicBool::new(false);

/// Base address of the mmap'd region, or `0` before `ensure_region` runs. Read on
/// every `dealloc` to test whether a pointer belongs to us.
static REGION_BASE: AtomicUsize = AtomicUsize::new(0);

/// Synchronizes the one-time mmap so concurrent first-allocators don't race.
static REGION_INIT: Once = Once::new();

/// Monotonic counter handed out to threads to pick their slab. `fetch_add`'d once per
/// thread on its first arena allocation. Threads that get `idx >= MAX_THREADS` mark
/// themselves `ARENA_NO_SLAB` and permanently fall through to the system allocator.
static THREAD_IDX: AtomicUsize = AtomicUsize::new(0);

thread_local! {
    /// Where this thread's next allocation lands. Advanced past each allocation.
    static ARENA_PTR: Cell<usize> = const { Cell::new(0) };
    /// One past the last byte of this thread's slab. An alloc fits iff
    /// `aligned + size <= ARENA_END`.
    static ARENA_END: Cell<usize> = const { Cell::new(0) };
    /// Base address of this thread's slab (`0` = not yet claimed). On reset,
    /// `ARENA_PTR` is set back to this value.
    static ARENA_BASE: Cell<usize> = const { Cell::new(0) };
    /// Last `GENERATION` value this thread observed. When the global moves past
    /// this, the next allocation resets `ARENA_PTR` to `ARENA_BASE` and updates
    /// this field.
    static ARENA_GEN: Cell<usize> = const { Cell::new(0) };
    /// `true` if this thread was created after `MAX_THREADS` was already exhausted.
    /// Such threads skip arena logic entirely and always go to the system allocator.
    static ARENA_NO_SLAB: Cell<bool> = const { Cell::new(false) };
}

/// Returns the base address of the mmap'd region, mapping it on the first call.
fn ensure_region() -> usize {
    REGION_INIT.call_once(|| {
        // SAFETY: mmap_anonymous returns a page-aligned pointer or null. MAP_NORESERVE
        // means no physical memory is committed until pages are touched.
        let ptr = unsafe { syscall::mmap_anonymous(REGION_SIZE) };
        if ptr.is_null() {
            std::process::abort();
        }
        unsafe { syscall::madvise(ptr, REGION_SIZE, syscall::MADV_NOHUGEPAGE) };
        REGION_BASE.store(ptr as usize, Ordering::Release);
    });
    REGION_BASE.load(Ordering::Acquire)
}

/// Opt into the arena for this process. Call once at startup, before any `begin_phase()`,
/// from a binary that owns the arena lifecycle (e.g. one that installs [`ZkAllocator`] as
/// `#[global_allocator]`, or one that drives proving through [`ProverAlloc`] buffers and
/// brackets it with `begin_phase`/`end_phase`). Until it is called, phases are inert and
/// everything uses the system allocator — see [`ARENA_ENGAGED`].
pub fn enable_arena() {
    ARENA_ENGAGED.store(true, Ordering::Release);
}

/// Activates the arena and resets every thread's slab. All allocations until the next
/// `end_phase()` go to the arena; the previous phase's data is overwritten in place.
///
/// No-op until [`enable_arena`] has opted the process into arena use.
pub fn begin_phase() {
    if !ARENA_ENGAGED.load(Ordering::Acquire) {
        return;
    }
    let prev_active = ARENA_ACTIVE.swap(true, Ordering::Release);
    assert!(
        !prev_active,
        "begin_phase() called while another phase is already active — phases must not nest"
    );
    GENERATION.fetch_add(1, Ordering::Release);
}

/// Deactivates the arena. New allocations go to the system allocator; existing arena
/// pointers stay valid until the next `begin_phase()` resets the slabs.
///
/// No-op until [`enable_arena`] has opted the process into arena use.
pub fn end_phase() {
    if !ARENA_ENGAGED.load(Ordering::Acquire) {
        return;
    }
    ARENA_ACTIVE.store(false, Ordering::Release);
}

#[cold]
#[inline(never)]
unsafe fn arena_alloc_cold(size: usize, align: usize) -> *mut u8 {
    let generation = GENERATION.load(Ordering::Relaxed);
    if !ARENA_NO_SLAB.get() && ARENA_GEN.get() != generation {
        let mut base = ARENA_BASE.get();
        if base == 0 {
            let region = ensure_region();
            let idx = THREAD_IDX.fetch_add(1, Ordering::Relaxed);
            if idx >= MAX_THREADS {
                ARENA_NO_SLAB.set(true);
                return unsafe { std::alloc::System.alloc(Layout::from_size_align_unchecked(size, align)) };
            }
            base = region + idx * SLAB_SIZE;
            ARENA_BASE.set(base);
            ARENA_END.set(base + SLAB_SIZE);
        }
        ARENA_PTR.set(base);
        ARENA_GEN.set(generation);
        let aligned = base.next_multiple_of(align);
        let new_ptr = aligned + size;
        if new_ptr <= ARENA_END.get() {
            ARENA_PTR.set(new_ptr);
            return aligned as *mut u8;
        }
    }
    unsafe { std::alloc::System.alloc(Layout::from_size_align_unchecked(size, align)) }
}

/// Shared allocation core: an arena bump while a phase is active and this thread's slab
/// is live, else a fallthrough to the system allocator. Used by both the process-wide
/// [`ZkAllocator`] (`GlobalAlloc`) and the explicit [`ProverAlloc`] (`Allocator`).
///
/// # Safety
/// `align` is a power of two; the returned pointer is valid for `size` bytes (or null on
/// system-allocator failure). Arena pointers stay valid until the next `begin_phase()`.
#[inline(always)]
unsafe fn raw_alloc(size: usize, align: usize) -> *mut u8 {
    if ARENA_ACTIVE.load(Ordering::Relaxed) {
        let generation = GENERATION.load(Ordering::Relaxed);
        if ARENA_GEN.get() == generation {
            let aligned = (ARENA_PTR.get() + align - 1) & !(align - 1);
            let new_ptr = aligned + size;
            if new_ptr <= ARENA_END.get() {
                ARENA_PTR.set(new_ptr);
                return aligned as *mut u8;
            }
        }
        return unsafe { arena_alloc_cold(size, align) };
    }
    unsafe { std::alloc::System.alloc(Layout::from_size_align_unchecked(size, align)) }
}

/// Free counterpart to [`raw_alloc`]: a no-op for arena-owned pointers (the slab is
/// reclaimed wholesale at the next `begin_phase()`), a system free otherwise.
///
/// # Safety
/// `ptr` came from [`raw_alloc`] with this `size`/`align`.
#[inline(always)]
unsafe fn raw_dealloc(ptr: *mut u8, size: usize, align: usize) {
    let addr = ptr as usize;
    let base = REGION_BASE.load(Ordering::Relaxed);
    if base != 0 && addr >= base && addr < base + REGION_SIZE {
        return; // arena-owned pointer — free is a no-op
    }
    unsafe { std::alloc::System.dealloc(ptr, Layout::from_size_align_unchecked(size, align)) };
}

// SAFETY: All pointers returned are either from our mmap'd region (valid, aligned,
// non-overlapping per thread) or from System. The arena is thread-local so no data
// races. Relaxed ordering on ARENA_ACTIVE/GENERATION is sound: worst case a thread
// sees a stale value and does one extra system-alloc before picking up the new
// generation on the next call.
unsafe impl GlobalAlloc for ZkAllocator {
    #[inline(always)]
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        unsafe { raw_alloc(layout.size(), layout.align()) }
    }

    #[inline(always)]
    unsafe fn dealloc(&self, ptr: *mut u8, layout: Layout) {
        unsafe { raw_dealloc(ptr, layout.size(), layout.align()) };
    }

    #[inline(always)]
    unsafe fn realloc(&self, ptr: *mut u8, layout: Layout, new_size: usize) -> *mut u8 {
        if new_size <= layout.size() {
            return ptr;
        }
        let new_ptr = unsafe { raw_alloc(new_size, layout.align()) };
        if !new_ptr.is_null() {
            unsafe { std::ptr::copy(ptr, new_ptr, layout.size()) };
            unsafe { raw_dealloc(ptr, layout.size(), layout.align()) };
        }
        new_ptr
    }
}

/// Explicit, `allocator_api2`-style handle onto the same arena as [`ZkAllocator`] —
/// **without** requiring the arena to be the process `#[global_allocator]`.
///
/// Attach it to the containers that hold proof data (`Vec<T, ProverAlloc>`,
/// `Box<T, ProverAlloc>`); every other allocation keeps the binary's own global
/// allocator. Inside a [`begin_phase`]/[`end_phase`] window it bump-allocates from the
/// arena; outside one it transparently uses the system allocator. Being a ZST it is
/// `Copy`, so threading it through container constructors costs nothing.
#[derive(Clone, Copy, Debug, Default)]
pub struct ProverAlloc;

// SAFETY: `allocate` hands out either a system pointer or a per-thread arena pointer
// (valid for the requested size, aligned, non-overlapping); `deallocate` only frees
// system pointers and treats arena pointers as no-ops, exactly as `GlobalAlloc` above.
// A returned arena pointer is invalidated by the next `begin_phase()` — the same
// "clone outputs before the next phase" contract the arena already documents.
unsafe impl Allocator for ProverAlloc {
    #[inline]
    fn allocate(&self, layout: Layout) -> Result<NonNull<[u8]>, AllocError> {
        let size = layout.size();
        if size == 0 {
            // allocator_api2 contract: a zero-sized request returns an aligned dangling
            // pointer without touching any allocator. align is a non-zero power of two.
            let dangling = unsafe { NonNull::new_unchecked(layout.align() as *mut u8) };
            return Ok(NonNull::slice_from_raw_parts(dangling, 0));
        }
        // SAFETY: size > 0; align is a valid power of two from `layout`.
        let ptr = unsafe { raw_alloc(size, layout.align()) };
        NonNull::new(ptr)
            .map(|nn| NonNull::slice_from_raw_parts(nn, size))
            .ok_or(AllocError)
    }

    #[inline]
    unsafe fn deallocate(&self, ptr: NonNull<u8>, layout: Layout) {
        if layout.size() == 0 {
            return; // never allocated (see `allocate`)
        }
        // SAFETY: `ptr`/`layout` come from a prior `allocate` on this allocator.
        unsafe { raw_dealloc(ptr.as_ptr(), layout.size(), layout.align()) };
    }
}
