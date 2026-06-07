//! Bump-pointer arena allocator, used **explicitly** (never as a `#[global_allocator]`).
//!
//! One mmap region split into per-thread slabs: allocation bumps a thread-local pointer, free is a
//! no-op, and `begin_phase()` resets every slab to its base (overwriting the previous phase).
//! Allocations that don't fit (too large, or beyond `MAX_THREADS`) fall back to the system
//! allocator. Proof data lives in [`ArenaVec<T>`], backed by `raw_alloc` / `raw_dealloc`; the latter
//! picks arena-vs-system by pointer range, so `ArenaVec` needs no allocator type parameter.
//!
//! ```ignore
//! enable_arena();                  // opt in once
//! loop {
//!     begin_phase();               // arena ON; slabs reset lazily
//!     let res = heavy_work();      // ArenaVec buffers bump; everything else stays on System
//!     end_phase();                 // arena OFF
//!     let copy = res.to_vec();     // detach before the next reset
//! }
//! ```

use std::alloc::{GlobalAlloc, Layout};
use std::cell::Cell;
use std::sync::OnceLock;
use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering};

use system_info::NUM_THREADS;

mod arena_vec;
mod syscall;

pub use arena_vec::ArenaVec;

const SLAB_SIZE: usize = 8 << 30; // 8 GiB
const SLACK: usize = 4; // SLACK absorbs the main thread and any non-rayon helpers.
const MAX_THREADS: usize = NUM_THREADS + SLACK;
const REGION_SIZE: usize = SLAB_SIZE * MAX_THREADS;

/// Incremented by `begin_phase()`. A thread whose cached `ARENA_GEN` differs resets its cursor to
/// its slab base on the next allocation — so one store "resets" every thread's slab, lock-free.
static GENERATION: AtomicUsize = AtomicUsize::new(0);

/// Master switch for the arena. `true` (set by `begin_phase`) routes allocations
/// through the arena; `false` (set by `end_phase`) routes them to the system allocator.
static ARENA_ACTIVE: AtomicBool = AtomicBool::new(false);

/// Process-wide opt-in. Until [`enable_arena`], `begin_phase`/`end_phase` are no-ops and every
/// [`ArenaVec`] uses the system allocator. Since `begin_phase` resets *every* thread's slab, it is only
/// safe when one proving owns the process; gating it keeps a stray `begin_phase` (e.g. a benchmark
/// reached from a concurrent test that never opted in) from corrupting other threads' buffers.
static ARENA_ENGAGED: AtomicBool = AtomicBool::new(false);

/// Base address of the mmap'd region, mapped once on first use (`None` until then). Read on every
/// `dealloc` to test whether a pointer belongs to us; the one-time init also races-safely here.
static REGION: OnceLock<usize> = OnceLock::new();

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
    *REGION.get_or_init(|| {
        // SAFETY: mmap_anonymous returns a page-aligned pointer or null. MAP_NORESERVE
        // means no physical memory is committed until pages are touched.
        let ptr = unsafe { syscall::mmap_anonymous(REGION_SIZE) };
        if ptr.is_null() {
            std::process::abort();
        }
        unsafe { syscall::madvise(ptr, REGION_SIZE, syscall::MADV_NOHUGEPAGE) };
        ptr as usize
    })
}

/// Opt into the arena for this process. Call once at startup, before any `begin_phase()`,
/// from a binary that owns the arena lifecycle (one proving at a time, driven through [`ArenaVec`]
/// buffers bracketed by `begin_phase`/`end_phase`). Until it is called, phases are inert and
/// every [`ArenaVec`] uses the system allocator — see [`ARENA_ENGAGED`].
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

/// Guard returned by [`enter_phase`]; calls [`end_phase`] when dropped.
#[derive(Debug)]
pub struct PhaseGuard(());

impl Drop for PhaseGuard {
    fn drop(&mut self) {
        end_phase();
    }
}

/// Open a proving phase ([`begin_phase`]) and return a guard that closes it ([`end_phase`]) on drop —
/// including on early return or panic, which hand-pairing the two calls does not guarantee. Phases
/// must not nest, so hold one guard at a time. No-op until [`enable_arena`].
#[must_use = "the phase ends the moment the guard is dropped"]
pub fn enter_phase() -> PhaseGuard {
    begin_phase();
    PhaseGuard(())
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

/// Allocation core for [`ArenaVec`]: an arena bump while a phase is active and this thread's slab
/// is live, else a fallthrough to the system allocator.
///
/// # Safety
/// `align` is a power of two; the returned pointer is valid for `size` bytes (or null on
/// system-allocator failure). Arena pointers stay valid until the next `begin_phase()`.
#[inline(always)]
pub(crate) unsafe fn raw_alloc(size: usize, align: usize) -> *mut u8 {
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
//
// SAFETY (allocation core): `raw_alloc` pointers come from our per-thread mmap'd region (valid,
// aligned, non-overlapping) or from System; the cursor is thread-local, so no data race. Relaxed
// ordering is sound — a stale read just costs one extra system-alloc before the next generation.
#[inline(always)]
pub(crate) unsafe fn raw_dealloc(ptr: *mut u8, size: usize, align: usize) {
    let addr = ptr as usize;
    if REGION
        .get()
        .is_some_and(|&base| addr >= base && addr < base + REGION_SIZE)
    {
        return; // arena-owned pointer — free is a no-op
    }
    unsafe { std::alloc::System.dealloc(ptr, Layout::from_size_align_unchecked(size, align)) };
}
