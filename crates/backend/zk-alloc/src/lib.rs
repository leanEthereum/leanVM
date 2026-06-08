//! Bump-pointer arena, used explicitly (never as a `#[global_allocator]`). One mmap region split
//! into per-thread slabs: alloc bumps a thread-local pointer, free is a no-op, `begin_phase()`
//! resets every slab. Proof data lives in [`ArenaVec`]; `raw_dealloc` picks arena-vs-system by
//! pointer range, so `ArenaVec` carries no allocator parameter.

use std::alloc::{GlobalAlloc, Layout};
use std::cell::Cell;
use std::sync::OnceLock;
use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering};

use system_info::NUM_THREADS;

mod arena_cow;
mod arena_vec;
mod syscall;

pub use arena_cow::ArenaCow;
pub use arena_vec::{ArenaVec, OwnedBuffer};

/// Build an [`ArenaVec`], mirroring [`std::vec!`]:
#[macro_export]
macro_rules! arena_vec {
    () => { $crate::ArenaVec::new() };
    ($elem:expr; $n:expr) => { $crate::ArenaVec::filled($elem, $n) };
    ($($x:expr),+ $(,)?) => { $crate::ArenaVec::from_iter([$($x),+]) };
}

const SLAB_SIZE: usize = 8 << 30; // 8 GiB; per-thread soft cap, overflow falls back to System
const SLACK: usize = 4; // extra slabs for non-pool threads that allocate in a phase
const MAX_THREADS: usize = NUM_THREADS + SLACK;
const REGION_SIZE: usize = SLAB_SIZE * MAX_THREADS; // one contiguous region => O(1) pointer classification

/// Bumped by `begin_phase()`; a thread resets its slab when its cached `ARENA_GEN` lags — one store
/// resets every thread, lock-free.
static GENERATION: AtomicUsize = AtomicUsize::new(0);
/// Arena on (route to arena) vs off (route to System).
static ARENA_ACTIVE: AtomicBool = AtomicBool::new(false);
/// Process-wide opt-in; gates `begin_phase`'s all-thread reset so a stray call can't corrupt another
/// proving's buffers. Until [`enable_arena`], phases are no-ops and `ArenaVec` uses System.
static ARENA_ENGAGED: AtomicBool = AtomicBool::new(false);
/// mmap'd region base, mapped once; also the arena-vs-system discriminator in `raw_dealloc`.
static REGION: OnceLock<usize> = OnceLock::new();
/// Slab index handed out once per thread; `idx >= MAX_THREADS` falls back to System.
static THREAD_IDX: AtomicUsize = AtomicUsize::new(0);

thread_local! {
    /// This thread's next allocation address.
    static ARENA_PTR: Cell<usize> = const { Cell::new(0) };
    /// One past this thread's slab.
    static ARENA_END: Cell<usize> = const { Cell::new(0) };
    /// This thread's slab base (`0` = unclaimed); the reset target.
    static ARENA_BASE: Cell<usize> = const { Cell::new(0) };
    /// Last `GENERATION` seen; a mismatch triggers a slab reset.
    static ARENA_GEN: Cell<usize> = const { Cell::new(0) };
    /// Thread got no slab (`idx >= MAX_THREADS`) — always uses System.
    static ARENA_NO_SLAB: Cell<bool> = const { Cell::new(false) };
}

fn ensure_region() -> usize {
    *REGION.get_or_init(|| {
        // SAFETY: mmap returns a page-aligned pointer or null; lazily backed.
        let ptr = unsafe { syscall::mmap_anonymous(REGION_SIZE) };
        if ptr.is_null() {
            std::process::abort();
        }
        unsafe { syscall::madvise(ptr, REGION_SIZE, syscall::MADV_NOHUGEPAGE) };
        ptr as usize
    })
}

/// Opt into the arena (once, at startup). Until then phases are inert and `ArenaVec` uses System.
pub fn enable_arena() {
    ARENA_ENGAGED.store(true, Ordering::Release);
}

/// Activate the arena and reset every thread's slab (overwriting the previous phase). No-op until
/// [`enable_arena`]; phases must not nest.
pub fn begin_phase() {
    if !ARENA_ENGAGED.load(Ordering::Acquire) {
        return;
    }
    let prev_active = ARENA_ACTIVE.swap(true, Ordering::Release);
    assert!(!prev_active, "phases must not nest");
    GENERATION.fetch_add(1, Ordering::Release);
}

/// Deactivate the arena; existing arena pointers stay valid until the next `begin_phase()`.
pub fn end_phase() {
    if !ARENA_ENGAGED.load(Ordering::Acquire) {
        return;
    }
    ARENA_ACTIVE.store(false, Ordering::Release);
}

/// Guard that [`end_phase`]s on drop.
#[derive(Debug)]
pub struct PhaseGuard(());

impl Drop for PhaseGuard {
    fn drop(&mut self) {
        end_phase();
    }
}

/// [`begin_phase`] + an RAII guard that [`end_phase`]s on drop (incl. early return / panic).
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

/// [`ArenaVec`]'s allocator: bump the thread's slab in an active phase, else System. The cursor is
/// thread-local, so the Relaxed reads can't race — a stale read just costs one extra System alloc.
///
/// # Safety
/// `align` is a power of two; the result is valid for `size` bytes (or null on System failure) until
/// the next `begin_phase()`.
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

/// Free for [`raw_alloc`]: no-op for arena pointers (reclaimed at the next `begin_phase()`), else System.
///
/// # Safety
/// `ptr` came from [`raw_alloc`] with this `size`/`align`.
#[inline(always)]
pub(crate) unsafe fn raw_dealloc(ptr: *mut u8, size: usize, align: usize) {
    let addr = ptr as usize;
    if REGION
        .get()
        .is_some_and(|&base| addr >= base && addr < base + REGION_SIZE)
    {
        return; // arena pointer — free is a no-op
    }
    unsafe { std::alloc::System.dealloc(ptr, Layout::from_size_align_unchecked(size, align)) };
}
