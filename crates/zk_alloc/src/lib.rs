//! Bump arena for proving buffers. A new phase requires every arena allocation from the previous phase to be released.
//!
//! # Reuse within a phase
//!
//! A prover is a pipeline: a stage's output is allocated while its input is
//! still live and the input dies first, so lifetimes are not nested and popping
//! the cursor reclaims almost nothing. Blocks of at least [`REUSE_MIN`] go to a
//! per-thread free list on release; anything it cannot serve falls back to the
//! bump.
//!
//! `ZK_ALLOC_POISON=1` fills released blocks and reclaimed phase storage.
//!
//! Live buffers prevent a reset, including buffers moved to another thread.
//!
//! # Usage
//!
//! ```no_run
//! zk_alloc::enable_arena(); // once, at startup
//! let _phase = zk_alloc::enter_phase(); // bind before the phase's buffers
//! let buf: zk_alloc::ArenaVec<u64> = zk_alloc::ArenaVec::with_capacity(1 << 20);
//! ```

use std::alloc::{GlobalAlloc, Layout, System};
use std::cell::Cell;
use std::mem::forget;
use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering};
use std::sync::{Mutex, OnceLock};

mod arena_vec;
mod syscall;

pub use arena_vec::{ArenaVec, alloc_uninit, assume_init};

/// Address space reserved per thread. Overflow falls back to the system allocator.
///
/// Miri backs the region with real memory, so there a slab is small.
const SLAB_SIZE: usize = if cfg!(miri) { 1 << 20 } else { 64 << 30 };

/// Extra slabs for non-pool threads that allocate during a phase.
const SLACK: usize = 8;

/// Minimum alignment for allocations at least this large.
const CACHE_LINE: usize = 64;

/// Smallest block the reuse list tracks: below it, small allocations are too
/// numerous to be worth a scan and too small to move the resident set.
///
/// Under Miri it shrinks with the slab, so the reuse list still runs.
pub const REUSE_MIN: usize = if cfg!(miri) { 1 << 12 } else { 1 << 20 };

/// Freed blocks one thread's list holds; generous, since the prover's large
/// buffers are few.
const FREE_LIST_CAP: usize = 128;

/// The alignment a `size`-byte request is actually served at. [`raw_alloc`] and
/// [`raw_dealloc`] must agree on it, or a system buffer would be freed under a
/// layout it was not allocated with.
const fn effective_align(size: usize, align: usize) -> usize {
    if size >= CACHE_LINE && align < CACHE_LINE {
        CACHE_LINE
    } else {
        align
    }
}

#[inline(always)]
const fn align_up(addr: usize, align: usize) -> usize {
    (addr + align - 1) & !(align - 1)
}

/// One thread's released blocks: inside its own slab, below its cursor, and
/// pairwise NON-ADJACENT, since `store` inserts only merged unions and `take`
/// carves strictly inside a block.
struct FreeList {
    blocks: [(usize, usize); FREE_LIST_CAP],
    len: usize,
}

impl FreeList {
    const EMPTY: Self = Self {
        blocks: [(0, 0); FREE_LIST_CAP],
        len: 0,
    };

    #[inline]
    const fn remove(&mut self, i: usize) {
        self.len -= 1;
        self.blocks[i] = self.blocks[self.len];
    }

    /// First block that fits, carved from its low end. The carve is NOT
    /// optional: without it one request consumes a whole merged union.
    fn take(&mut self, size: usize) -> Option<usize> {
        let i = self.blocks[..self.len].iter().position(|&(_, len)| len >= size)?;
        let (addr, len) = self.blocks[i];
        // Realigned, so the remainder is still a legal block to hand out.
        let rest = align_up(addr + size, CACHE_LINE);
        let rest_len = (addr + len).saturating_sub(rest);
        if rest_len >= REUSE_MIN {
            self.blocks[i] = (rest, rest_len);
        } else {
            self.remove(i);
        }
        Some(addr)
    }

    /// Absorb the held blocks adjacent to `[addr, addr + size)` and return the
    /// union. Held blocks are non-adjacent, so at most one lies on each side.
    const fn merge(&mut self, addr: usize, size: usize) -> (usize, usize) {
        let (mut a, mut n) = (addr, size);
        let mut i = 0;
        while i < self.len {
            let (b, m) = self.blocks[i];
            if b + m == a {
                a = b;
                n += m;
            } else if a + n == b {
                n += m;
            } else {
                i += 1;
                continue;
            }
            // Swap-remove moves an unexamined block to `i`, so stay put. One
            // pass suffices only because held blocks are non-adjacent.
            self.remove(i);
        }
        (a, n)
    }

    /// Hold `[addr, size)`, or drop it when the list is full (an unheld block is
    /// just not recycled).
    const fn store(&mut self, addr: usize, size: usize) {
        if self.len < FREE_LIST_CAP {
            self.blocks[self.len] = (addr, size);
            self.len += 1;
        }
    }
}

fn max_threads() -> usize {
    static N: OnceLock<usize> = OnceLock::new();
    *N.get_or_init(|| std::thread::available_parallelism().map_or(1, |n| n.get()) + SLACK)
}

fn region_size() -> usize {
    SLAB_SIZE * max_threads()
}

/// Bumped by [`begin_phase`]; a thread resets its slab when its cached
/// `ARENA_GEN` lags, so one store resets every thread without a lock.
static GENERATION: AtomicUsize = AtomicUsize::new(0);
/// Low bits admit allocations or reserve a phase transition; upper bits count live allocations.
static PHASE: AtomicUsize = AtomicUsize::new(0);
const ACTIVE: usize = 1;
const OPENING: usize = 2;
const ALLOCATION: usize = 4;

/// Holds a reset barrier until an allocation owns it, including during unwinding.
struct AllocationLease;

impl AllocationLease {
    fn acquire() -> Option<Self> {
        let mut state = PHASE.load(Ordering::Acquire);
        while state & ACTIVE != 0 {
            let next = state.checked_add(ALLOCATION).expect("arena allocation count overflow");
            match PHASE.compare_exchange_weak(state, next, Ordering::AcqRel, Ordering::Acquire) {
                Ok(_) => return Some(Self),
                Err(current) => state = current,
            }
        }
        None
    }
}

impl Drop for AllocationLease {
    fn drop(&mut self) {
        PHASE.fetch_sub(ALLOCATION, Ordering::Release);
    }
}
/// Process-wide opt-in. Until [`enable_arena`], phases are inert and `ArenaVec`
/// is a plain system-allocated vector, so a stray [`begin_phase`] in a process
/// that never opted in cannot invalidate anything.
static ARENA_ENGAGED: AtomicBool = AtomicBool::new(false);
/// Base of the reservation, mapped once. Also the arena-vs-system discriminator
/// in [`raw_dealloc`].
static REGION: OnceLock<usize> = OnceLock::new();
/// Slab indices handed out one per thread; `idx >= max_threads()` gets none.
static NEXT_SLAB: AtomicUsize = AtomicUsize::new(0);
/// Slabs whose threads have exited, each with the generation it was retired in.
///
/// A retired slab may still back a buffer another thread owns, until the next phase opens.
/// Opening a phase requires every arena buffer to be released, so from then on the slab is free.
static RETIRED: Mutex<Vec<(usize, usize)>> = Mutex::new(Vec::new());

/// High-water mark of any single thread's slab use, in bytes.
static HIGH_WATER: AtomicUsize = AtomicUsize::new(0);
/// Bytes that overflowed a slab mid-phase and went to the system allocator.
static OVERFLOW_BYTES: AtomicUsize = AtomicUsize::new(0);
/// Peak slab use summed over all threads and phases, accumulated one atomic per
/// thread per phase (at reset).
/// The PEAK, not the total bumped: with reuse the cursor moves both ways.
static ARENA_BYTES: AtomicUsize = AtomicUsize::new(0);

/// `ZK_ALLOC_POISON`, resolved in [`enable_arena`] with the rest of the
/// process-wide policy, so the release path pays one relaxed load.
static POISON: AtomicBool = AtomicBool::new(false);

thread_local! {
    static FREE: std::cell::RefCell<FreeList> = const { std::cell::RefCell::new(FreeList::EMPTY) };
    /// Highest cursor address reached in the phase in flight. The cursor
    /// retreats when a release tops it, so its final value is not its peak.
    static HIGH: Cell<usize> = const { Cell::new(0) };
    static PTR: Cell<usize> = const { Cell::new(0) };
    static END: Cell<usize> = const { Cell::new(0) };
    static BASE: Cell<usize> = const { Cell::new(0) };
    static GEN: Cell<usize> = const { Cell::new(0) };
    static NO_SLAB: Cell<bool> = const { Cell::new(false) };
    /// Retires this thread's slab when the thread exits.
    static OWNER: SlabOwner = const { SlabOwner(Cell::new(None)) };
}

/// The slab index a thread owns, handed back when the thread exits.
struct SlabOwner(Cell<Option<usize>>);

impl Drop for SlabOwner {
    fn drop(&mut self) {
        if let Some(idx) = self.0.get() {
            let generation = GENERATION.load(Ordering::Relaxed);
            RETIRED
                .lock()
                .unwrap_or_else(|e| e.into_inner())
                .push((idx, generation));
        }
    }
}

/// A slab for a thread that has none: a retired one a phase has opened since, else a fresh one.
///
/// Without reuse, every thread that ever allocated would keep its slab's pages resident.
fn claim_slab(generation: usize) -> Option<usize> {
    let mut retired = RETIRED.lock().unwrap_or_else(|e| e.into_inner());
    if let Some(i) = retired.iter().position(|&(_, g)| g < generation) {
        return Some(retired.swap_remove(i).0);
    }
    drop(retired);
    let idx = NEXT_SLAB.fetch_add(1, Ordering::Relaxed);
    (idx < max_threads()).then_some(idx)
}

fn region() -> usize {
    *REGION.get_or_init(|| {
        let size = region_size();
        // SAFETY: `reserve` returns a page-aligned pointer or null.
        let ptr = unsafe { syscall::reserve(size) };
        assert!(
            !ptr.is_null(),
            "zk_alloc could not reserve {} GiB of address space",
            size >> 30
        );
        // SAFETY: the mapping we just made is live and exactly `size` bytes.
        unsafe { syscall::disable_huge_pages(ptr, size) };
        ptr as usize
    })
}

/// Opt into the arena. Call once at startup, before any proving.
///
/// Until this is called, phases are inert and [`ArenaVec`] is a plain
/// system-allocated vector, which is the right configuration for a
/// memory-constrained host, at the cost of the page-fault churn described in the
/// module docs.
pub fn enable_arena() {
    syscall::retain_system_heap();
    POISON.store(std::env::var_os("ZK_ALLOC_POISON").is_some(), Ordering::Relaxed);
    ARENA_ENGAGED.store(true, Ordering::Release);
}

/// Whether [`enable_arena`] has been called.
#[must_use]
pub fn is_enabled() -> bool {
    ARENA_ENGAGED.load(Ordering::Acquire)
}

/// Open a phase after every allocation from the preceding phase has been released.
///
/// # Panics
/// A phase is already open or an arena allocation is still live.
pub(crate) fn begin_phase() -> bool {
    if !is_enabled() {
        return false;
    }
    assert!(
        PHASE
            .compare_exchange(0, OPENING, Ordering::Acquire, Ordering::Relaxed)
            .is_ok(),
        "an arena phase is already open or an arena allocation is still live"
    );
    GENERATION.fetch_add(1, Ordering::Relaxed);
    PHASE.store(ACTIVE, Ordering::Release);
    true
}

/// Stop admitting allocations without releasing any live buffer's reset barrier.
pub(crate) fn end_phase() {
    PHASE.fetch_and(!ACTIVE, Ordering::Release);
}

/// Closes allocation admission on drop; live buffers remain valid.
#[derive(Debug)]
pub struct PhaseGuard(bool);

impl Drop for PhaseGuard {
    fn drop(&mut self) {
        if self.0 {
            end_phase();
        }
    }
}

/// Open a phase and close allocation admission on drop.
///
/// Arena buffers may outlive this guard, but must be dropped before the next phase.
///
/// # Panics
/// A phase is already open or an arena allocation is still live.
#[must_use = "the phase ends as soon as the guard is dropped"]
pub fn enter_phase() -> PhaseGuard {
    PhaseGuard(begin_phase())
}

/// What the arena did, for sizing `SLAB_SIZE` and checking that the buffers
/// meant to be arena-backed actually are.
#[derive(Clone, Copy, Debug)]
pub struct Stats {
    /// Phases opened so far.
    pub phases: usize,
    /// Slabs handed out so far, i.e. threads that have allocated in a phase.
    pub threads: usize,
    /// Peak slab use summed over the threads that have published one. A thread
    /// publishes when it RESETS, so a phase counts only for the threads that
    /// allocate again afterwards: a worker that exits, and the phase in flight,
    /// are both missing. An underestimate of the arena's footprint, in other
    /// words, and the pool's steady threads are what make it a useful one.
    pub peak_bytes: usize,
    /// Largest peak any single thread reached within a phase, in bytes. Compare
    /// against [`Stats::slab_size`].
    pub high_water: usize,
    /// Bytes that overflowed a slab mid-phase and fell back to the system
    /// allocator. Nonzero means `SLAB_SIZE` is too small for this workload.
    pub overflow: usize,
    /// The per-thread slab size this build was compiled with.
    pub slab_size: usize,
}

/// Snapshot the arena's accounting. `peak_bytes` and `high_water` are published
/// when a thread resets its slab, so read them after at least one
/// [`enter_phase`] has followed the phase of interest.
#[must_use]
pub fn stats() -> Stats {
    Stats {
        phases: GENERATION.load(Ordering::Relaxed),
        threads: NEXT_SLAB.load(Ordering::Relaxed).min(max_threads()),
        peak_bytes: ARENA_BYTES.load(Ordering::Relaxed),
        high_water: HIGH_WATER.load(Ordering::Relaxed),
        overflow: OVERFLOW_BYTES.load(Ordering::Relaxed),
        slab_size: SLAB_SIZE,
    }
}

impl std::fmt::Display for Stats {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let bytes_to_gib = |bytes: usize| bytes as f64 / (1u64 << 30) as f64;
        // A thread publishes its peak when it RESETS, so the phase in flight is
        // not in the sum: report the count the average is actually over.
        let completed = self.phases.saturating_sub(1);
        let per_phase = bytes_to_gib(self.peak_bytes) / completed.max(1) as f64;
        write!(
            f,
            "arena: {:.2} GiB/phase over {} completed phase(s) on {} thread(s); \
             high water {:.2} of {} GiB per slab; overflow {:.2} GiB",
            per_phase,
            completed,
            self.threads,
            bytes_to_gib(self.high_water),
            self.slab_size >> 30,
            bytes_to_gib(self.overflow),
        )
    }
}

/// The allocation slow path: this thread's cursor is stale (a new phase, or a
/// first-ever allocation), or its slab is full.
#[cold]
#[inline(never)]
unsafe fn alloc_slow(size: usize, align: usize) -> *mut u8 {
    let generation = GENERATION.load(Ordering::Relaxed);
    if !NO_SLAB.get() && GEN.get() != generation {
        let mut base = BASE.get();
        if base == 0 {
            let Some(idx) = claim_slab(generation) else {
                // More live allocating threads than slabs: this one uses System forever.
                NO_SLAB.set(true);
                OVERFLOW_BYTES.fetch_add(size, Ordering::Relaxed);
                // SAFETY: this function's caller passes a power-of-two `align` and a nonzero `size`.
                return unsafe { system_alloc(size, align) };
            };
            // A thread already exiting has no owner to retire the slab: it just stays claimed.
            let _ = OWNER.try_with(|owner| owner.0.set(Some(idx)));
            base = region() + idx * SLAB_SIZE;
            BASE.set(base);
            END.set(base + SLAB_SIZE);
        } else {
            // The PEAK, not where the cursor ended: reuse moves it both ways.
            let peak = HIGH.get().max(PTR.get()) - base;
            ARENA_BYTES.fetch_add(peak, Ordering::Relaxed);
            HIGH_WATER.fetch_max(peak, Ordering::Relaxed);
            if POISON.load(Ordering::Relaxed) {
                // SAFETY: a new phase requires all preceding allocations to be released.
                // The range lies within this thread's slab.
                unsafe { std::ptr::write_bytes(base as *mut u8, 0xCD, peak) };
            }
        }
        // Allocation leases prevent a generation change while this slab is in use.
        PTR.set(base);
        HIGH.set(base);
        FREE.with(|f| f.borrow_mut().len = 0);
        GEN.set(generation);
        let aligned = align_up(base, align);
        let bumped = aligned + size;
        if bumped <= END.get() {
            PTR.set(bumped);
            return aligned as *mut u8;
        }
    }
    // Slab exhausted (or none owned): fall back, and record it so `stats()` can
    // report that SLAB_SIZE is undersized for this workload.
    OVERFLOW_BYTES.fetch_add(size, Ordering::Relaxed);
    // SAFETY: this function's caller passes a power-of-two `align` and a nonzero `size`.
    unsafe { system_alloc(size, align) }
}

#[inline]
unsafe fn system_alloc(size: usize, align: usize) -> *mut u8 {
    // SAFETY: `align` is a power of two and `size` is nonzero (callers check).
    unsafe { System.alloc(Layout::from_size_align_unchecked(size, align)) }
}

/// [`ArenaVec`]'s allocator: bump this thread's slab inside a phase, else use
/// the system allocator.
///
/// The cursor is thread-local, so the relaxed loads cannot race: a stale
/// `GENERATION` read only sends this call down [`alloc_slow`].
///
/// # Safety
/// `align` must be a power of two and `size` nonzero. The result is valid for
/// `size` bytes (or null, if the system allocator failed) until it is released.
#[inline(always)]
pub(crate) unsafe fn raw_alloc(size: usize, align: usize) -> *mut u8 {
    let align = effective_align(size, align);
    if let Some(lease) = AllocationLease::acquire() {
        if GEN.get() == GENERATION.load(Ordering::Relaxed) {
            // Recycle first, so a phase's cursor tracks its live set. At this
            // size `effective_align` has already raised any smaller request to
            // `CACHE_LINE`, which every listed address is aligned to.
            if size >= REUSE_MIN
                && align <= CACHE_LINE
                && let Some(addr) = alloc_reuse(size)
            {
                forget(lease);
                return addr;
            }
            let aligned = align_up(PTR.get(), align);
            let bumped = aligned + size;
            if bumped <= END.get() {
                PTR.set(bumped);
                forget(lease);
                return aligned as *mut u8;
            }
        }
        // SAFETY: `align` is a power of two (the caller's, or `CACHE_LINE`) and `size` is the caller's nonzero size.
        let ptr = unsafe { alloc_slow(size, align) };
        if REGION
            .get()
            .is_some_and(|&base| (ptr as usize).wrapping_sub(base) < region_size())
        {
            forget(lease);
        }
        return ptr;
    }
    // SAFETY: as for the slow path above.
    unsafe { system_alloc(size, align) }
}

/// Serve `size` from this thread's free list. Out of line to keep the scan and
/// its panic edge out of every `ArenaVec` growth site.
#[inline(never)]
fn alloc_reuse(size: usize) -> Option<*mut u8> {
    FREE.with(|f| f.borrow_mut().take(size)).map(|a| a as *mut u8)
}

/// The cursor is about to retreat from `p`, and only ever falls here, so this is
/// where it peaks. Keeps the allocation path free of accounting.
#[inline]
fn note_peak(p: usize) {
    if p > HIGH.get() {
        HIGH.set(p);
    }
}

/// Merge with any neighbour, then unwind the cursor if the union tops it and
/// hold it for reuse otherwise. Out of line, as [`alloc_reuse`].
#[inline(never)]
fn dealloc_large(addr: usize, size: usize) {
    FREE.with(|f| {
        let mut f = f.borrow_mut();
        let (a, n) = f.merge(addr, size);
        let p = PTR.get();
        if a + n == p {
            note_peak(p);
            PTR.set(a);
        } else {
            f.store(a, n);
        }
    });
}

/// The matching free: for an arena pointer, recycle it (at least [`REUSE_MIN`]
/// joins this thread's [`FreeList`], smaller pops the cursor if it tops it) or
/// leave it to the next [`begin_phase`]; for a system pointer, a system free.
///
/// Which one applies is decided by address range, not by a flag stored beside
/// the buffer, which is what lets [`ArenaVec`] carry no allocator parameter and
/// stay a single type whether or not a phase was open when it was built.
///
/// Recycling is safe NOT because of a cursor property (reuse puts live
/// allocations below the cursor), but because a block reaches the list only from
/// a release, which the caller performs only on a dead block, and
/// [`FreeList::take`] removes or carves whatever it hands out.
///
/// A block released on a thread other than its allocator is dropped here, the
/// list being thread-local. Not a rare class: `parallel`'s per-worker buffers
/// are built on the worker and dropped on the dispatcher. Fix it there.
///
/// # Safety
/// `ptr` came from [`raw_alloc`] with this `size` and `align`.
#[inline(always)]
pub(crate) unsafe fn raw_dealloc(ptr: *mut u8, size: usize, align: usize) {
    let addr = ptr as usize;
    if REGION
        .get()
        .is_some_and(|&base| addr >= base && addr - base < region_size())
    {
        // Release the reset barrier after all accesses to the slab are complete.
        let _lease = AllocationLease;
        // This thread's own slab, this phase only. BOTH bounds are load-bearing:
        // foreign releases are routine (`parallel` drops a worker's buffer on
        // the dispatcher), and `END` is 0 for a thread that never claimed a
        // slab. Live allocations prevent a generation change.
        if addr < BASE.get() || addr >= END.get() || GEN.get() != GENERATION.load(Ordering::Relaxed) {
            return;
        }
        if POISON.load(Ordering::Relaxed) {
            // SAFETY: the caller guarantees this block came from `raw_alloc`
            // with this size, and it is being released, so nothing may read it.
            unsafe { std::ptr::write_bytes(ptr, 0xCD, size) };
        }
        if size < REUSE_MIN {
            let p = PTR.get();
            if addr + size == p {
                note_peak(p);
                PTR.set(addr);
            }
            return;
        }
        dealloc_large(addr, size);
        return;
    }
    let align = effective_align(size, align);
    // SAFETY: the caller guarantees this pointer/layout pair came from
    // `raw_alloc`, and the range check above ruled out the arena.
    unsafe { System.dealloc(ptr, Layout::from_size_align_unchecked(size, align)) };
}

#[cfg(test)]
mod tests {
    use super::{ArenaVec, enable_arena, enter_phase};

    #[test]
    fn an_inert_guard_cannot_close_an_enabled_phase() {
        let inert = enter_phase();
        enable_arena();
        let active = enter_phase();
        drop(inert);
        assert!(std::panic::catch_unwind(enter_phase).is_err());

        let live = ArenaVec::filled(7u64, 8);
        drop(active);
        assert!(std::panic::catch_unwind(enter_phase).is_err());
        drop(live);
        let _phase = enter_phase();
    }
}
