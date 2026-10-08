//! The heap as the global allocator counts it: the bytes live at once and the allocations made, over a window of the program ([`HeapWindow`]), which the resident set size cannot tell apart from what the allocator keeps.

use std::alloc::{GlobalAlloc, Layout};
use std::cell::Cell;
use std::sync::atomic::{AtomicIsize, AtomicU64, AtomicUsize, Ordering::Relaxed};

/// A global allocator that counts what `A` hands out: install it over the allocator in use, `bench::Counting(bench::Jemalloc)`.
///
/// - Each thread adds its allocations to a counter of its own, so counting is exact and threads never share a cache line for it.
/// - Each thread folds the bytes it allocates and frees into one global live count only once they move by 64 KiB or more, and the peak is taken when they fold. The live count misses under 64 KiB per thread that allocated, so a window's peak is within that many bytes of the true one.
pub struct Counting<A>(pub A);

/// Bytes a thread allocates or frees before it folds them into [`LIVE`].
const BATCH: usize = 64 << 10;

/// Live bytes, short of the true count by each thread's unfolded bytes.
static LIVE: AtomicIsize = AtomicIsize::new(0);

/// The most [`LIVE`] reached since the innermost open [`HeapWindow`] opened.
static PEAK: AtomicIsize = AtomicIsize::new(0);

/// Allocation counters, one per thread up to their number, each on a cache line of its own; later threads share them.
const SLOTS: usize = 128;

#[repr(align(128))]
struct Slot(AtomicU64);

static ALLOCATIONS: [Slot; SLOTS] = [const { Slot(AtomicU64::new(0)) }; SLOTS];

static NEXT_SLOT: AtomicUsize = AtomicUsize::new(0);

/// A thread's allocation counter and the bytes it has not folded yet.
struct Local {
    slot: Cell<usize>,
    unfolded: Cell<isize>,
}

thread_local! {
    // Constant and without a destructor, so reading it never allocates, even as the thread exits.
    static LOCAL: Local = const {
        Local {
            slot: Cell::new(usize::MAX),
            unfolded: Cell::new(0),
        }
    };
}

/// Counts an allocation that moved the live bytes by `bytes`, or with `allocations` zero a free.
#[inline]
fn record(bytes: isize, allocations: u64) {
    LOCAL.with(|local| {
        if allocations != 0 {
            let mut slot = local.slot.get();
            if slot == usize::MAX {
                slot = NEXT_SLOT.fetch_add(1, Relaxed) % SLOTS;
                local.slot.set(slot);
            }
            ALLOCATIONS[slot].0.fetch_add(allocations, Relaxed);
        }
        let unfolded = local.unfolded.get() + bytes;
        if unfolded.unsigned_abs() < BATCH {
            local.unfolded.set(unfolded);
            return;
        }
        local.unfolded.set(0);
        let live = LIVE.fetch_add(unfolded, Relaxed) + unfolded;
        if live > PEAK.load(Relaxed) {
            PEAK.fetch_max(live, Relaxed);
        }
    });
}

/// Every allocation counted so far, by every thread.
fn allocations() -> u64 {
    ALLOCATIONS.iter().map(|slot| slot.0.load(Relaxed)).sum()
}

// SAFETY: every call is forwarded to `A` unchanged; counting only reads the sizes.
unsafe impl<A: GlobalAlloc> GlobalAlloc for Counting<A> {
    #[inline]
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        // SAFETY: the caller's contract, passed on.
        let ptr = unsafe { self.0.alloc(layout) };
        if !ptr.is_null() {
            record(layout.size() as isize, 1);
        }
        ptr
    }

    #[inline]
    unsafe fn alloc_zeroed(&self, layout: Layout) -> *mut u8 {
        // SAFETY: the caller's contract, passed on.
        let ptr = unsafe { self.0.alloc_zeroed(layout) };
        if !ptr.is_null() {
            record(layout.size() as isize, 1);
        }
        ptr
    }

    #[inline]
    unsafe fn dealloc(&self, ptr: *mut u8, layout: Layout) {
        // SAFETY: the caller's contract, passed on.
        unsafe { self.0.dealloc(ptr, layout) };
        record(-(layout.size() as isize), 0);
    }

    #[inline]
    unsafe fn realloc(&self, ptr: *mut u8, layout: Layout, new_size: usize) -> *mut u8 {
        // SAFETY: the caller's contract, passed on.
        let new = unsafe { self.0.realloc(ptr, layout, new_size) };
        if !new.is_null() {
            record(new_size as isize - layout.size() as isize, 1);
        }
        new
    }
}

/// What a window of the program allocated, counted by [`Counting`]; zero where it is not the global allocator.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct Heap {
    /// The most bytes live at once above those live when the window opened, within 64 KiB per thread.
    pub peak: u64,
    /// Allocations and reallocations, exact.
    pub allocations: u64,
}

/// An open window of the program, whose [`Heap`] its [`close`](Self::close) returns.
///
/// Windows nest: one opened inside another closes before it, as a span opened inside another does, and its peak counts towards the outer one's.
#[must_use = "a window measures until it is closed"]
pub struct HeapWindow {
    live: isize,
    outer_peak: isize,
    allocations: u64,
}

impl HeapWindow {
    pub fn open() -> Self {
        let live = LIVE.load(Relaxed);
        Self {
            live,
            outer_peak: PEAK.swap(live, Relaxed),
            allocations: allocations(),
        }
    }

    /// The live bytes when the window opened, as [`LIVE`] counts them.
    pub(crate) const fn opened_at(&self) -> isize {
        self.live
    }

    /// The window's heap, and the most bytes [`LIVE`] counted in it; the enclosing window's peak then takes this one's.
    pub(crate) fn close_at(self) -> (Heap, isize) {
        let peak = PEAK.fetch_max(self.outer_peak, Relaxed);
        let heap = Heap {
            peak: (peak - self.live).max(0) as u64,
            allocations: allocations() - self.allocations,
        };
        (heap, peak)
    }

    pub fn close(self) -> Heap {
        self.close_at().0
    }
}

/// Run `f` in a [`HeapWindow`].
pub fn measure_heap<T>(f: impl FnOnce() -> T) -> (T, Heap) {
    let window = HeapWindow::open();
    let out = f();
    (out, window.close())
}

/// Whether [`Counting`] is the global allocator: it has counted an allocation.
pub(crate) fn counting() -> bool {
    allocations() != 0
}

#[cfg(test)]
mod tests {
    use super::{Counting, Heap, HeapWindow};
    use std::alloc::{GlobalAlloc, Layout, System};

    /// The only counted allocations in the test binary, whose global allocator is not [`Counting`]; each is a fold.
    #[test]
    fn an_inner_window_peak_counts_towards_the_outer_one() {
        let counting = Counting(System);
        let mib = |n: usize| Layout::from_size_align(n << 20, 8).unwrap();
        // SAFETY: each block is freed once, with the layout it was allocated with.
        unsafe {
            let outer = HeapWindow::open();
            let held = counting.alloc(mib(1));
            let inner = HeapWindow::open();
            let freed = counting.alloc(mib(2));
            counting.dealloc(freed, mib(2));
            let grown = counting.realloc(held, mib(1), 3 << 20);
            let inner = inner.close();
            counting.dealloc(grown, mib(3));
            let after = HeapWindow::open();
            let small = counting.alloc(mib(1));
            counting.dealloc(small, mib(1));
            let after = after.close();
            let outer = outer.close();

            let heap = |mib: u64, allocations| Heap {
                peak: mib << 20,
                allocations,
            };
            assert_eq!(inner, heap(2, 2), "above the 1 MiB held when it opened");
            assert_eq!(
                after,
                heap(1, 1),
                "a window after the inner one starts from its own opening"
            );
            assert_eq!(
                outer,
                heap(3, 4),
                "the inner window's peak, and every allocation in or out of it"
            );
        }
    }
}
