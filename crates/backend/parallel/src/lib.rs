//! Minimal fixed-size thread pool for flat, static data-parallel kernels.
//!
//! This is a deliberately tiny alternative to rayon for the one shape the prover
//! actually uses on its hot paths: "split a slice into N pieces, run a closure on
//! each." Unlike rayon it does **no** work-stealing of nested tasks and allocates
//! **nothing** per dispatch — the whole point is to remove the per-task heap
//! traffic that currently forces the `zk-alloc` arena to exist.
//!
//! ## Model
//!
//! The pool owns exactly `NUM_THREADS - 1` background worker threads with stable
//! ids `1..NUM_THREADS`. The dispatching thread acts as worker `0` and runs its
//! share inline, so a dispatch keeps all `NUM_THREADS` hardware threads busy with
//! only `NUM_THREADS - 1` extra threads (no oversubscription, matching the
//! build-time `NUM_THREADS` assumption baked in elsewhere).
//!
//! Tasks are claimed from a shared atomic counter. That gives dynamic load
//! balancing across uneven task costs for free, while still allocating nothing.
//!
//! ## Why stable worker ids
//!
//! [`current_worker_id`] returns a stable `0..NUM_THREADS` id. This is the hook for
//! a future per-worker scratch-buffer strategy: once each worker can index its own
//! preallocated scratch, the short-lived per-task allocations that `zk-alloc`
//! currently absorbs disappear at the source, and the arena can be dropped.
//!
//! ## Constraints
//!
//! - **No nesting.** A worker must not itself dispatch (it would deadlock on the
//!   dispatch lock / barriers). The prover's parallel sections are flat, so this
//!   holds. Nesting is a logic error, not a soundness hole.
//! - **One dispatcher at a time.** Concurrent dispatches are serialized by a mutex.

use std::cell::{Cell, UnsafeCell};
use std::ptr::NonNull;
use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering};
use std::sync::{Barrier, Mutex, Once, OnceLock};

use system_info::NUM_THREADS;

/// Total worker count (including the dispatching thread). Equal to the build-time
/// `NUM_THREADS`.
#[must_use]
pub const fn num_threads() -> usize {
    NUM_THREADS
}

thread_local! {
    /// Stable id of this thread within the pool. Set once per background worker;
    /// stays `0` on the dispatching thread (which acts as worker 0) and on any
    /// thread that never participates.
    static WORKER_ID: Cell<usize> = const { Cell::new(0) };
}

/// Stable id of the calling worker, in `0..NUM_THREADS`. Returns `0` on the
/// dispatching thread and on any non-worker thread.
#[must_use]
pub fn current_worker_id() -> usize {
    WORKER_ID.with(Cell::get)
}

/// A type-erased unit of parallel work. `f` is a `&(dyn Fn(usize) + Sync)` whose
/// lifetime has been erased to `'static`: it is only ever dereferenced between the
/// start and end barriers of a single dispatch, during which the dispatcher blocks,
/// so the borrow it came from outlives every call.
struct Job {
    f: NonNull<dyn Fn(usize) + Sync>,
    n_tasks: usize,
}

struct Pool {
    /// Current job. Written by the dispatcher before `start.wait()` and read by
    /// workers after it; the barrier supplies the happens-before relationship, so
    /// no additional synchronization on this cell is required.
    job: UnsafeCell<Option<Job>>,
    /// Next task index to claim. Reset to 0 before each dispatch.
    counter: AtomicUsize,
    shutdown: AtomicBool,
    /// Workers park here between dispatches; the dispatcher releases them.
    start: Barrier,
    /// Everyone meets here once all tasks are drained.
    end: Barrier,
    /// Serializes dispatchers: only one thread may drive the pool at a time.
    dispatch: Mutex<()>,
}

// SAFETY: `job` is only mutated by the unique dispatcher (serialized by `dispatch`)
// while workers are parked, and only read by workers/dispatcher while no one writes;
// the barriers order these phases. The erased `Job` pointer is never used outside a
// dispatch window during which its source borrow is live.
unsafe impl Sync for Pool {}
unsafe impl Send for Pool {}

/// Construct the pool and exercise its full dispatch path once, now.
///
/// **Must be called before any arena allocator that recycles memory between phases
/// is active** (e.g. before `zk_alloc::begin_phase()`), and is idempotent.
///
/// Two things must end up in the system allocator (not a recyclable arena slab):
/// 1. the leaked `Pool` struct, and
/// 2. the OS sync primitives behind `Mutex`/`Barrier`. On macOS std allocates the
///    underlying `pthread_mutex_t` / `pthread_cond_t` **lazily on first use**, not at
///    construction. So merely building the `Pool` is not enough — if the first
///    `lock()`/`wait()` happened during a phase, that primitive would land in the
///    arena and the next reset would corrupt it (observed as `EINVAL` on lock).
///
/// Running one real dispatch here forces every lazy primitive (the dispatch mutex
/// and both barriers, touched by the dispatcher and every worker) to allocate while
/// the arena is inactive, pinning them in the system allocator for good.
pub fn init() {
    static INIT: Once = Once::new();
    INIT.call_once(|| {
        let _ = pool();
        // `n_tasks > 1` and `NUM_THREADS > 1` are required to take the real dispatch
        // path rather than the sequential fast path. On single-core builds the pool
        // is never used, so there is nothing to warm up.
        if NUM_THREADS > 1 {
            for_each_index(NUM_THREADS, |_| {});
        }
    });
}

fn pool() -> &'static Pool {
    static POOL: OnceLock<&'static Pool> = OnceLock::new();
    POOL.get_or_init(|| {
        let n = NUM_THREADS.max(1);
        let p: &'static Pool = Box::leak(Box::new(Pool {
            job: UnsafeCell::new(None),
            counter: AtomicUsize::new(0),
            shutdown: AtomicBool::new(false),
            start: Barrier::new(n),
            end: Barrier::new(n),
            dispatch: Mutex::new(()),
        }));
        for id in 1..n {
            std::thread::Builder::new()
                .name(format!("parallel-worker-{id}"))
                .spawn(move || worker_main(p, id))
                .expect("failed to spawn pool worker");
        }
        p
    })
}

fn worker_main(pool: &'static Pool, id: usize) {
    WORKER_ID.with(|c| c.set(id));
    loop {
        pool.start.wait();
        if pool.shutdown.load(Ordering::Acquire) {
            break;
        }
        drain(pool);
        pool.end.wait();
    }
}

/// Claim and run task indices until the counter is exhausted.
fn drain(pool: &Pool) {
    // SAFETY: the dispatcher published `Some(job)` before the start barrier we just
    // crossed, and clears it only after the end barrier; nobody writes during drain.
    let job = unsafe { (*pool.job.get()).as_ref().expect("drain without a published job") };
    // SAFETY: `job.f` points at a `&dyn Fn` borrow held live by the blocked
    // dispatcher for the entire dispatch window.
    let f = unsafe { job.f.as_ref() };
    let n = job.n_tasks;
    loop {
        let i = pool.counter.fetch_add(1, Ordering::Relaxed);
        if i >= n {
            break;
        }
        f(i);
    }
}

/// Run `f(i)` for every `i` in `0..n_tasks`, in parallel across the pool. Blocks
/// until all tasks complete. The dispatching thread participates as worker 0.
///
/// Falls back to a sequential loop for trivial sizes or single-core builds, so no
/// workers are woken for work that isn't worth the handshake.
pub fn for_each_index<F: Fn(usize) + Sync>(n_tasks: usize, f: F) {
    if NUM_THREADS <= 1 || n_tasks <= 1 {
        for i in 0..n_tasks {
            f(i);
        }
        return;
    }

    let pool = pool();
    let _guard = pool.dispatch.lock().unwrap();

    let f_ref: &(dyn Fn(usize) + Sync) = &f;
    // SAFETY: erase the borrow's lifetime to store it in the 'static `Job`. The
    // dispatcher blocks on `end.wait()` below before returning, so `f` (and thus
    // `f_ref`) outlives every worker call that dereferences this pointer.
    let f_erased: NonNull<dyn Fn(usize) + Sync> = unsafe {
        std::mem::transmute::<NonNull<dyn Fn(usize) + Sync>, NonNull<dyn Fn(usize) + Sync>>(NonNull::from(f_ref))
    };

    // SAFETY: workers are parked on `start`; we hold `dispatch`, so we are the sole
    // writer of `job` and `counter` here.
    unsafe { *pool.job.get() = Some(Job { f: f_erased, n_tasks }) };
    pool.counter.store(0, Ordering::Relaxed);

    pool.start.wait(); // release workers (publishes job)
    drain(pool); // dispatcher runs as worker 0
    pool.end.wait(); // wait for all workers

    // SAFETY: all workers have passed `end`; none will touch `job` until the next
    // dispatch republishes it.
    unsafe { *pool.job.get() = None };
}

/// Wrapper holding a raw base pointer that is safe to share across workers because
/// each worker only ever touches a disjoint sub-slice computed from its task index.
struct SendPtr<T>(*mut T);
// SAFETY: see `par_chunks_mut` — accesses are partitioned by task index.
unsafe impl<T> Send for SendPtr<T> {}
unsafe impl<T> Sync for SendPtr<T> {}

impl<T> SendPtr<T> {
    /// SAFETY: `n` must keep the result within the original allocation.
    unsafe fn add(&self, n: usize) -> *mut T {
        unsafe { self.0.add(n) }
    }
}

/// Parallel equivalent of `data.chunks_mut(chunk).enumerate().for_each(...)`.
///
/// Splits `data` into `ceil(len / chunk)` consecutive chunks and runs
/// `f(chunk_index, chunk)` on each in parallel. The final chunk may be shorter.
/// Mirrors rayon's `par_chunks_mut().enumerate()` for the prover's kernels.
pub fn par_chunks_mut<T: Send, F>(data: &mut [T], chunk: usize, f: F)
where
    F: Fn(usize, &mut [T]) + Sync,
{
    assert!(chunk > 0, "chunk size must be non-zero");
    let len = data.len();
    let n_chunks = len.div_ceil(chunk);
    let base = SendPtr(data.as_mut_ptr());

    for_each_index(n_chunks, |i| {
        let start = i * chunk;
        let this_len = chunk.min(len - start);
        // SAFETY: distinct `i` produce non-overlapping `[start, start+this_len)`
        // ranges within `data`, and the dispatcher keeps `data` borrowed for the
        // whole call. `SendPtr` only re-exposes a pointer into that live borrow.
        let slice = unsafe { std::slice::from_raw_parts_mut(base.add(start), this_len) };
        f(i, slice);
    });
}

/// Parallel map-reduce over `0..n_tasks`, equivalent to
/// `(0..n_tasks).into_par_iter().map(map).reduce(identity, reduce)`.
///
/// Each worker folds the task indices it claims into a single local accumulator, so
/// only one accumulator is allocated per worker (not one per task). The per-worker
/// partials are then combined on the dispatching thread. `reduce` must be
/// associative; the combination order is otherwise unspecified.
pub fn map_reduce<T, ID, M, R>(n_tasks: usize, identity: ID, map: M, reduce: R) -> T
where
    T: Send,
    ID: Fn() -> T,
    M: Fn(usize) -> T + Sync,
    R: Fn(T, T) -> T + Sync,
{
    if NUM_THREADS <= 1 || n_tasks <= 1 {
        let mut acc = identity();
        for i in 0..n_tasks {
            acc = reduce(acc, map(i));
        }
        return acc;
    }

    // One slot per worker id (0 == dispatcher). Each worker touches only its own slot.
    let mut partials: Vec<Option<T>> = (0..NUM_THREADS).map(|_| None).collect();
    let slots = SendPtr(partials.as_mut_ptr());

    for_each_index(n_tasks, |i| {
        let wid = current_worker_id();
        // SAFETY: `wid` is unique per live worker and < NUM_THREADS, so slots are
        // disjoint; `partials` outlives the dispatch (dispatcher blocks until done).
        let slot = unsafe { &mut *slots.add(wid) };
        let v = map(i);
        *slot = Some(match slot.take() {
            Some(acc) => reduce(acc, v),
            None => v,
        });
    });

    partials.into_iter().flatten().fold(identity(), &reduce)
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::sync::atomic::AtomicU64;

    #[test]
    fn for_each_index_runs_all() {
        let n = 10_000;
        let sum = AtomicU64::new(0);
        for_each_index(n, |i| {
            sum.fetch_add(i as u64, Ordering::Relaxed);
        });
        assert_eq!(sum.load(Ordering::Relaxed), (0..n as u64).sum());
    }

    #[test]
    fn par_chunks_mut_writes_disjoint() {
        let mut data = vec![0usize; 100_000];
        par_chunks_mut(&mut data, 64, |i, chunk| {
            for (j, x) in chunk.iter_mut().enumerate() {
                *x = i * 64 + j;
            }
        });
        for (idx, &v) in data.iter().enumerate() {
            assert_eq!(v, idx);
        }
    }

    #[test]
    fn map_reduce_matches_sequential() {
        for n in [0usize, 1, 2, 1000, 100_000] {
            let got = map_reduce(n, || 0u64, |i| i as u64, |a, b| a + b);
            assert_eq!(got, (0..n as u64).sum::<u64>(), "scalar sum n={n}");
        }
        // Vec accumulator (mirrors sumcheck's parallel_sum shape).
        let n = 5000;
        let got = map_reduce(
            n,
            || vec![0u64; 3],
            |i| vec![i as u64, (i * 2) as u64, (i * 3) as u64],
            |mut a, b| {
                for (x, y) in a.iter_mut().zip(b) {
                    *x += y;
                }
                a
            },
        );
        let s: u64 = (0..n as u64).sum();
        assert_eq!(got, vec![s, 2 * s, 3 * s]);
    }

    #[test]
    fn repeated_dispatch_is_stable() {
        for _ in 0..50 {
            let mut data = vec![0u32; 8192];
            par_chunks_mut(&mut data, 16, |_, chunk| {
                for x in chunk.iter_mut() {
                    *x += 1;
                }
            });
            assert!(data.iter().all(|&x| x == 1));
        }
    }
}
