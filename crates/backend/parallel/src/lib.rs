//! Minimal fixed-size thread pool for flat, static data-parallel kernels.
//!
//! A deliberately tiny alternative to rayon for the one shape the prover uses on its
//! hot paths: "split a range/slice into pieces, run a closure on each." Unlike rayon
//! it does **no** work-stealing of nested tasks and allocates **nothing** per
//! dispatch — the whole point is to own the runtime so we can (a) attach per-worker
//! scratch buffers (eliminating the per-task allocations that justify the `zk-alloc`
//! arena), and (b) drop rayon entirely along with its `flush_rayon` injector hack.
//!
//! ## Model
//!
//! The pool owns exactly `NUM_THREADS - 1` background workers with stable ids
//! `1..NUM_THREADS`; the dispatching thread acts as worker `0` and runs its share
//! inline (so a dispatch keeps all `NUM_THREADS` hardware threads busy with only
//! `NUM_THREADS - 1` extra threads — no oversubscription). Tasks are claimed from a
//! shared atomic counter, giving dynamic load balancing for free.
//!
//! ## Dispatch is lock-free on the hot path
//!
//! A `std::Barrier` (mutex + condvar) wake-up costs ~2x rayon per dispatch, which the
//! prover's many dispatches turn into a real regression. Instead, dispatch bumps a
//! `generation` counter that idle workers watch by **spinning** (so back-to-back
//! dispatches never pay a syscall), parking only after `SPIN_LIMIT` unrewarded spins.
//! Completion is a lock-free atomic countdown (`working`) the dispatcher spins on.
//! Park/unpark uses a per-worker `parked` flag with SeqCst ordering against
//! `generation` to avoid lost wake-ups, so the unpark syscall is skipped while
//! workers are hot. Measured ~7.5µs/dispatch vs rayon's ~37µs.
//!
//! ## Coexistence caveat
//!
//! Running this pool *alongside* rayon (a partial migration) regresses the prover
//! ~30% — work bounces between two disjoint thread sets, thrashing caches and
//! oversubscribing at region boundaries. This pool only pays off once rayon is gone
//! everywhere. Treat partial-migration benchmarks accordingly.
//!
//! ## Nesting falls back to sequential
//!
//! Some kernels nest parallelism (e.g. the NTT fans out over blocks, then over rows
//! within a block). A flat pool can't dispatch from inside a task — that would
//! deadlock on the dispatch lock. So a `for_each_index` call made from a thread
//! already running a pool task runs **sequentially inline** instead. Correct, never
//! deadlocks; the inner level loses parallelism but the outer level has usually
//! already saturated all cores. (rayon work-steals through nesting instead; this is
//! the one place we trade a little potential utilization for a vastly simpler pool.)
//!
//! ## Constraint
//!
//! - **One dispatcher at a time.** Concurrent (non-nested) dispatches from different
//!   threads are serialized by a mutex.

use std::cell::{Cell, UnsafeCell};
use std::ptr::NonNull;
use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering};
use std::sync::{Mutex, Once, OnceLock};
use std::thread::Thread;

use system_info::NUM_THREADS;

/// Spins an idle worker performs before parking. Tuned so back-to-back dispatches
/// keep workers hot (no syscalls) while a long idle stretch still lets them sleep.
const SPIN_LIMIT: u32 = 1 << 16;

/// Total worker count (including the dispatching thread). Equal to build-time `NUM_THREADS`.
#[must_use]
pub const fn num_threads() -> usize {
    NUM_THREADS
}

thread_local! {
    /// Stable id of this thread within the pool. Set once per background worker;
    /// stays `0` on the dispatching thread (worker 0) and on any non-worker thread.
    static WORKER_ID: Cell<usize> = const { Cell::new(0) };
    /// True while this thread is executing a pool task. A `for_each_index` issued in
    /// that state is a nested dispatch and runs sequentially (see module docs).
    static IN_TASK: Cell<bool> = const { Cell::new(false) };
}

/// Stable id of the calling worker, in `0..NUM_THREADS` (`0` off-pool). The hook for
/// per-worker scratch buffers.
#[must_use]
pub fn current_worker_id() -> usize {
    WORKER_ID.with(Cell::get)
}

/// Type-erased unit of work: a `&(dyn Fn(usize) + Sync)` whose lifetime is erased to
/// `'static`. Only dereferenced inside a dispatch window during which the dispatcher
/// blocks, so the source borrow outlives every call.
struct Job {
    f: NonNull<dyn Fn(usize) + Sync>,
    n_tasks: usize,
}

struct Pool {
    /// Current job. Written by the dispatcher before bumping `generation`, read by
    /// workers after they observe the bump; `generation` supplies the happens-before.
    job: UnsafeCell<Option<Job>>,
    /// Bumped once per dispatch. Idle workers watch it (spin, then park).
    generation: AtomicUsize,
    /// Next task index to claim. Reset to 0 before each dispatch.
    counter: AtomicUsize,
    /// Background workers still draining the current dispatch; dispatcher spins to 0.
    working: AtomicUsize,
    shutdown: AtomicBool,
    /// Per-worker "currently parked" flags (indexed by worker id; slot 0 unused).
    parked: Vec<AtomicBool>,
    /// Per-worker thread handles for `unpark` (indexed by worker id; slot 0 unused).
    handles: Vec<OnceLock<Thread>>,
    /// Serializes dispatchers: only one thread may drive the pool at a time.
    dispatch: Mutex<()>,
}

// SAFETY: `job` is mutated only by the unique dispatcher while workers are parked or
// before they observe the generation bump, and read only after; the `generation`
// release/acquire (and SeqCst park protocol) order these phases. The erased `Job`
// pointer is never used outside a dispatch window during which its borrow is live.
unsafe impl Sync for Pool {}
unsafe impl Send for Pool {}

/// Construct the pool and exercise its dispatch path once, now.
///
/// **Must be called before any arena allocator that recycles memory between phases is
/// active** (e.g. before `zk_alloc::begin_phase()`); idempotent. The leaked `Pool`
/// and the `dispatch` mutex's lazily-allocated `pthread_mutex_t` (macOS allocates it
/// on first lock, not construction) must live in the system allocator, not a slab the
/// next reset recycles. Running one real dispatch forces those allocations while the
/// arena is inactive. (Worker `Parker`s are allocated eagerly at spawn, also here.)
pub fn init() {
    static INIT: Once = Once::new();
    INIT.call_once(|| {
        let _ = pool();
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
            generation: AtomicUsize::new(0),
            counter: AtomicUsize::new(0),
            working: AtomicUsize::new(0),
            shutdown: AtomicBool::new(false),
            parked: (0..n).map(|_| AtomicBool::new(false)).collect(),
            handles: (0..n).map(|_| OnceLock::new()).collect(),
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
    let _ = pool.handles[id].set(std::thread::current());

    let mut last_gen = 0usize;
    loop {
        let mut spins = 0u32;
        let g = loop {
            let g = pool.generation.load(Ordering::Acquire);
            if g != last_gen {
                break g;
            }
            if pool.shutdown.load(Ordering::Acquire) {
                return;
            }
            if spins < SPIN_LIMIT {
                spins += 1;
                std::hint::spin_loop();
            } else {
                // About to park. Publish it, then re-check `generation`: by SeqCst
                // total order with the dispatcher's `generation` bump and `parked`
                // load, at least one side sees the other, so no wake-up is lost.
                pool.parked[id].store(true, Ordering::SeqCst);
                if pool.generation.load(Ordering::SeqCst) != last_gen {
                    pool.parked[id].store(false, Ordering::SeqCst);
                } else if pool.shutdown.load(Ordering::SeqCst) {
                    pool.parked[id].store(false, Ordering::SeqCst);
                    return;
                } else {
                    std::thread::park();
                    pool.parked[id].store(false, Ordering::SeqCst);
                }
                spins = 0;
            }
        };
        last_gen = g;
        drain(pool);
        pool.working.fetch_sub(1, Ordering::Release);
    }
}

/// Claim and run task indices until the counter is exhausted.
fn drain(pool: &Pool) {
    // SAFETY: the dispatcher published `Some(job)` before the generation bump this
    // worker just observed, and overwrites it only on the next dispatch (gated on
    // `working == 0`); nobody writes during drain.
    let job = unsafe { (*pool.job.get()).as_ref().expect("drain without a published job") };
    // SAFETY: `job.f` points at a `&dyn Fn` borrow held live by the blocked dispatcher.
    let f = unsafe { job.f.as_ref() };
    let n = job.n_tasks;
    // Mark this thread as in-task so a nested `for_each_index` runs sequentially
    // rather than deadlocking on the dispatch lock.
    let prev = IN_TASK.replace(true);
    loop {
        let i = pool.counter.fetch_add(1, Ordering::Relaxed);
        if i >= n {
            break;
        }
        f(i);
    }
    IN_TASK.set(prev);
}

/// Run `f(i)` for every `i` in `0..n_tasks`, in parallel across the pool. Blocks until
/// all tasks complete; the dispatching thread participates as worker 0.
pub fn for_each_index<F: Fn(usize) + Sync>(n_tasks: usize, f: F) {
    // Trivial sizes, single-core builds, and nested dispatches (called from within a
    // pool task) all run sequentially — the last avoids deadlocking on the lock.
    if NUM_THREADS <= 1 || n_tasks <= 1 || IN_TASK.get() {
        for i in 0..n_tasks {
            f(i);
        }
        return;
    }

    let pool = pool();
    let _guard = pool.dispatch.lock().unwrap();
    let n = NUM_THREADS;

    let f_ref: &(dyn Fn(usize) + Sync) = &f;
    // SAFETY: erase the borrow's lifetime to store in the 'static `Job`. The
    // dispatcher spins on `working` below before returning, so `f` outlives every
    // worker call that dereferences this pointer.
    let f_erased: NonNull<dyn Fn(usize) + Sync> = unsafe {
        std::mem::transmute::<NonNull<dyn Fn(usize) + Sync>, NonNull<dyn Fn(usize) + Sync>>(NonNull::from(f_ref))
    };

    // SAFETY: all workers finished the previous dispatch (we waited for `working == 0`)
    // and none observes this one until the generation bump, so we are the sole writer.
    unsafe { *pool.job.get() = Some(Job { f: f_erased, n_tasks }) };
    pool.counter.store(0, Ordering::Relaxed);
    pool.working.store(n - 1, Ordering::Release);

    // Publish the dispatch. SeqCst so the parked-flag protocol can't lose a wake-up.
    pool.generation.fetch_add(1, Ordering::SeqCst);

    // Wake only workers that actually parked; hot (spinning) ones see the bump for free.
    for id in 1..n {
        if pool.parked[id].load(Ordering::SeqCst)
            && let Some(t) = pool.handles[id].get()
        {
            t.unpark();
        }
    }

    drain(pool); // dispatcher runs as worker 0

    // Lock-free completion: wait for every background worker to finish draining.
    while pool.working.load(Ordering::Acquire) != 0 {
        std::hint::spin_loop();
    }
}

/// Wrapper holding a raw base pointer that is safe to share across workers because
/// each worker only touches a disjoint sub-slice computed from its task index.
struct SendPtr<T>(*mut T);
// SAFETY: accesses are partitioned by task index (see callers).
unsafe impl<T> Send for SendPtr<T> {}
unsafe impl<T> Sync for SendPtr<T> {}

impl<T> SendPtr<T> {
    /// SAFETY: `n` must keep the result within the original allocation.
    unsafe fn add(&self, n: usize) -> *mut T {
        unsafe { self.0.add(n) }
    }
}

/// Parallel equivalent of `data.chunks_mut(chunk).enumerate().for_each(...)`, running
/// `f(chunk_index, chunk)` on each in parallel. The final chunk may be shorter.
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
        // SAFETY: distinct `i` produce non-overlapping in-bounds ranges, and `data`
        // stays borrowed for the whole call.
        let slice = unsafe { std::slice::from_raw_parts_mut(base.add(start), this_len) };
        f(i, slice);
    });
}

/// Parallel map-reduce over `0..n_tasks`, equivalent to
/// `(0..n_tasks).into_par_iter().map(map).reduce(identity, reduce)`.
///
/// Each worker folds the task indices it claims into one local accumulator (one per
/// worker, not per task); the per-worker partials are combined on the dispatcher.
/// `reduce` must be associative.
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

    let mut slots: Vec<Option<T>> = (0..NUM_THREADS).map(|_| None).collect();
    let ptr = SendPtr(slots.as_mut_ptr());

    for_each_index(n_tasks, |i| {
        let wid = current_worker_id();
        // SAFETY: `wid` is unique per live worker and < NUM_THREADS; slots disjoint;
        // `slots` outlives the dispatch.
        let slot = unsafe { &mut *ptr.add(wid) };
        let v = map(i);
        *slot = Some(match slot.take() {
            Some(acc) => reduce(acc, v),
            None => v,
        });
    });

    slots.into_iter().flatten().fold(identity(), &reduce)
}

/// Parallel reduce where each worker keeps reusable **scratch** alongside its
/// accumulator, so the per-task body can avoid allocating. Each worker creates
/// `(scratch, acc)` once on its first task and reuses the scratch across all the
/// tasks it claims; the per-worker `acc`s are then combined. `combine` must be
/// associative.
pub fn map_reduce_with_state<S, A, IS, IA, F, C>(n_tasks: usize, init_state: IS, init_acc: IA, fold: F, combine: C) -> A
where
    S: Send,
    A: Send,
    IS: Fn() -> S + Sync,
    IA: Fn() -> A + Sync,
    F: Fn(&mut S, &mut A, usize) + Sync,
    C: Fn(A, A) -> A,
{
    if NUM_THREADS <= 1 || n_tasks <= 1 {
        let mut state = init_state();
        let mut acc = init_acc();
        for i in 0..n_tasks {
            fold(&mut state, &mut acc, i);
        }
        return acc;
    }

    let mut slots: Vec<Option<(S, A)>> = (0..NUM_THREADS).map(|_| None).collect();
    let ptr = SendPtr(slots.as_mut_ptr());

    for_each_index(n_tasks, |i| {
        let wid = current_worker_id();
        // SAFETY: `wid` unique per live worker and < NUM_THREADS; slots disjoint;
        // `slots` outlives the dispatch.
        let slot = unsafe { &mut *ptr.add(wid) };
        let (state, acc) = slot.get_or_insert_with(|| (init_state(), init_acc()));
        fold(state, acc, i);
    });

    slots
        .into_iter()
        .flatten()
        .map(|(_, acc)| acc)
        .fold(init_acc(), &combine)
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
    fn map_reduce_with_state_matches_sequential() {
        for n in [0usize, 1, 3, 1000, 50_000] {
            let got = map_reduce_with_state(
                n,
                Vec::<u64>::new,
                || vec![0u64; 2],
                |scratch: &mut Vec<u64>, acc: &mut Vec<u64>, i| {
                    scratch.clear();
                    scratch.push(i as u64);
                    scratch.push((i * i) as u64);
                    acc[0] += scratch[0];
                    acc[1] += scratch[1];
                },
                |mut a: Vec<u64>, b: Vec<u64>| {
                    for (x, y) in a.iter_mut().zip(b) {
                        *x += y;
                    }
                    a
                },
            );
            let s0: u64 = (0..n as u64).sum();
            let s1: u64 = (0..n as u64).map(|i| i * i).sum();
            assert_eq!(got, vec![s0, s1], "n={n}");
        }
    }

    #[test]
    fn nested_dispatch_does_not_deadlock() {
        // Outer parallel loop whose body itself dispatches — must run (inner goes
        // sequential) and produce correct results, not hang.
        let mut data = vec![0u64; 1000];
        par_chunks_mut(&mut data, 50, |outer, chunk| {
            // Nested dispatch from inside a pool task.
            let sum = AtomicU64::new(0);
            for_each_index(chunk.len(), |i| {
                sum.fetch_add((outer * 50 + i) as u64, Ordering::Relaxed);
            });
            chunk[0] = sum.load(Ordering::Relaxed);
        });
        for (c, chunk) in data.chunks(50).enumerate() {
            let expected: u64 = (0..50).map(|i| (c * 50 + i) as u64).sum();
            assert_eq!(chunk[0], expected, "chunk {c}");
        }
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
