//! Minimal fixed-size thread pool for flat data-parallel kernels: "split a range into
//! pieces, run a closure on each." No nested work-stealing, no per-dispatch allocation —
//! owning the runtime lets us attach per-worker scratch buffers and drop rayon.
//!
//! ## Model
//!
//! `NUM_THREADS - 1` background workers (ids `1..NUM_THREADS`); the dispatching thread is
//! worker `0` and runs its share inline (no oversubscription). Tasks are claimed from a
//! shared atomic counter for dynamic load balancing.
//!
//! ## Lock-free dispatch
//!
//! A mutex+condvar wake-up costs ~2x per dispatch. Instead, dispatch bumps a `generation`
//! counter that idle workers **spin** on (back-to-back dispatches pay no syscall), parking
//! only after `SPIN_LIMIT` unrewarded spins. Completion is a lock-free `working` countdown
//! the dispatcher spins on. The per-worker `parked` flag is ordered SeqCst against
//! `generation` so no wake-up is lost and the unpark syscall is skipped while workers spin.
//!
//! ## Nesting falls back to sequential
//!
//! A flat pool can't dispatch from inside a task (would deadlock the dispatch lock), so a
//! `for_each_index` issued from within a pool task runs sequentially inline. The outer
//! level has usually already saturated all cores.
//!
//! ## Constraint
//!
//! One dispatcher at a time: concurrent (non-nested) dispatches are serialized by a mutex.

use std::cell::{Cell, UnsafeCell};
use std::ptr::NonNull;
use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering};
use std::sync::{Mutex, Once, OnceLock};
use std::thread::Thread;

use system_info::NUM_THREADS;

/// Idle spins before a worker parks. Tuned so back-to-back dispatches stay hot but
/// sequential gaps let workers sleep, freeing cores for the active thread.
const SPIN_LIMIT: u32 = 1 << 12;

/// Cap on a single guided-self-scheduling claim (see [`drain`]). Bounds worst-case load
/// imbalance while keeping million-task kernels to a few thousand claims.
const MAX_CLAIM_BATCH: usize = 1 << 12;

/// Total worker count (including the dispatching thread). Equal to build-time `NUM_THREADS`.
#[must_use]
pub const fn num_threads() -> usize {
    NUM_THREADS
}

/// Chunk size for a flat fan-out: a few chunks per worker so the atomic counter can
/// rebalance heterogeneous cores, coarse enough to amortize dispatch.
#[must_use]
#[inline]
pub fn recommended_chunk_size(n_items: usize) -> usize {
    n_items.div_ceil(NUM_THREADS * 4).max(1)
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

/// Type-erased unit of work: a `&(dyn Fn(usize, usize) + Sync)` whose lifetime is erased
/// to `'static`. Only dereferenced inside a dispatch window during which the dispatcher
/// blocks, so the source borrow outlives every call.
struct Job {
    /// Range-based work: `f(start, end)` processes the half-open task range `start..end`.
    /// Building the primitive on ranges (rather than single indices) lets reductions look
    /// up their per-worker accumulator once per claimed batch instead of once per element.
    f: NonNull<dyn Fn(usize, usize) + Sync>,
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

/// Idempotent warm-up: spawn workers and run one dispatch so the pool, parkers, and the
/// mutex's lazily-allocated `pthread_mutex_t` (macOS) exist before timed proving work.
/// Without it the pool initializes lazily on the first parallel call.
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

/// Claim and run task indices until the counter is exhausted, using **guided
/// self-scheduling**: each claim grabs `remaining / (NUM_THREADS * 2)`, capped at
/// [`MAX_CLAIM_BATCH`]. Large early batches keep counter contention low; the proportional
/// shrink keeps the tail finely divided for load balance.
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
        // Stale counter read only affects batch granularity, not correctness: `fetch_add`
        // tiles `0..n` into non-overlapping claims, and out-of-range tails are clamped.
        let observed = pool.counter.load(Ordering::Relaxed);
        if observed >= n {
            break;
        }
        let batch = ((n - observed) / (NUM_THREADS * 2)).clamp(1, MAX_CLAIM_BATCH);
        let start = pool.counter.fetch_add(batch, Ordering::Relaxed);
        if start >= n {
            break;
        }
        let end = (start + batch).min(n);
        f(start, end);
    }
    IN_TASK.set(prev);
}

/// Core dispatch: run `f(start, end)` over disjoint contiguous sub-ranges that together
/// tile `0..n_tasks`, in parallel across the pool. The ranges are produced by guided
/// self-scheduling (see [`drain`]); a worker may receive several. Blocks until all
/// complete; the dispatching thread participates as worker 0.
///
/// This is the primitive everything else is built on. Range-based (rather than per-index)
/// so a reduction can look up its per-worker accumulator once per claimed batch.
pub fn for_each_chunk<F: Fn(usize, usize) + Sync>(n_tasks: usize, f: F) {
    // Trivial sizes, single-core builds, and nested dispatches (called from within a
    // pool task) all run sequentially — the last avoids deadlocking on the lock.
    if NUM_THREADS <= 1 || n_tasks <= 1 || IN_TASK.get() {
        if n_tasks > 0 {
            f(0, n_tasks);
        }
        return;
    }

    let pool = pool();
    let _guard = pool.dispatch.lock().unwrap();
    let n = NUM_THREADS;

    // SAFETY: erase the borrow's lifetime so the closure can live in the `'static`
    // `Job`. The dispatcher blocks on `working` below before returning, so `f`
    // outlives every worker dereference of this pointer.
    let f_ref: &(dyn Fn(usize, usize) + Sync) = &f;
    let f_erased: NonNull<dyn Fn(usize, usize) + Sync> = unsafe { std::mem::transmute(NonNull::from(f_ref)) };

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

/// Run `f(i)` for every `i` in `0..n_tasks`, in parallel across the pool. Blocks until
/// all tasks complete; the dispatching thread participates as worker 0.
pub fn for_each_index<F: Fn(usize) + Sync>(n_tasks: usize, f: F) {
    for_each_chunk(n_tasks, |start, end| {
        for i in start..end {
            f(i);
        }
    });
}

/// A raw base pointer shareable across pool workers. Sound only because callers partition
/// the allocation by task index, so each worker touches a disjoint region. Reuse this for
/// the "share a `*mut` across a dispatch" pattern instead of redefining it per crate.
#[derive(Debug)]
pub struct SendPtr<T>(pub *mut T);
// SAFETY: accesses are partitioned by task index (see callers).
unsafe impl<T> Send for SendPtr<T> {}
unsafe impl<T> Sync for SendPtr<T> {}

impl<T> SendPtr<T> {
    /// Offset the base pointer by `n` elements.
    ///
    /// # Safety
    /// `n` must keep the result within the original allocation, and any write through it
    /// must target a slot no other concurrent task touches.
    #[inline]
    pub unsafe fn add(&self, n: usize) -> *mut T {
        unsafe { self.0.add(n) }
    }

    /// Reconstruct the `len`-long slice starting at element offset `off`.
    ///
    /// # Safety
    /// `off`/`len` must stay in-bounds and the slice must be disjoint from every other
    /// slice any concurrent task reconstructs.
    #[inline]
    pub unsafe fn slice<'a>(&self, off: usize, len: usize) -> &'a mut [T] {
        unsafe { std::slice::from_raw_parts_mut(self.0.add(off), len) }
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

/// Parallel `data.iter_mut().enumerate().for_each(...)`, sized with
/// [`recommended_chunk_size`]. Hands the closure each element's **global** index.
/// `#[inline]` to fold into the per-region caller (recovers the hand-written codegen).
#[inline]
pub fn par_for_each_mut<T: Send, F>(data: &mut [T], f: F)
where
    F: Fn(usize, &mut T) + Sync,
{
    let chunk = recommended_chunk_size(data.len());
    par_chunks_mut(data, chunk, |ci, sub| {
        let base = ci * chunk;
        for (k, slot) in sub.iter_mut().enumerate() {
            f(base + k, slot);
        }
    });
}

/// Give each worker exclusive, persistent access to its own `Option<S>` slot while it
/// drains `0..n_tasks`: `run(slot, start, end)` is called once per claimed batch, always
/// with the same slot for a given worker, so state accumulates across the batches it
/// claims. Returns the per-worker slots (one per worker that ran, rest `None`) for the
/// caller to combine. This is the single home of the cross-worker slot `unsafe`.
fn drain_into_slots<S: Send>(n_tasks: usize, run: impl Fn(&mut Option<S>, usize, usize) + Sync) -> Vec<Option<S>> {
    let mut slots: Vec<Option<S>> = (0..NUM_THREADS).map(|_| None).collect();
    let ptr = SendPtr(slots.as_mut_ptr());
    for_each_chunk(n_tasks, |start, end| {
        // SAFETY: `current_worker_id()` is unique per live worker and < NUM_THREADS, so
        // workers touch disjoint slots; `slots` outlives the dispatch.
        let slot = unsafe { &mut *ptr.add(current_worker_id()) };
        run(slot, start, end);
    });
    slots
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
        return (0..n_tasks).fold(identity(), |acc, i| reduce(acc, map(i)));
    }
    let slots = drain_into_slots(n_tasks, |slot, start, end| {
        // Fold the batch into the worker's accumulator, taking/replacing the shared slot
        // just once so per-element writes stay off the cross-worker pointer.
        let acc = (start..end).fold(slot.take(), |acc, i| {
            Some(match acc {
                Some(a) => reduce(a, map(i)),
                None => map(i),
            })
        });
        *slot = acc;
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
    let slots = drain_into_slots(n_tasks, |slot, start, end| {
        // Scratch and accumulator are created once and threaded through every batch.
        let (state, acc) = slot.get_or_insert_with(|| (init_state(), init_acc()));
        for i in start..end {
            fold(state, acc, i);
        }
    });
    slots
        .into_iter()
        .flatten()
        .map(|(_, acc)| acc)
        .fold(init_acc(), &combine)
}
