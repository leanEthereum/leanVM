//! Fixed-size thread pool for flat data-parallel kernels. Workers claim ranges from one shared counter, which also balances heterogeneous cores. Dispatches cannot nest. Task panics are resumed on the dispatcher after all workers stop.

use std::any::Any;
use std::cell::{Cell, UnsafeCell};
use std::panic::{AssertUnwindSafe, catch_unwind, resume_unwind};
use std::ptr::NonNull;
use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering};
use std::sync::{Mutex, Once, OnceLock};
use std::thread::Thread;

mod topology;

use topology::{Qos, set_qos};
pub use topology::{Topology, num_threads, topology};

/// Idle spins before a worker parks: long enough to stay hot across back-to-back
/// dispatches, short enough to yield the core during a sequential stretch.
///
/// Miri interprets every spin, so there a worker parks at once.
const SPIN_LIMIT: u32 = if cfg!(miri) { 0 } else { 1 << 12 };

/// How finely guided scheduling divides the remaining work.
const CLAIM_DIVISOR: usize = 4;

/// Largest range claimed in one scheduling step.
const MAX_CLAIM_BATCH: usize = 1 << 12;

/// Chunk size for a flat fan-out: many chunks per worker, fine enough for the
/// claim counter to rebalance heterogeneous cores, coarse enough to amortize the
/// dispatch.
///
#[must_use]
#[inline]
pub fn recommended_chunk_size(n_items: usize) -> usize {
    n_items
        .div_ceil(num_threads() * CHUNK_OVERSUBSCRIBE)
        .max(CHUNK_FLOOR)
        .min(n_items.max(1))
}

/// Claims per worker that [`recommended_chunk_size`] aims for, and the smallest
/// chunk it will hand out.
const CHUNK_OVERSUBSCRIBE: usize = 32;
const CHUNK_FLOOR: usize = 64;

thread_local! {
    static WORKER_ID: Cell<usize> = const { Cell::new(0) };
    static IN_TASK: Cell<bool> = const { Cell::new(false) };
}

/// A type-erased work unit. The `&dyn Fn`'s lifetime is erased to `'static`; it
/// is dereferenced only inside a dispatch window during which the dispatcher
/// blocks, so the borrow outlives every call. Range-based (`f(start, end)`) so a
/// reduction looks up its per-worker accumulator once per claim, not per item.
struct Job {
    f: NonNull<dyn Fn(usize, usize) + Sync>,
    n_tasks: usize,
}

/// Park state for one worker (slot 0, the dispatcher, never parks).
struct Worker {
    /// "Currently parked", SeqCst-ordered against [`Pool::generation`].
    parked: AtomicBool,
    /// Handle for `unpark`, published once at worker start-up.
    handle: OnceLock<Thread>,
}

/// One atomic per cache line: `generation`, `counter` and `entered` are hammered
/// by different parties inside the same dispatch window, so packing them together
/// makes every completion decrement invalidate the line every spinner is reading.
/// 128 rather than 64 because x86-64 prefetches the adjacent line of a pair.
#[repr(align(128))]
struct Line(AtomicUsize);

impl std::ops::Deref for Line {
    type Target = AtomicUsize;
    #[inline]
    fn deref(&self) -> &AtomicUsize {
        &self.0
    }
}

struct Pool {
    /// The current job: written by the sole dispatcher before the `generation`
    /// bump, read by workers after observing it (the bump supplies the ordering).
    job: UnsafeCell<Option<Job>>,
    /// Bumped once per dispatch; idle workers watch it (spin, then park).
    generation: Line,
    /// Next item index to claim; reset per dispatch.
    counter: Line,
    /// Background workers inside the current job; the dispatcher spins this to zero.
    entered: Line,
    /// Whether the current job takes no more workers.
    ///
    /// Set once its items are all claimed, so a worker that wakes later never touches it.
    closed: AtomicBool,
    /// Park flag and unpark handle per worker.
    workers: Vec<Worker>,
    /// Serializes dispatchers: one driver at a time.
    dispatch: Mutex<()>,
    /// The dispatch's first task-panic payload, re-raised by the dispatcher.
    /// Caught here so it cannot unwind across `worker_main`, which would skip the
    /// `entered` decrement and hang the completion spin.
    panic: Mutex<Option<Box<dyn Any + Send>>>,
}

// SAFETY: `job` is written only by the sole dispatcher (while the workers are
// parked or before they observe the generation bump) and read only after; the
// generation release/acquire plus the SeqCst park protocol order the two phases.
// The erased `Job` pointer is used only within a dispatch window where the
// borrow it came from is live.
unsafe impl Sync for Pool {}

/// Idempotent warm-up: spawn the workers and run one empty dispatch, so the pool
/// (and, on macOS, its lazily allocated mutex) exists before any timed work.
/// Without this the pool initializes inside whichever kernel dispatches first.
pub fn init() {
    static INIT: Once = Once::new();
    INIT.call_once(|| {
        let _ = pool();
        for_each(num_threads(), |_| {});
    });
}

fn pool() -> &'static Pool {
    static POOL: OnceLock<&'static Pool> = OnceLock::new();
    POOL.get_or_init(|| {
        let topo = topology();
        let n = topo.total().max(1);
        // The dispatcher is worker 0 and runs on a performance core.
        set_qos(Qos::Interactive);
        let pool_ref: &'static Pool = Box::leak(Box::new(Pool {
            job: UnsafeCell::new(None),
            generation: Line(AtomicUsize::new(0)),
            counter: Line(AtomicUsize::new(0)),
            entered: Line(AtomicUsize::new(0)),
            closed: AtomicBool::new(true),
            workers: (0..n)
                .map(|_| Worker {
                    parked: AtomicBool::new(false),
                    handle: OnceLock::new(),
                })
                .collect(),
            dispatch: Mutex::new(()),
            panic: Mutex::new(None),
        }));
        for id in 1..n {
            // Ids past the performance count are the efficiency workers.
            let qos = if id < topo.perf { Qos::Interactive } else { Qos::Utility };
            std::thread::Builder::new()
                .name(format!("parallel-{id}"))
                .spawn(move || worker_main(pool_ref, id, qos))
                .expect("failed to spawn a pool worker");
        }
        pool_ref
    })
}

fn worker_main(pool: &'static Pool, id: usize, qos: Qos) {
    WORKER_ID.set(id);
    set_qos(qos);
    let _ = pool.workers[id].handle.set(std::thread::current());
    let mut last_generation = 0usize;
    loop {
        last_generation = wait_for_dispatch(pool, id, last_generation);
        // Count in, then check the job is still open.
        //
        //     worker:      entered += 1,  then read closed
        //     dispatcher:  closed = true, then read entered
        //
        // Both SeqCst: a worker the dispatcher does not wait for reads the job closed, and skips it.
        pool.entered.fetch_add(1, Ordering::SeqCst);
        if !pool.closed.load(Ordering::SeqCst) {
            drain(pool);
        }
        pool.entered.fetch_sub(1, Ordering::Release);
    }
}

/// Block until a new job is published, returning its generation. Spins up to
/// [`SPIN_LIMIT`], then parks: publish `parked = true`, re-check `generation`,
/// both SeqCst, the same total order the dispatcher's bump and its `parked` load
/// observe, so a wakeup cannot be lost.
fn wait_for_dispatch(pool: &Pool, id: usize, last_generation: usize) -> usize {
    let mut spins = 0u32;
    loop {
        let generation = pool.generation.load(Ordering::Acquire);
        if generation != last_generation {
            return generation;
        }
        if spins < SPIN_LIMIT {
            spins += 1;
            std::hint::spin_loop();
            continue;
        }
        // Announce the intent to park, then re-check: park only if nothing
        // changed, else loop again.
        pool.workers[id].parked.store(true, Ordering::SeqCst);
        if pool.generation.load(Ordering::SeqCst) == last_generation {
            std::thread::park();
        }
        pool.workers[id].parked.store(false, Ordering::SeqCst);
        spins = 0;
    }
}

/// Claim item ranges until the counter is exhausted.
/// Each claim takes half the remaining items per worker, within the batch limits.
/// Large early claims reduce contention.
/// Smaller late claims balance cores of different speeds.
fn drain(pool: &Pool) {
    // SAFETY: the dispatcher published `Some(job)` before opening it, and this worker
    // saw it open after counting itself in. The dispatcher overwrites it only on the
    // next dispatch, after `entered` has fallen to zero, so there is no writer while draining.
    let job = unsafe { (*pool.job.get()).as_ref().expect("drain without a published job") };
    // SAFETY: `job.f` borrows a `&dyn Fn` the blocked dispatcher keeps alive.
    let f = unsafe { job.f.as_ref() };
    let task_count = job.n_tasks;
    let worker_count = num_threads();
    IN_TASK.set(true); // catches nested dispatch; see `for_each_chunk`
    // Catch a task panic so it cannot unwind across `worker_main` (skipping the
    // `entered` decrement and hanging the join) or poison the dispatch lock.
    let result = catch_unwind(AssertUnwindSafe(|| {
        loop {
            // A stale read only affects granularity: `fetch_add` tiles `0..n`
            // into disjoint claims regardless.
            let observed = pool.counter.load(Ordering::Relaxed);
            if observed >= task_count {
                break;
            }
            let batch = ((task_count - observed) / (worker_count * CLAIM_DIVISOR)).clamp(1, MAX_CLAIM_BATCH);
            let start = pool.counter.fetch_add(batch, Ordering::Relaxed);
            if start >= task_count {
                break;
            }
            f(start, (start + batch).min(task_count));
        }
    }));
    IN_TASK.set(false);
    if let Err(payload) = result {
        pool.panic.lock().unwrap().get_or_insert(payload); // keep the first
    }
}

/// Run `f(start, end)` over disjoint ranges tiling `0..n_tasks`, in parallel; one
/// worker may get several (guided self-scheduling). Blocks until every range is done, with
/// the dispatcher acting as worker 0.
///
/// This is the base primitive. It is range-based rather than index-based so a
/// reduction can amortize its per-worker lookups over a whole claim.
///
/// # Panics
/// If called from inside a pool task: that would deadlock on the dispatch lock, so
/// it panics rather than silently serializing. Fan out over the outermost
/// independent unit and keep the levels below it sequential.
pub fn for_each_chunk<F: Fn(usize, usize) + Sync>(n_tasks: usize, f: F) {
    assert!(!IN_TASK.get(), "nested parallel dispatch from inside a pool task");

    let worker_count = num_threads();
    if worker_count <= 1 || n_tasks <= 1 {
        if n_tasks > 0 {
            f(0, n_tasks);
        }
        return;
    }

    let pool = pool();
    let guard = pool.dispatch.lock().unwrap();

    let f_ref: &(dyn Fn(usize, usize) + Sync) = &f;
    // SAFETY: erase the borrow to `'static` so it fits in `Job`. The dispatcher closes the
    // job and waits for `entered` to fall to zero before returning, and a worker entering
    // later reads the job closed, so `f` outlives every dereference.
    // `transmute` rather than a `*const dyn` cast is required: a bare cast would
    // default the trait object's lifetime to `'static` and force `F: 'static`
    // (E0310); the transmute reinterprets the same fat pointer without that bound.
    let f_erased: NonNull<dyn Fn(usize, usize) + Sync> = unsafe { std::mem::transmute(NonNull::from(f_ref)) };

    // SAFETY: sole writer. The prior job is closed and every worker that entered it has left,
    // and a worker entering now reads the job closed until the store below opens it.
    unsafe { *pool.job.get() = Some(Job { f: f_erased, n_tasks }) };
    pool.counter.store(0, Ordering::Relaxed);
    // Open the job: a worker that reads it open also sees the job and the counter above.
    pool.closed.store(false, Ordering::SeqCst);
    pool.generation.fetch_add(1, Ordering::SeqCst); // publish; SeqCst guards the park protocol

    // Wake only the parked workers; the spinning ones see the bump for free.
    for worker in &pool.workers[1..] {
        if worker.parked.load(Ordering::SeqCst)
            && let Some(t) = worker.handle.get()
        {
            t.unpark();
        }
    }

    drain(pool); // the dispatcher runs as worker 0

    // Every item is claimed, so close the job, then wait only for the workers inside it.
    //
    // A worker still spinning or parked is not waited for: it reads the job closed and skips it.
    pool.closed.store(true, Ordering::SeqCst);
    while pool.entered.load(Ordering::SeqCst) != 0 {
        std::hint::spin_loop();
        // Miri runs one thread at a time, so a spin that never yields starves the worker it waits for.
        #[cfg(miri)]
        std::thread::yield_now();
    }

    // Re-raise the first task panic after dropping the guard, so the lock
    // releases cleanly (no poison) and the pool stays usable.
    let panicked = pool.panic.lock().unwrap().take();
    drop(guard);
    if let Some(payload) = panicked {
        resume_unwind(payload);
    }
}

/// `f(i)` for every `i` in `0..n_tasks`, in parallel. `#[inline]` folds the
/// range-to-index adapter into the monomorphized [`for_each_chunk`].
#[inline]
pub fn for_each<F: Fn(usize) + Sync>(n_tasks: usize, f: F) {
    for_each_chunk(n_tasks, |start, end| {
        for i in start..end {
            f(i);
        }
    });
}

/// A base `*mut` that can cross into the task closures. Sound only because
/// callers partition the allocation by item index; every dereference site
/// restates that.
#[derive(Clone, Copy, Debug)]
pub struct SendPtr<T>(pub *mut T);

// SAFETY: `SendPtr` grants no access by itself; every dereference is inside an
// `unsafe` block whose comment establishes that the range being touched belongs
// to exactly one task.
unsafe impl<T> Send for SendPtr<T> {}
// SAFETY: sharing the pointer value is as harmless as sending it, for the reason above.
unsafe impl<T> Sync for SendPtr<T> {}

impl<T> SendPtr<T> {
    /// Offset the base by `n` elements.
    ///
    /// # Safety
    /// `n` stays inside the allocation, and any write targets a slot no
    /// concurrent task touches.
    #[inline]
    pub const unsafe fn add(&self, n: usize) -> *mut T {
        // SAFETY: the caller keeps `n` inside the allocation.
        unsafe { self.0.add(n) }
    }

    /// Rebuild the `len`-element slice at element offset `off`.
    ///
    /// # Safety
    /// `off`/`len` are in bounds and disjoint from every other concurrent task's
    /// slice, and the underlying buffer outlives `'a`.
    #[inline]
    pub const unsafe fn slice<'a>(&self, off: usize, len: usize) -> &'a mut [T] {
        // SAFETY: the caller guarantees `off..off + len` is in bounds, borrowed by no other task, and alive for `'a`.
        unsafe { std::slice::from_raw_parts_mut(self.0.add(off), len) }
    }
}

/// Parallel `data.chunks_mut(chunk).enumerate().for_each(f)`; the final chunk may
/// be shorter.
pub fn chunks_mut<T: Send, F>(data: &mut [T], chunk: usize, f: F)
where
    F: Fn(usize, &mut [T]) + Sync,
{
    let view = Chunks::new(data, chunk);
    for_each(view.count(), |i| {
        // SAFETY: distinct `i` give disjoint in-bounds chunks, and `data` stays
        // borrowed for the whole dispatch.
        f(i, unsafe { view.get(i) });
    });
}

/// Parallel `a.chunks_mut(chunk).zip(b.chunks_mut(chunk))`, for the kernels that
/// fold two tables in lockstep. `a` and `b` must have equal length.
pub fn chunks_mut2<A: Send, B: Send, F>(a: &mut [A], b: &mut [B], chunk: usize, f: F)
where
    F: Fn(usize, &mut [A], &mut [B]) + Sync,
{
    assert_eq!(a.len(), b.len(), "chunks_mut2: slices differ in length");
    let b_ptr = SendPtr(b.as_mut_ptr());
    chunks_mut(a, chunk, |i, sub| {
        let start = i * chunk;
        // SAFETY: `b` has the same length as `a`, so chunk `i` of `b` is the same
        // in-bounds range that chunk `i` of `a` just proved disjoint.
        let sub_b = unsafe { b_ptr.slice(start, sub.len()) };
        f(i, sub, sub_b);
    });
}

/// A `chunks_mut` view that can be handed to tasks: `chunk(i)` is item `i`'s
/// slice. Composes to any number of buffers, which the zip-based helpers do not:
/// a kernel writing four tables at two different widths builds one of these per
/// table and indexes them all by the same item.
#[derive(Clone, Copy, Debug)]
pub struct Chunks<T> {
    base: SendPtr<T>,
    width: usize,
    len: usize,
}

impl<T> Chunks<T> {
    /// View `data` as `len.div_ceil(width)` chunks of `width` (the last shorter).
    #[must_use]
    pub fn new(data: &mut [T], width: usize) -> Self {
        assert!(width > 0, "chunk width must be non-zero");
        Self {
            base: SendPtr(data.as_mut_ptr()),
            width,
            len: data.len(),
        }
    }

    /// Number of chunks.
    #[must_use]
    pub const fn count(&self) -> usize {
        self.len.div_ceil(self.width)
    }

    /// Chunk `i`.
    ///
    /// # Safety
    /// `i < self.count()`, no other live borrow covers chunk `i`, and the
    /// underlying buffer outlives `'a`. Calling this once per `i` inside a
    /// [`for_each`] body satisfies all three.
    #[inline]
    pub unsafe fn get<'a>(&self, i: usize) -> &'a mut [T] {
        let start = i * self.width;
        debug_assert!(start < self.len);
        // SAFETY: `i < count()` puts `start` below `len`, so `start..start + min(width, len - start)` lies in
        // the slice `new` took; the caller guarantees no other borrow of it and that it outlives `'a`.
        unsafe { self.base.slice(start, self.width.min(self.len - start)) }
    }
}

/// Parallel `dst.chunks_mut(chunk).zip(src.chunks(chunk))`, for a kernel that
/// writes one table while reading another of the same length.
pub fn chunks_mut_zip<T: Send, S: Sync, F>(dst: &mut [T], src: &[S], chunk: usize, f: F)
where
    F: Fn(usize, &mut [T], &[S]) + Sync,
{
    assert_eq!(dst.len(), src.len(), "chunks_mut_zip: slices differ in length");
    chunks_mut(dst, chunk, |i, sub| {
        let start = i * chunk;
        f(i, sub, &src[start..start + sub.len()]);
    });
}

/// Parallel `data.iter_mut().enumerate().for_each(f)`, chunked by
/// [`recommended_chunk_size`]. Hands the closure each element's **global** index.
#[inline]
pub fn for_each_mut<T: Send, F>(data: &mut [T], f: F)
where
    F: Fn(usize, &mut T) + Sync,
{
    let chunk = recommended_chunk_size(data.len());
    chunks_mut(data, chunk, |chunk_index, values| {
        for (offset, slot) in values.iter_mut().enumerate() {
            f(chunk_index * chunk + offset, slot);
        }
    });
}

/// Parallel `for (i, slot) in dst.iter_mut().enumerate() { *slot = build(i) }`.
/// The in-place counterpart of [`map_collect`], which allocates.
#[inline]
pub fn fill<T: Send, F: Fn(usize) -> T + Sync>(dst: &mut [T], build: F) {
    for_each_mut(dst, |i, slot| *slot = build(i));
}

/// Parallel `(0..n_tasks).map(f).collect::<Vec<_>>()`: runs `f(i)` across the
/// pool and writes each result straight into the output at its own index: one
/// allocation, no `Option` slots, no per-worker intermediate vectors.
pub fn map_collect<T: Send, F: Fn(usize) -> T + Sync>(n_tasks: usize, f: F) -> Vec<T> {
    let mut out: Vec<T> = Vec::with_capacity(n_tasks);
    let base = SendPtr(out.as_mut_ptr());
    for_each(n_tasks, |i| {
        // SAFETY: distinct `i` write disjoint in-bounds slots, each exactly once,
        // and the dispatch blocks until every write is finished. A panic in `f`
        // leaks the slots written so far, which is acceptable: a task panic is
        // re-raised on the dispatcher and fails the proof.
        unsafe { base.add(i).write(f(i)) };
    });
    // SAFETY: every slot in `0..n_tasks` was initialized exactly once above.
    unsafe { out.set_len(n_tasks) };
    out
}

/// The smallest `i` in `0..n_tasks` with `pred(i)`, or `None`. Deterministic
/// regardless of how the claims fall, because the answer is the global minimum
/// rather than whichever hit landed first.
///
/// Workers publish hits into a shared minimum and skip any claim that starts past
/// it, so the search stops early without giving up determinism.
pub fn find_first<P: Fn(usize) -> bool + Sync>(n_tasks: usize, pred: P) -> Option<usize> {
    let best = AtomicUsize::new(usize::MAX);
    for_each_chunk(n_tasks, |start, end| {
        if start >= best.load(Ordering::Relaxed) {
            return; // a smaller hit already exists
        }
        for i in start..end {
            if pred(i) {
                best.fetch_min(i, Ordering::Relaxed);
                return; // later hits in this claim are larger
            }
        }
    });
    let index = best.load(Ordering::Relaxed);
    (index != usize::MAX).then_some(index)
}

/// One slot per cache line: a worker writes through its accumulator on the
/// per-item path, so a dense array would false-share the boundary lines. 128
/// rather than 64 for the same reason [`Line`] is, and because that is the line
/// itself on Apple silicon.
#[repr(align(128))]
struct Slot<S>(Option<S>);

/// Give each worker its own persistent `Option<S>` while it drains `0..n_tasks`:
/// `run(slot, start, end)` fires once per claim with that worker's slot, so state
/// accumulates across its claims. Returns the slots (the rest `None`) for the
/// caller to combine.
fn drain_into_slots<S: Send>(n_tasks: usize, run: impl Fn(&mut Option<S>, usize, usize) + Sync) -> Vec<Slot<S>> {
    let mut slots: Vec<Slot<S>> = (0..num_threads()).map(|_| Slot(None)).collect();
    let ptr = SendPtr(slots.as_mut_ptr());
    for_each_chunk(n_tasks, |start, end| {
        // SAFETY: `WORKER_ID.get() < num_threads()` is unique per live worker, so
        // the slots are disjoint; `slots` outlives the dispatch.
        let slot = unsafe { &mut (*ptr.add(WORKER_ID.get())).0 };
        run(slot, start, end);
    });
    slots
}

/// Parallel map-reduce over `0..n_tasks`, i.e. `(0..n).map(map).reduce(identity,
/// reduce)`. Each worker folds its claimed indices into one local partial; the
/// partials combine on the dispatcher. `reduce` must be associative with
/// `identity()` a neutral element.
pub fn map_reduce<T, ID, M, R>(n_tasks: usize, identity: ID, map: M, reduce: R) -> T
where
    T: Send,
    ID: Fn() -> T,
    M: Fn(usize) -> T + Sync,
    R: Fn(T, T) -> T + Sync,
{
    let slots = drain_into_slots(n_tasks, |slot, start, end| {
        // Fold the claim into the worker's partial, seeded by the first `map` so
        // `identity` stays off the per-item path; touch the slot once per claim.
        *slot = (start..end).fold(slot.take(), |acc, i| {
            Some(acc.map_or_else(|| map(i), |partial| reduce(partial, map(i))))
        });
    });
    // `identity()` seeds the combine as a left identity, which makes the empty
    // and single-worker cases fall out without a special path.
    slots.into_iter().filter_map(|s| s.0).fold(identity(), &reduce)
}

/// Parallel fold-then-reduce: each worker builds one accumulator with `init`,
/// folds every index it claims into it, and the accumulators `combine` on the
/// dispatcher. `combine` must be associative with `init()` a neutral element.
///
/// This is the shape for a reduction whose accumulator is itself a buffer (a
/// 64-slot bit-fold, say): the buffer is allocated once per worker rather than
/// once per item, and no two workers share a cache line.
pub fn fold_reduce<A, I, F, C>(n_tasks: usize, init: I, fold: F, combine: C) -> A
where
    A: Send,
    I: Fn() -> A + Sync,
    F: Fn(&mut A, usize) + Sync,
    C: Fn(A, A) -> A,
{
    map_reduce_with_state(n_tasks, || (), &init, |_, acc, i| fold(acc, i), combine)
}

/// Parallel reduce where each worker keeps reusable scratch beside its
/// accumulator, so the per-item body need not allocate. `(scratch, acc)` are
/// created once per worker and threaded through its claims; the accumulators
/// combine on the dispatcher. `combine` must be associative with `init_acc()` a
/// neutral element.
pub fn map_reduce_with_state<S, A, IS, IA, F, C>(n_tasks: usize, init_state: IS, init_acc: IA, fold: F, combine: C) -> A
where
    S: Send,
    A: Send,
    IS: Fn() -> S + Sync,
    IA: Fn() -> A + Sync,
    F: Fn(&mut S, &mut A, usize) + Sync,
    C: Fn(A, A) -> A,
{
    let slots = drain_into_slots(n_tasks, |slot, start, end| {
        let (state, acc) = slot.get_or_insert_with(|| (init_state(), init_acc()));
        for i in start..end {
            fold(state, acc, i);
        }
    });
    slots
        .into_iter()
        .filter_map(|s| s.0)
        .map(|(_, acc)| acc)
        .fold(init_acc(), &combine)
}
