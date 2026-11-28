//! Fixed-size thread pool for flat data-parallel kernels.
//! Workers claim ranges from one shared counter, which also balances cores of different speeds.
//! Dispatches cannot nest: a dispatch from a pool task panics, and one from a thread a task spawned can deadlock.
//! Task panics are resumed on the dispatcher after every worker has stopped.

use std::any::Any;
use std::cell::Cell;
use std::panic::{AssertUnwindSafe, catch_unwind, resume_unwind};
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::{Condvar, Mutex, Once, OnceLock};

static NUM_THREADS: OnceLock<usize> = OnceLock::new();

/// Worker count including the dispatcher: [`set_num_threads`]'s, else one per physical core (the logical CPUs, halved
/// where Linux says SMT is active: a second hardware thread per core slows a proof).
///
/// Out of line, as [`for_each_chunk`]'s dispatch is: the pool's machinery stays in functions of its own.
#[must_use]
#[inline(never)]
pub fn num_threads() -> usize {
    *NUM_THREADS.get_or_init(|| {
        let logical = std::thread::available_parallelism().map_or(1, |n| n.get());
        let smt = std::fs::read_to_string("/sys/devices/system/cpu/smt/active").is_ok_and(|s| s.trim() == "1");
        if smt { (logical / 2).max(1) } else { logical }
    })
}

/// Fixes [`num_threads`] before the pool starts; `0` keeps the default. Panics if it is already another.
pub fn set_num_threads(n: usize) {
    if n == 0 {
        return;
    }
    let set = *NUM_THREADS.get_or_init(|| n);
    assert_eq!(set, n, "the thread pool already runs with {set} threads");
}

/// How finely guided scheduling divides the remaining work.
const CLAIM_DIVISOR: usize = 4;

/// Largest range claimed in one scheduling step.
const MAX_CLAIM_BATCH: usize = 1 << 12;

thread_local! {
    static IN_TASK: Cell<bool> = const { Cell::new(false) };
}

/// A closure `f(start, end)` erased to a pointer to it and the one function that calls it. Unlike a `dyn Fn`, it
/// makes no vtable, which would hold a second copy of the closure's body, for a call by value.
#[derive(Clone, Copy)]
struct Task {
    data: *const (),
    call: unsafe fn(*const (), usize, usize),
}

impl Task {
    fn new<F: Fn(usize, usize) + Sync>(f: &F) -> Self {
        /// # Safety
        /// `data` points to a live `F`.
        unsafe fn call<F: Fn(usize, usize)>(data: *const (), start: usize, end: usize) {
            // SAFETY: the caller's contract.
            unsafe { (*data.cast::<F>())(start, end) }
        }
        Self {
            data: (f as *const F).cast(),
            call: call::<F>,
        }
    }

    /// # Safety
    /// The closure it was made from is still alive.
    unsafe fn run(self, start: usize, end: usize) {
        // SAFETY: the caller's contract.
        unsafe { (self.call)(self.data, start, end) }
    }
}

/// A work unit: its task over ranges tiling `0..n_tasks`. The dispatcher waits for every worker to finish the job
/// before it returns, so the closure outlives every call.
#[derive(Clone, Copy)]
struct Job {
    task: Task,
    n_tasks: usize,
}

// SAFETY: the closure behind the task is `Sync`, and it outlives every worker's use of it (see `Job`).
unsafe impl Send for Job {}

/// What the workers wait on: the current job, numbered by its generation, and how many workers sleep on `start`.
struct State {
    generation: usize,
    job: Option<Job>,
    sleeping: usize,
}

/// Idle spins before a worker or the dispatcher sleeps: back-to-back dispatches, the common case, then cost no
/// wake-up through the kernel, which on many cores is where the time goes.
const SPIN_LIMIT: u32 = 1 << 12;

struct Pool {
    state: Mutex<State>,
    /// Signalled when a new job is published.
    start: Condvar,
    /// Signalled when the last worker finishes the job.
    done: Condvar,
    /// `State::generation`, readable without the lock, for the spinning workers.
    published: AtomicUsize,
    /// Workers still running the current job.
    running: AtomicUsize,
    /// Next item index to claim; reset per dispatch.
    counter: AtomicUsize,
    /// Serializes dispatchers: one driver at a time.
    dispatch: Mutex<()>,
    /// The dispatch's first task-panic payload, re-raised by the dispatcher.
    panic: Mutex<Option<Box<dyn Any + Send>>>,
}

/// Idempotent warm-up: spawn the workers and run one empty dispatch, which waits for every worker,
/// so the pool exists before any timed work.
pub fn init() {
    static INIT: Once = Once::new();
    INIT.call_once(|| for_each(num_threads(), |_| {}));
}

fn pool() -> &'static Pool {
    static POOL: OnceLock<&'static Pool> = OnceLock::new();
    POOL.get_or_init(|| {
        let pool: &'static Pool = Box::leak(Box::new(Pool {
            state: Mutex::new(State {
                generation: 0,
                job: None,
                sleeping: 0,
            }),
            start: Condvar::new(),
            done: Condvar::new(),
            published: AtomicUsize::new(0),
            running: AtomicUsize::new(0),
            counter: AtomicUsize::new(0),
            dispatch: Mutex::new(()),
            panic: Mutex::new(None),
        }));
        // The dispatcher is worker 0.
        for id in 1..num_threads() {
            std::thread::Builder::new()
                .name(format!("parallel-{id}"))
                .spawn(move || worker_main(pool))
                .expect("failed to spawn a pool worker");
        }
        pool
    })
}

fn worker_main(pool: &'static Pool) {
    IN_TASK.set(true); // a worker only ever runs tasks
    let mut seen = 0;
    loop {
        spin_while(|| pool.published.load(Ordering::Acquire) == seen);
        let job = {
            let mut state = pool.state.lock().unwrap();
            while state.generation == seen {
                state.sleeping += 1;
                state = pool.start.wait(state).unwrap();
                state.sleeping -= 1;
            }
            seen = state.generation;
            state.job.expect("a published job")
        };
        drain(pool, job);
        if pool.running.fetch_sub(1, Ordering::AcqRel) == 1 {
            // The dispatcher checks `running` under the lock before it sleeps, so this wake-up is never lost.
            let _state = pool.state.lock().unwrap();
            pool.done.notify_one();
        }
    }
}

/// Spin while `busy` holds, at most [`SPIN_LIMIT`] times.
fn spin_while(busy: impl Fn() -> bool) {
    for _ in 0..SPIN_LIMIT {
        if !busy() {
            return;
        }
        std::hint::spin_loop();
    }
}

/// Claim and run item ranges until the counter is exhausted. Each claim takes
/// `remaining / (CLAIM_DIVISOR · workers)`, clamped to `1..=`[`MAX_CLAIM_BATCH`]: big early
/// claims cut counter contention, and the proportional shrink keeps the tail
/// balanced across cores of different speeds.
fn drain(pool: &Pool, job: Job) {
    let n = job.n_tasks;
    // Catch a task panic so it cannot unwind out of a worker, which would leave the dispatcher waiting.
    let result = catch_unwind(AssertUnwindSafe(|| {
        loop {
            let observed = pool.counter.load(Ordering::Relaxed);
            if observed >= n {
                break;
            }
            let batch = ((n - observed) / (num_threads() * CLAIM_DIVISOR)).clamp(1, MAX_CLAIM_BATCH);
            let start = pool.counter.fetch_add(batch, Ordering::Relaxed);
            if start >= n {
                break;
            }
            // SAFETY: the dispatcher keeps the closure alive until every worker has finished the job.
            unsafe { job.task.run(start, (start + batch).min(n)) };
        }
    }));
    if let Err(payload) = result {
        pool.panic.lock().unwrap().get_or_insert(payload); // keep the first
    }
}

/// Marks the calling thread as inside a dispatch until dropped, unwinding included.
struct InTask;

impl InTask {
    fn enter() -> Self {
        IN_TASK.set(true);
        Self
    }
}

impl Drop for InTask {
    fn drop(&mut self) {
        IN_TASK.set(false);
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
    dispatch(n_tasks, Task::new(&f));
}

/// [`for_each_chunk`] with the closure erased: every dispatch goes through this one function, out of line, so the
/// pool's machinery stays apart from the tasks it runs.
#[inline(never)]
fn dispatch(n_tasks: usize, task: Task) {
    assert!(!IN_TASK.get(), "nested parallel dispatch from inside a pool task");
    // The caller runs tasks too, inline or as worker 0, so nesting panics on every path.
    let _task = InTask::enter();

    if num_threads() <= 1 || n_tasks <= 1 {
        if n_tasks > 0 {
            // SAFETY: the caller's closure lives until this returns.
            unsafe { task.run(0, n_tasks) };
        }
        return;
    }

    let pool = pool();
    let guard = pool.dispatch.lock().unwrap();

    let job = Job { task, n_tasks };

    pool.counter.store(0, Ordering::Relaxed);
    pool.running.store(num_threads() - 1, Ordering::Relaxed);
    let sleeping = {
        let mut state = pool.state.lock().unwrap();
        state.generation += 1;
        state.job = Some(job);
        pool.published.store(state.generation, Ordering::Release);
        state.sleeping
    };
    // The spinning workers see the new generation by themselves.
    if sleeping > 0 {
        pool.start.notify_all();
    }

    drain(pool, job); // the dispatcher runs as worker 0
    spin_while(|| pool.running.load(Ordering::Acquire) > 0);
    {
        let mut state = pool.state.lock().unwrap();
        while pool.running.load(Ordering::Acquire) > 0 {
            state = pool.done.wait(state).unwrap();
        }
        state.job = None;
    }

    // Re-raise the first task panic after dropping the guard, so the lock
    // releases cleanly (no poison) and the pool stays usable.
    let panicked = pool.panic.lock().unwrap().take();
    drop(guard);
    if let Some(payload) = panicked {
        resume_unwind(payload);
    }
}

/// `f(i)` for every `i` in `0..n_tasks`, in parallel.
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
struct SendPtr<T>(*mut T);

// SAFETY: `SendPtr` grants no access by itself; every dereference is inside an
// `unsafe` block whose comment establishes that the range being touched belongs
// to exactly one task, and the elements it reaches may move to that task's thread.
unsafe impl<T: Send> Send for SendPtr<T> {}
unsafe impl<T: Send> Sync for SendPtr<T> {}

impl<T> SendPtr<T> {
    /// Offset the base by `n` elements.
    ///
    /// # Safety
    /// `n` stays inside the allocation, and any write targets a slot no concurrent task touches.
    #[inline]
    unsafe fn add(&self, n: usize) -> *mut T {
        unsafe { self.0.add(n) }
    }
}

/// Parallel `data.chunks_mut(chunk).enumerate().for_each(f)`; the final chunk may
/// be shorter.
pub fn chunks_mut<T: Send, F>(data: &mut [T], chunk: usize, f: F)
where
    F: Fn(usize, &mut [T]) + Sync,
{
    let view = Chunks::new(data, chunk);
    // SAFETY: the dispatch runs each task `i` once, and `data` stays borrowed until it returns.
    for_each(view.count(), |i| f(i, unsafe { view.get(i) }));
}

/// A `chunks_mut` view that can be handed to tasks: `get(i)` is item `i`'s slice.
struct Chunks<T> {
    base: SendPtr<T>,
    width: usize,
    len: usize,
}

impl<T> Chunks<T> {
    /// View `data` as `len.div_ceil(width)` chunks of `width` (the last shorter).
    #[must_use]
    fn new(data: &mut [T], width: usize) -> Self {
        assert!(width > 0, "chunk width must be non-zero");
        Self {
            base: SendPtr(data.as_mut_ptr()),
            width,
            len: data.len(),
        }
    }

    /// Number of chunks.
    #[must_use]
    const fn count(&self) -> usize {
        self.len.div_ceil(self.width)
    }

    /// Chunk `i`.
    ///
    /// # Safety
    /// `i < self.count()`, no other live borrow covers chunk `i`, and the
    /// underlying buffer outlives `'a`. Calling this once per `i` inside a
    /// [`for_each`] body satisfies all three.
    #[inline]
    unsafe fn get<'a>(&self, i: usize) -> &'a mut [T] {
        let start = i * self.width;
        debug_assert!(start < self.len);
        unsafe { std::slice::from_raw_parts_mut(self.base.add(start), self.width.min(self.len - start)) }
    }
}

/// [`fold_reduce`] over the chunks of `N` buffers: task `i` gets chunk `i` of each, so a kernel writing several
/// tables takes its slices of all of them.
///
/// Buffer `k` is cut into chunks of `widths[k]`, the last shorter. There are as many tasks as the
/// buffer with the most chunks has, and a buffer with fewer gives an empty slice to the tasks past its end.
pub fn map_reduce_chunks_mut<T, const N: usize, A, I, F, C>(
    bufs: [&mut [T]; N],
    widths: [usize; N],
    init: I,
    fold: F,
    combine: C,
) -> A
where
    T: Send,
    A: Send,
    I: Fn() -> A + Sync,
    F: Fn(&mut A, usize, [&mut [T]; N]) + Sync,
    C: Fn(A, A) -> A,
{
    let mut widths = widths.into_iter();
    let views = bufs.map(|buf| Chunks::new(buf, widths.next().expect("one width per buffer")));
    let n_tasks = views.iter().map(Chunks::count).max().unwrap_or(0);
    fold_reduce(
        n_tasks,
        init,
        |acc, i| {
            // SAFETY: the dispatch runs each task `i` once, and `bufs` stays borrowed until it returns, so chunk `i`
            // of each buffer is taken once and the slices are disjoint.
            let chunks = views.each_ref().map(|view| {
                if i < view.count() {
                    unsafe { view.get(i) }
                } else {
                    &mut []
                }
            });
            fold(acc, i, chunks);
        },
        combine,
    )
}

/// Parallel `for (i, slot) in dst.iter_mut().enumerate() { *slot = build(i) }`.
/// The in-place counterpart of [`map_collect`], which allocates.
pub fn fill<T: Send, F: Fn(usize) -> T + Sync>(dst: &mut [T], build: F) {
    chunks_mut(dst, 1, |i, slot| slot[0] = build(i));
}

/// `n` copies of `value`, written in parallel: a large buffer's first pass over memory is spread across the pool.
pub fn filled<T: Copy + Send + Sync>(n: usize, value: T) -> Vec<T> {
    map_collect(n, |_| value)
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

/// Blocks per worker in a [`fold_reduce`]: more than one, so that faster cores take more.
const BLOCKS_PER_WORKER: usize = 4;

/// The smallest `i` in `0..n_tasks` with `pred(i)`, or `None`.
///
/// The workers claim ranges in increasing order and test each in order, up to its first hit or the least hit found so
/// far: every index below the answer is tested, and few past it.
pub fn find_first<P: Fn(usize) -> bool + Sync>(n_tasks: usize, pred: P) -> Option<usize> {
    let best = AtomicUsize::new(n_tasks);
    for_each_chunk(n_tasks, |start, end| {
        let below = |i: &usize| *i < best.load(Ordering::Relaxed);
        if let Some(hit) = (start..end).take_while(below).find(|&i| pred(i)) {
            best.fetch_min(hit, Ordering::Relaxed);
        }
    });
    Some(best.into_inner()).filter(|&i| i < n_tasks)
}

/// Parallel fold-then-reduce: `0..n_tasks` is cut into `BLOCKS_PER_WORKER` blocks per worker, each block folds its
/// indices in order into an accumulator of its own, built with `init`, and the accumulators `combine` on the dispatcher
/// in block order. The blocks depend on the worker count, so `combine` must be associative and commutative, with
/// `init()` neutral.
///
/// This is the shape for a reduction whose accumulator is itself a buffer (a 64-slot bit-fold, say): the buffer is
/// allocated once per block rather than once per item. Scratch a block reuses across items rides in the accumulator
/// too, `combine` keeping either side's.
pub fn fold_reduce<A, I, F, C>(n_tasks: usize, init: I, fold: F, combine: C) -> A
where
    A: Send,
    I: Fn() -> A + Sync,
    F: Fn(&mut A, usize) + Sync,
    C: Fn(A, A) -> A,
{
    let blocks = n_tasks.min(BLOCKS_PER_WORKER * num_threads());
    let accs = map_collect(blocks, |b| {
        let mut acc = init();
        for i in b * n_tasks / blocks..(b + 1) * n_tasks / blocks {
            fold(&mut acc, i);
        }
        acc
    });
    accs.into_iter().fold(init(), combine)
}

/// Parallel map-reduce over `0..n_tasks`, i.e. `(0..n).map(map).fold(identity(), reduce)`. Each block of
/// [`fold_reduce`] folds its indices into one partial from `identity()`; the partials combine on the dispatcher. The
/// blocks depend on the worker count, so `reduce` must be associative and commutative, with `identity()` neutral.
pub fn map_reduce<T, ID, M, R>(n_tasks: usize, identity: ID, map: M, reduce: R) -> T
where
    T: Copy + Send,
    ID: Fn() -> T + Sync,
    M: Fn(usize) -> T + Sync,
    R: Fn(T, T) -> T + Sync,
{
    fold_reduce(
        n_tasks,
        identity,
        |partial, i| *partial = reduce(*partial, map(i)),
        &reduce,
    )
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    #[should_panic(expected = "already runs")]
    fn a_fixed_count_refuses_another() {
        set_num_threads(num_threads());
        set_num_threads(num_threads() + 1);
    }
}
