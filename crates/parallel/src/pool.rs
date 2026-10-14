//! The pool's engine: workers, the claim counter, and one dispatch at a time.
//!
//! - The dispatcher publishes a job and drains it as worker 0.
//! - Workers spin, then park, between dispatches.
//! - A task panic is caught on its worker and resumed on the dispatcher once every worker has stopped.

use crate::topology::{self, Qos, set_qos};
use crate::{Topology, for_each, num_threads};
use std::any::Any;
use std::cell::{Cell, UnsafeCell};
use std::marker::PhantomData;
use std::num::NonZeroUsize;
use std::ops::Deref;
use std::panic::{AssertUnwindSafe, catch_unwind, resume_unwind};
use std::ptr::NonNull;
use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering};
use std::sync::{Mutex, Once, OnceLock};
use std::thread::{Builder, Thread};
use thiserror::Error;

/// Idle spins before a worker parks: long enough to stay hot across back-to-back
/// dispatches, short enough to yield the core during a sequential stretch.
///
/// Miri interprets every spin, so there a worker parks at once.
const SPIN_LIMIT: u32 = if cfg!(miri) { 0 } else { 1 << 12 };

/// How finely guided scheduling divides the remaining work.
const CLAIM_DIVISOR: usize = 4;

/// Largest range claimed in one scheduling step.
const MAX_CLAIM_BATCH: usize = 1 << 12;

thread_local! {
    /// The running thread's worker index: 0 for the dispatcher, `1..` for the pool's threads.
    static WORKER_ID: Cell<usize> = const { Cell::new(0) };
    /// Why a dispatch from this thread would be a bug, if it would: set inside a pool task and inside [`serial`].
    static REFUSED: Cell<Option<&'static str>> = const { Cell::new(None) };
}

/// The running thread's worker index, below the thread count and unique among live workers.
pub(crate) fn worker_id() -> usize {
    WORKER_ID.get()
}

/// Refuse every dispatch from this thread while the returned guard lives: one panics, whatever the pool's size.
///
/// The native verifier holds one, so that a dispatch it reaches fails every test that verifies a proof, rather than
/// only those whose sizes cross a kernel's threshold or whose pool has more than one worker.
#[must_use = "dispatch is refused only while the guard lives"]
pub fn serial() -> Serial {
    let previous = REFUSED.get();
    REFUSED.set(Some(previous.unwrap_or("parallel dispatch inside a serial section")));
    Serial {
        previous,
        _thread: PhantomData,
    }
}

/// A [`serial`] section: dropping it restores the previous refusal, on return and on unwinding alike.
pub struct Serial {
    previous: Option<&'static str>,
    /// The refusal is this thread's, so the guard stays on it.
    _thread: PhantomData<*const ()>,
}

impl Drop for Serial {
    fn drop(&mut self) {
        REFUSED.set(self.previous);
    }
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

impl Deref for Line {
    type Target = AtomicUsize;
    #[inline]
    fn deref(&self) -> &AtomicUsize {
        &self.0
    }
}

/// The pool's shared state, leaked once and shared by every worker.
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

/// The pool was already configured with another shape.
#[derive(Clone, Copy, Debug, Error, PartialEq, Eq)]
#[error("the pool is already configured as {0:?}")]
pub struct AlreadyConfigured(pub Topology);

/// Initializes exactly `threads` workers, the dispatcher included, without touching the environment.
///
/// Call it before any parallel operation.
///
/// Repeating the same configuration succeeds.
///
/// # Errors
///
/// Returns the existing shape when another configuration initialized the pool first.
pub fn init_with_threads(threads: NonZeroUsize) -> Result<(), AlreadyConfigured> {
    topology::configure_threads(threads).map_err(AlreadyConfigured)?;
    init();
    Ok(())
}

/// The pool, spawned on first use.
fn pool() -> &'static Pool {
    static POOL: OnceLock<&'static Pool> = OnceLock::new();
    POOL.get_or_init(|| {
        let topo = crate::topology();
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
            Builder::new()
                .name(format!("parallel-{id}"))
                .spawn(move || worker_main(pool_ref, id, qos))
                .expect("failed to spawn a pool worker");
        }
        pool_ref
    })
}

/// A pool thread's life: wait for a dispatch, join it while it is open, repeat.
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
    REFUSED.set(Some("nested parallel dispatch from inside a pool task")); // see `for_each_chunk`
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
    REFUSED.set(None);
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
/// independent unit and keep the levels below it sequential. Also if called inside [`serial`].
pub fn for_each_chunk<F: Fn(usize, usize) + Sync>(n_tasks: usize, f: F) {
    if let Some(why) = REFUSED.get() {
        panic!("{why}");
    }

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
