//! Data-parallel kernels over a fixed-size rayon pool.

use rayon::prelude::*;
use std::sync::OnceLock;

/// Worker count: `LEANVM_NUM_THREADS` when set, `1` being strictly sequential, else one per physical core, as
/// experimental's: the logical CPUs the platform reports, halved where Linux says SMT is active (a core's second
/// hardware thread slows a proof on a many-core machine).
#[must_use]
#[inline]
pub fn num_threads() -> usize {
    static NUM_THREADS: OnceLock<usize> = OnceLock::new();
    *NUM_THREADS.get_or_init(|| {
        std::env::var("LEANVM_NUM_THREADS")
            .ok()
            .and_then(|v| v.parse::<usize>().ok())
            .filter(|&n| n > 0)
            .unwrap_or_else(|| {
                let logical = std::thread::available_parallelism().map_or(1, |n| n.get());
                let smt = std::fs::read_to_string("/sys/devices/system/cpu/smt/active").is_ok_and(|s| s.trim() == "1");
                if smt { (logical / 2).max(1) } else { logical }
            })
    })
}

fn pool() -> &'static rayon::ThreadPool {
    static POOL: OnceLock<rayon::ThreadPool> = OnceLock::new();
    POOL.get_or_init(|| {
        rayon::ThreadPoolBuilder::new()
            .num_threads(num_threads())
            .thread_name(|id| format!("parallel-{id}"))
            .build()
            .expect("failed to build the pool")
    })
}

/// Start the pool's workers, so that no timed work pays for it.
pub fn init() {
    pool().broadcast(|_| ());
}

/// Run `f(start, end)` over disjoint ranges tiling `0..n_tasks`, in parallel.
pub fn for_each_chunk<F: Fn(usize, usize) + Sync>(n_tasks: usize, f: F) {
    let chunk = n_tasks.div_ceil(4 * num_threads()).max(1);
    pool().install(|| {
        (0..n_tasks.div_ceil(chunk))
            .into_par_iter()
            .for_each(|c| f(c * chunk, ((c + 1) * chunk).min(n_tasks)));
    });
}

/// `f(i)` for every `i` in `0..n_tasks`, in parallel.
pub fn for_each<F: Fn(usize) + Sync>(n_tasks: usize, f: F) {
    pool().install(|| (0..n_tasks).into_par_iter().for_each(&f));
}

/// Parallel `data.chunks_mut(chunk).enumerate().for_each(f)`; the final chunk may be shorter.
pub fn chunks_mut<T: Send, F>(data: &mut [T], chunk: usize, f: F)
where
    F: Fn(usize, &mut [T]) + Sync,
{
    pool().install(|| data.par_chunks_mut(chunk).enumerate().for_each(|(i, c)| f(i, c)));
}

/// [`map_reduce_with_state`] over the chunks of `N` buffers: task `i` gets chunk `i` of each, so a kernel
/// writing several tables takes its slices of all of them.
///
/// Buffer `k` is cut into chunks of `widths[k]`, the last shorter. There are as many tasks as the
/// buffer with the most chunks has, and a buffer with fewer gives an empty slice to the tasks past its end.
pub fn map_reduce_chunks_mut<T, const N: usize, S, A, IS, IA, F, C>(
    bufs: [&mut [T]; N],
    widths: [usize; N],
    init_state: IS,
    init_acc: IA,
    fold: F,
    combine: C,
) -> A
where
    T: Send,
    S: Send,
    A: Send,
    IS: Fn() -> S + Sync,
    IA: Fn() -> A + Sync,
    F: Fn(&mut S, &mut A, usize, [&mut [T]; N]) + Sync,
    C: Fn(A, A) -> A,
{
    let mut widths = widths.into_iter();
    let mut chunks = bufs.map(|buf| buf.chunks_mut(widths.next().expect("one width per buffer")));
    let n_tasks = chunks.iter().map(ExactSizeIterator::len).max().unwrap_or(0);
    let tasks: Vec<[&mut [T]; N]> = (0..n_tasks)
        .map(|_| chunks.each_mut().map(|c| c.next().unwrap_or_default()))
        .collect();
    let partials: Vec<A> = pool().install(|| {
        tasks
            .into_par_iter()
            .enumerate()
            .fold(
                || (init_state(), init_acc()),
                |(mut state, mut acc), (i, task)| {
                    fold(&mut state, &mut acc, i, task);
                    (state, acc)
                },
            )
            .map(|(_, acc)| acc)
            .collect()
    });
    partials.into_iter().fold(init_acc(), combine)
}

/// Parallel `for (i, slot) in dst.iter_mut().enumerate() { *slot = build(i) }`.
/// The in-place counterpart of [`map_collect`], which allocates.
pub fn fill<T: Send, F: Fn(usize) -> T + Sync>(dst: &mut [T], build: F) {
    pool().install(|| dst.par_iter_mut().enumerate().for_each(|(i, slot)| *slot = build(i)));
}

/// `n` copies of `value`, written in parallel: a large buffer's first pass over memory is spread across the pool.
pub fn filled<T: Copy + Send + Sync>(n: usize, value: T) -> Vec<T> {
    map_collect(n, |_| value)
}

/// Parallel `(0..n_tasks).map(f).collect::<Vec<_>>()`.
pub fn map_collect<T: Send, F: Fn(usize) -> T + Sync>(n_tasks: usize, f: F) -> Vec<T> {
    pool().install(|| (0..n_tasks).into_par_iter().map(&f).collect())
}

/// The smallest `i` in `0..n_tasks` with `pred(i)`, or `None`.
pub fn find_first<P: Fn(usize) -> bool + Sync>(n_tasks: usize, pred: P) -> Option<usize> {
    pool().install(|| (0..n_tasks).into_par_iter().find_first(|&i| pred(i)))
}

/// Parallel map-reduce over `0..n_tasks`, i.e. `(0..n).map(map).reduce(identity, reduce)`; `reduce` must be
/// associative and commutative, with `identity()` neutral.
pub fn map_reduce<T, ID, M, R>(n_tasks: usize, identity: ID, map: M, reduce: R) -> T
where
    T: Send,
    ID: Fn() -> T,
    M: Fn(usize) -> T + Sync,
    R: Fn(T, T) -> T + Sync,
{
    let partials: Vec<T> = pool().install(|| {
        (0..n_tasks)
            .into_par_iter()
            .fold(
                || None,
                |acc: Option<T>, i| Some(acc.map_or_else(|| map(i), |acc| reduce(acc, map(i)))),
            )
            .flatten()
            .collect()
    });
    partials.into_iter().fold(identity(), &reduce)
}

/// Parallel fold-then-reduce: accumulators built with `init` fold the indices, then `combine`; `combine` must be
/// associative and commutative, with `init()` neutral.
pub fn fold_reduce<A, I, F, C>(n_tasks: usize, init: I, fold: F, combine: C) -> A
where
    A: Send,
    I: Fn() -> A + Sync,
    F: Fn(&mut A, usize) + Sync,
    C: Fn(A, A) -> A,
{
    map_reduce_with_state(n_tasks, || (), &init, |_, acc, i| fold(acc, i), combine)
}

/// Parallel reduce with reusable scratch beside each accumulator, so the per-item body need not allocate; `combine`
/// must be associative and commutative, with `init_acc()` neutral.
pub fn map_reduce_with_state<S, A, IS, IA, F, C>(n_tasks: usize, init_state: IS, init_acc: IA, fold: F, combine: C) -> A
where
    S: Send,
    A: Send,
    IS: Fn() -> S + Sync,
    IA: Fn() -> A + Sync,
    F: Fn(&mut S, &mut A, usize) + Sync,
    C: Fn(A, A) -> A,
{
    let partials: Vec<A> = pool().install(|| {
        (0..n_tasks)
            .into_par_iter()
            .fold(
                || (init_state(), init_acc()),
                |(mut state, mut acc), i| {
                    fold(&mut state, &mut acc, i);
                    (state, acc)
                },
            )
            .map(|(_, acc)| acc)
            .collect()
    });
    partials.into_iter().fold(init_acc(), combine)
}
