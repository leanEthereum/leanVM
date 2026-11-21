//! The pool's contract: every item runs exactly once, writes land where the
//! caller partitioned them, reductions are order-independent, and a task panic
//! surfaces on the dispatcher without wedging the pool.

extern crate stable_parallel as parallel;
use std::panic::{AssertUnwindSafe, catch_unwind, panic_any};
use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering};
use std::time::Duration;

const SIZES: [usize; 7] = [0, 1, 2, 17, 1_000, 4_096, 100_000];

#[test]
fn every_item_runs_exactly_once() {
    for n in SIZES {
        let counts: Vec<AtomicUsize> = (0..n).map(|_| AtomicUsize::new(0)).collect();
        parallel::for_each(n, |i| {
            counts[i].fetch_add(1, Ordering::Relaxed);
        });
        for (i, c) in counts.iter().enumerate() {
            assert_eq!(c.load(Ordering::Relaxed), 1, "item {i} of {n}");
        }
    }
}

#[test]
fn chunk_ranges_tile_the_domain() {
    for n in SIZES {
        let seen: Vec<AtomicUsize> = (0..n).map(|_| AtomicUsize::new(0)).collect();
        parallel::for_each_chunk(n, |start, end| {
            assert!(start < end && end <= n, "range {start}..{end} outside 0..{n}");
            for i in start..end {
                seen[i].fetch_add(1, Ordering::Relaxed);
            }
        });
        assert!(seen.iter().all(|c| c.load(Ordering::Relaxed) == 1), "n = {n}");
    }
}

#[test]
fn map_collect_preserves_index_order() {
    for n in SIZES {
        let out = parallel::map_collect(n, |i| i * i);
        assert_eq!(out.len(), n);
        assert!(out.iter().enumerate().all(|(i, &v)| v == i * i), "n = {n}");
    }
}

#[test]
fn fill_writes_every_slot() {
    for n in SIZES {
        let mut dst = vec![usize::MAX; n];
        parallel::fill(&mut dst, |i| i + 7);
        assert!(dst.iter().enumerate().all(|(i, &v)| v == i + 7), "n = {n}");
    }
}

#[test]
fn chunks_mut_hands_out_disjoint_slices() {
    for chunk in [1usize, 3, 64, 1024] {
        let mut data = vec![0usize; 5_000];
        parallel::chunks_mut(&mut data, chunk, |ci, sub| {
            for (k, slot) in sub.iter_mut().enumerate() {
                *slot = ci * chunk + k;
            }
        });
        assert!(data.iter().enumerate().all(|(i, &v)| v == i), "chunk = {chunk}");
    }
}

#[test]
fn map_reduce_matches_the_sequential_fold() {
    for n in SIZES {
        let got = parallel::map_reduce(n, || 0usize, |i| i + 1, |a, b| a + b);
        assert_eq!(got, (0..n).map(|i| i + 1).sum::<usize>(), "n = {n}");
    }
}

#[test]
fn fold_reduce_matches_the_sequential_fold() {
    for n in SIZES {
        // A buffer accumulator, allocated once per worker and kept across its claims.
        let got = parallel::fold_reduce(
            n,
            || vec![0usize; 3],
            |acc, i| acc[i % 3] += i,
            |mut a, b| {
                a.iter_mut().zip(b).for_each(|(a, b)| *a += b);
                a
            },
        );
        let want: Vec<usize> = (0..3).map(|k| (0..n).filter(|i| i % 3 == k).sum()).collect();
        assert_eq!(got, want, "n = {n}");
    }
}

#[test]
fn task_panic_reaches_the_dispatcher_and_the_pool_survives() {
    let result = std::panic::catch_unwind(|| {
        parallel::for_each(1_000, |i| {
            assert_ne!(i, 500, "boom");
        });
    });
    assert!(result.is_err(), "a task panic must be re-raised on the dispatcher");
    // The dispatch lock must not be poisoned and the workers must still be alive.
    let out = parallel::map_collect(1_000, |i| i);
    assert!(out.iter().enumerate().all(|(i, &v)| v == i));
}

/// Nesting is a bug, not a slow path: it must be reported, not silently
/// serialized, so that a lost fan-out cannot hide as a slow one.
#[test]
#[should_panic = "nested parallel dispatch"]
fn nested_dispatch_panics_rather_than_deadlocking() {
    parallel::for_each(parallel::num_threads().max(2), |_| {
        parallel::for_each(4, |_| {});
    });
}

#[test]
fn find_first_returns_the_global_minimum() {
    for n in SIZES {
        // Every multiple of 7 matches, so the answer is 0 whenever n > 0.
        let got = parallel::find_first(n, |i| i.is_multiple_of(7));
        assert_eq!(got, (n > 0).then_some(0), "n = {n}");
        // A single match deep in the range must still be found.
        let target = n / 2;
        assert_eq!(parallel::find_first(n, |i| i == target), (n > 0).then_some(target));
        // No match.
        assert_eq!(parallel::find_first(n, |_| false), None, "n = {n}");
    }
}

#[test]
#[should_panic = "nested parallel dispatch"]
fn nested_dispatch_panics_even_when_the_outer_runs_inline() {
    parallel::for_each(1, |_| parallel::for_each(4, |_| {}));
}

#[test]
fn back_to_back_dispatches_leave_no_worker_in_a_finished_one() {
    // Invariant: a worker that wakes after a dispatch closed must not run that dispatch's closure, whose
    // captures are dead by then, and every item of every dispatch runs exactly once.
    //
    // Fixture state: 2_000 dispatches of 2 to 17 items, every other one with a slow first item (a short
    // sleep, so workers arrive after the others are done), every 97th one panicking on its last item.
    // Each dispatch counts into a fresh vector that dies when it returns.
    for round in 0..2_000usize {
        let n = 2 + round % 16;
        let counts: Vec<AtomicUsize> = (0..n).map(|_| AtomicUsize::new(0)).collect();
        let panics = round % 97 == 0;
        let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            parallel::for_each(n, |i| {
                if round % 2 == 0 && i == 0 {
                    std::thread::sleep(std::time::Duration::from_micros(50));
                }
                counts[i].fetch_add(1, Ordering::Relaxed);
                assert!(!(panics && i == n - 1), "boom");
            });
        }));
        // Expected: the panic is re-raised exactly when one was thrown, and every item ran once.
        assert_eq!(result.is_err(), panics, "round {round}");
        assert!(counts.iter().all(|c| c.load(Ordering::Relaxed) == 1), "round {round}");
    }
}

/// A panic payload whose `Drop` panics. The pool must never drop one where that panic could escape.
struct Bomb;

impl Drop for Bomb {
    fn drop(&mut self) {
        panic!("a panic payload's drop panicked");
    }
}

/// Counts a task as running until dropped, unwinding included.
struct Running<'a>(&'a AtomicUsize);

impl<'a> Running<'a> {
    fn enter(count: &'a AtomicUsize) -> Self {
        count.fetch_add(1, Ordering::SeqCst);
        Self(count)
    }
}

impl Drop for Running<'_> {
    fn drop(&mut self) {
        self.0.fetch_sub(1, Ordering::SeqCst);
    }
}

/// Two tasks of one dispatch panic with a `Bomb`, one on the dispatcher and one on a worker: the keeper first, the
/// surplus once the pool has had time to keep the keeper's payload, so the pool is left holding a second payload whose
/// `Drop` panics. The other workers' tasks stay in the closure until after the surplus panic.
fn surplus_panic_payload_is_contained(surplus_on_dispatcher: bool) {
    let pause = || std::thread::sleep(Duration::from_millis(20));
    let wait = |flag: &AtomicBool| {
        while !flag.load(Ordering::SeqCst) {
            std::thread::yield_now();
        }
    };
    let dispatcher = std::thread::current().id();
    let sequential = parallel::num_threads() == 1;
    // Whether each side's actor has started, indexed by `on_dispatcher`.
    let present = [AtomicBool::new(false), AtomicBool::new(false)];
    let worker_actor_taken = AtomicBool::new(false);
    let (kept, surplus) = (AtomicBool::new(false), AtomicBool::new(false));
    let running = AtomicUsize::new(0);
    // Every worker holds at most one task until the surplus panic, so one is left for the dispatcher.
    let caught = catch_unwind(AssertUnwindSafe(|| {
        parallel::for_each(parallel::num_threads().max(2), |_| {
            let _running = Running::enter(&running);
            if sequential {
                // The task runs inline and its panic unwinds straight to the caller: there is no worker.
                panic_any(Bomb);
            }
            let on_dispatcher = std::thread::current().id() == dispatcher;
            if !on_dispatcher && worker_actor_taken.swap(true, Ordering::SeqCst) {
                wait(&surplus);
                pause();
                return;
            }
            present[usize::from(on_dispatcher)].store(true, Ordering::SeqCst);
            if on_dispatcher == surplus_on_dispatcher {
                wait(&kept);
                pause();
                surplus.store(true, Ordering::SeqCst);
            } else {
                wait(&present[usize::from(!on_dispatcher)]);
                kept.store(true, Ordering::SeqCst);
            }
            panic_any(Bomb);
        });
    }));
    let payload = caught.expect_err("a task panic must be re-raised on the dispatcher");
    let resumed_a_bomb = payload.is::<Bomb>();
    std::mem::forget(payload);
    assert_eq!(running.load(Ordering::SeqCst), 0, "a task outlived the dispatch");
    assert!(resumed_a_bomb, "the dispatch must re-raise the first task panic");
    let out = parallel::map_collect(1_000, |i| i);
    assert!(out.iter().enumerate().all(|(i, &v)| v == i));
}

#[test]
fn surplus_panic_payload_on_the_dispatcher_is_contained() {
    surplus_panic_payload_is_contained(true);
}

#[test]
fn surplus_panic_payload_on_a_worker_is_contained() {
    surplus_panic_payload_is_contained(false);
}
