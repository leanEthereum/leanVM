//! The pool's contract: every item runs exactly once, writes land where the
//! caller partitioned them, reductions are order-independent, and a task panic
//! surfaces on the dispatcher without wedging the pool.

use std::sync::atomic::{AtomicUsize, Ordering};

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
fn tiny_dispatches_run_every_item_while_workers_wake_late() {
    // Invariant: a dispatch finishes once its items are done, whatever the idle workers do.
    //
    // Fixture state: jobs of 2 items leave most workers idle, and a worker that wakes late
    // must find the job closed rather than run it, or run the next one it finds open.
    //
    //     batch 0:  back-to-back, workers spinning
    //     batch 1:  after 5 ms idle, workers parked
    for batch in 0..2 {
        if batch == 1 {
            std::thread::sleep(std::time::Duration::from_millis(5));
        }
        for round in 0..1000 {
            let hits: Vec<AtomicUsize> = (0..2).map(|_| AtomicUsize::new(0)).collect();
            parallel::for_each(2, |i| {
                hits[i].fetch_add(1, Ordering::Relaxed);
            });
            // The borrow of `hits` ends here, so a late worker touching it would be a use after return.
            assert!(
                hits.iter().all(|h| h.load(Ordering::Relaxed) == 1),
                "batch {batch} round {round}"
            );
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
fn chunks_mut2_stays_in_lockstep() {
    let mut a = vec![0usize; 3_000];
    let mut b = vec![0usize; 3_000];
    parallel::chunks_mut2(&mut a, &mut b, 128, |ci, sa, sb| {
        assert_eq!(sa.len(), sb.len());
        for (k, (x, y)) in sa.iter_mut().zip(sb.iter_mut()).enumerate() {
            *x = ci * 128 + k;
            *y = 2 * (ci * 128 + k);
        }
    });
    assert!(a.iter().enumerate().all(|(i, &v)| v == i));
    assert!(b.iter().enumerate().all(|(i, &v)| v == 2 * i));
}

#[test]
fn for_each_mut_reports_global_indices() {
    let mut data = vec![0usize; 7_777];
    parallel::for_each_mut(&mut data, |i, slot| *slot = i * 3);
    assert!(data.iter().enumerate().all(|(i, &v)| v == i * 3));
}

#[test]
fn map_reduce_matches_the_sequential_fold() {
    for n in SIZES {
        let got = parallel::map_reduce(n, || 0usize, |i| i + 1, |a, b| a + b);
        assert_eq!(got, (0..n).map(|i| i + 1).sum::<usize>(), "n = {n}");
    }
}

#[test]
fn map_reduce_with_state_reuses_worker_scratch() {
    for n in SIZES {
        // The scratch is a per-worker counter of how many items it folded; the
        // accumulator is the running sum. Both must survive across claims.
        let got = parallel::map_reduce_with_state(
            n,
            || 0usize,
            || 0usize,
            |folded, acc, i| {
                *folded += 1;
                *acc += i;
            },
            |a, b| a + b,
        );
        assert_eq!(got, (0..n).sum::<usize>(), "n = {n}");
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

/// The default holds back one performance worker exactly when there are
/// efficiency workers to absorb its share (see `default_topology`), so a
/// homogeneous host must field every core it reports.
#[test]
fn default_topology_reserves_no_worker_on_a_homogeneous_host() {
    // The env var this binary may have inherited would pin the count and defeat
    // the check, so only assert when nothing is pinned.
    if std::env::var_os("LEANVM_NUM_THREADS").is_some() {
        return;
    }
    let topo = parallel::topology();
    if topo.efficiency == 0 {
        let cores = std::thread::available_parallelism().map_or(1, |n| n.get());
        assert_eq!(topo.perf, cores, "nothing may be reserved without efficiency workers");
    }
}
