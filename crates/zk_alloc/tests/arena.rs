//! The arena is driven explicitly: the process keeps its own allocator, and only
//! [`ArenaVec`] buffers live in a slab. Everything else must be untouched by a
//! phase reset, which is the property that lets a library use the arena without
//! imposing it on its consumers.

use std::sync::atomic::{AtomicUsize, Ordering};
use zk_alloc::{ArenaVec, enable_arena, enter_phase};

const N: usize = 4096;

fn phase_reset_recycles_the_slab_and_spares_the_system_heap() {
    // One arena allocation on this thread claims its slab at the base.
    let p1 = {
        let _phase = enter_phase();
        let mut first: ArenaVec<u64> = ArenaVec::with_capacity(N);
        first.resize(N, 0xABCD); // fits the reservation, so the pointer stays put
        first.as_ptr() as usize
    };

    // Allocated with the arena closed: goes to the system allocator and must
    // survive the next reset.
    let canary = vec![0xAB_u8; 8192];

    // The slab resets, so an identically shaped buffer lands at the same address.
    let p2 = {
        let _phase = enter_phase();
        let mut second: ArenaVec<u64> = ArenaVec::with_capacity(N);
        second.resize(N, 0x1234);
        assert!(second.iter().all(|&x| x == 0x1234));
        second.as_ptr() as usize
    };

    assert_eq!(p1, p2, "a phase reset must recycle the slab");
    assert!(
        canary.iter().all(|&b| b == 0xAB),
        "the reset corrupted a system allocation"
    );

    // With no phase open, ArenaVec is an ordinary system-allocated vector.
    let mut outside: ArenaVec<u64> = ArenaVec::new();
    outside.extend(0..1000);
    assert_eq!(outside.iter().sum::<u64>(), (0..1000).sum());
}

fn guard_closes_the_phase_on_unwind() {
    let panicked = std::panic::catch_unwind(|| {
        let _phase = enter_phase();
        let _v: ArenaVec<u8> = ArenaVec::filled(7, 32);
        panic!("boom");
    });
    assert!(panicked.is_err());
    // If the guard had leaked the open phase, this would trip the nesting assert.
    let _phase = enter_phase();
}

fn growth_preserves_contents_across_reallocation() {
    let _phase = enter_phase();
    let mut v: ArenaVec<usize> = ArenaVec::new();
    for i in 0..10_000 {
        v.push(i);
    }
    assert_eq!(v.len(), 10_000);
    assert!(v.iter().copied().eq(0..10_000));
}

fn zeroed_clears_a_recycled_slab() {
    {
        let _phase = enter_phase();
        let mut dirty: ArenaVec<u64> = ArenaVec::filled(!0, N);
        dirty[0] = 1; // keep the buffer live and written
    }
    {
        // Same shape, same slab bytes: `zeroed` must not inherit them.
        let _phase = enter_phase();
        // SAFETY: all-zero is a valid u64.
        let fresh: ArenaVec<u64> = unsafe { ArenaVec::zeroed(N) };
        assert!(fresh.iter().all(|&x| x == 0), "zeroed must overwrite stale slab bytes");
    }
}

fn drop_runs_for_elements_that_need_it() {
    static DROPS: AtomicUsize = AtomicUsize::new(0);

    struct Noisy(#[allow(dead_code)] usize);
    impl Drop for Noisy {
        fn drop(&mut self) {
            DROPS.fetch_add(1, Ordering::Relaxed);
        }
    }

    let _phase = enter_phase();
    {
        let mut v: ArenaVec<Noisy> = ArenaVec::new();
        for i in 0..100 {
            v.push(Noisy(i));
        }
        v.truncate(40);
        assert_eq!(DROPS.load(Ordering::Relaxed), 60, "truncate drops the tail");
    }
    assert_eq!(DROPS.load(Ordering::Relaxed), 100, "drop releases the rest");
}

fn zero_sized_elements_never_allocate() {
    let _phase = enter_phase();
    let mut v: ArenaVec<()> = ArenaVec::new();
    for _ in 0..1000 {
        v.push(());
    }
    assert_eq!(v.len(), 1000);
    assert_eq!(v.capacity(), usize::MAX);
}

/// The shape the LIFO pop cannot reclaim, and the reason the reuse list exists:
/// allocate the next buffer, release the previous one. Nothing is ever freed at
/// the cursor, so without reuse the cursor would grow by a buffer per iteration.
fn reuse_holds_a_rotation_at_its_live_set() {
    let words = zk_alloc::REUSE_MIN; // `REUSE_MIN * 8` bytes, well over the floor
    let buf = words * size_of::<u64>();
    let rounds = 16;

    // A thread publishes its peak only when it next RESETS, so bracket the
    // rotation with phases that force one.
    let flush = || {
        let _phase = enter_phase();
        let _tiny: ArenaVec<u64> = ArenaVec::with_capacity(1);
    };
    flush();
    let before = zk_alloc::stats().peak_bytes;
    {
        let _phase = enter_phase();
        let mut live = Some(ArenaVec::<u64>::with_capacity(words));
        for _ in 0..rounds {
            let next = ArenaVec::<u64>::with_capacity(words);
            drop(live.take());
            live = Some(next);
        }
    }
    flush();

    // Two buffers are live across the swap, so that is the floor; a third would
    // mean the rotation grew the cursor instead of recycling.
    let peak = zk_alloc::stats().peak_bytes - before;
    assert!(
        (2 * buf..3 * buf).contains(&peak),
        "a rotation of {rounds} buffers of {buf} bytes peaked at {peak}, not two buffers"
    );
}

/// A buffer allocated on one thread and released on another must not enter the
/// releasing thread's free list, or that thread hands out memory it does not
/// own. Not hypothetical: `parallel::map_reduce_with_state` builds each worker's
/// accumulator on the worker and folds (and drops) the slots on the dispatcher.
fn a_foreign_release_never_enters_this_thread_s_free_list() {
    let words = zk_alloc::REUSE_MIN; // over the reuse floor, so the list would take it
    let _phase = enter_phase();

    // Claim this thread's slab first, so the worker gets a different one.
    let mine: ArenaVec<u64> = ArenaVec::with_capacity(words);
    let foreign = std::thread::scope(|scope| {
        scope
            .spawn(|| ArenaVec::<u64>::with_capacity(words))
            .join()
            .expect("worker allocates")
    });
    let foreign_addr = foreign.as_ptr() as usize;
    assert_ne!(
        foreign_addr,
        mine.as_ptr() as usize,
        "the worker shared this thread's slab"
    );
    drop(foreign); // released HERE, on a thread whose slab it is not in

    let next: ArenaVec<u64> = ArenaVec::with_capacity(words);
    assert_ne!(
        next.as_ptr() as usize,
        foreign_addr,
        "a release from another thread's slab was recycled into this one"
    );
}

/// Recycled memory must never back two live buffers at once. Mixed sizes and
/// out-of-order releases, so the carve, the merge and the cursor unwind all run
/// (a same-size rotation exercises none of them); every buffer carries its own
/// tag and is checked while all the others are still live, so an overlap shows
/// up here rather than as a proof that quietly stops verifying.
fn recycled_blocks_never_back_two_live_buffers() {
    let _phase = enter_phase();
    let mib = zk_alloc::REUSE_MIN / size_of::<u64>(); // words, so every buffer clears the floor
    let mut seed = 0x243f_6a88_85a3_08d3_u64;
    let mut rand = move || {
        seed ^= seed << 13;
        seed ^= seed >> 7;
        seed ^= seed << 17;
        seed
    };

    let mut live: Vec<(u64, ArenaVec<u64>)> = Vec::new();
    for tag in 1..=200_u64 {
        // Deliberately not a whole number of cache lines, so a carve's remainder
        // has to be realigned rather than starting where the block ended.
        let words = mib * (1 + rand() as usize % 6) + 1;
        let mut buf: ArenaVec<u64> = ArenaVec::with_capacity(words);
        buf.resize(words, tag);
        // Large blocks are served at cache-line alignment, recycled or not.
        assert_eq!(buf.as_ptr() as usize % 64, 0, "buffer {tag} came back under-aligned");
        live.push((tag, buf));
        // The ends are what an overlapping block writes over first.
        for (t, b) in &live {
            assert_eq!((b[0], b[b.len() - 1]), (*t, *t), "buffer {t} was handed out twice");
        }
        if live.len() > 4 {
            live.remove(rand() as usize % live.len());
        }
    }
}

fn escaped_buffers_keep_their_storage_until_release() {
    let phase = enter_phase();
    let mut old = ArenaVec::filled(String::from("live"), 8);
    drop(phase);

    assert!(std::panic::catch_unwind(enter_phase).is_err());
    assert!(old.iter().all(|value| value == "live"));
    old[0].push_str(" buffer");
    assert_eq!(old[0], "live buffer");

    drop(old);
    let _phase = enter_phase();
    let fresh = ArenaVec::filled(String::from("fresh"), 8);
    assert!(fresh.iter().all(|value| value == "fresh"));
}

fn failed_nested_open_preserves_the_active_phase() {
    let phase = enter_phase();
    assert!(std::panic::catch_unwind(enter_phase).is_err());
    let old = ArenaVec::filled(7u64, 8);
    drop(phase);

    assert!(std::panic::catch_unwind(enter_phase).is_err());
    assert_eq!(&*old, &[7; 8]);
    drop(old);
    let _phase = enter_phase();
}

fn a_cross_thread_owner_blocks_reset_until_release() {
    let phase = enter_phase();
    let old = ArenaVec::filled(7u64, N);
    drop(phase);

    std::thread::scope(|scope| {
        let (release, wait) = std::sync::mpsc::channel();
        let worker = scope.spawn(move || {
            wait.recv().unwrap();
            assert_eq!(old[0], 7);
            drop(old);
        });
        assert!(std::panic::catch_unwind(enter_phase).is_err());
        release.send(()).unwrap();
        worker.join().unwrap();
    });
    let _phase = enter_phase();
}

fn growth_after_closing_a_phase_releases_the_reset_barrier() {
    let phase = enter_phase();
    let mut old = ArenaVec::filled(7u64, 8);
    drop(phase);

    old.reserve(N);
    let _phase = enter_phase();
    assert_eq!(&*old, &[7; 8]);
}

fn a_panicking_element_destructor_releases_the_reset_barrier() {
    struct Panics(u8);
    impl Drop for Panics {
        fn drop(&mut self) {
            panic!("element {}", self.0);
        }
    }

    let phase = enter_phase();
    let mut buffer = ArenaVec::new();
    buffer.push(Panics(7));
    drop(phase);

    assert!(std::panic::catch_unwind(|| drop(buffer)).is_err());
    let _phase = enter_phase();
}

fn exited_threads_hand_their_slabs_on() {
    // Invariant: a slab outlives its thread only until the next phase opens.
    //
    // Fixture state: more short-lived threads than there are slabs, one after another,
    // each opening a phase and filling a buffer, as a server's request threads would.
    //
    //     without reuse:  one fresh slab per thread, until they run out
    //     with reuse:     each thread takes the slab its predecessor retired
    let before = zk_alloc::stats().threads;
    let threads = std::thread::available_parallelism().map_or(1, |n| n.get()) + 16;
    let mut addresses = Vec::new();
    for _ in 0..threads {
        let address = std::thread::spawn(|| {
            let _phase = enter_phase();
            let buffer = ArenaVec::filled(7u64, N);
            assert!(buffer.iter().all(|&x| x == 7));
            buffer.as_ptr() as usize
        })
        .join()
        .expect("the request thread ran");
        addresses.push(address);
    }
    // The first thread claims a fresh slab; every later one reuses it.
    assert!(
        zk_alloc::stats().threads <= before + 1,
        "{} slabs for {threads} threads in sequence",
        zk_alloc::stats().threads - before
    );
    assert!(
        addresses.windows(2).all(|w| w[0] == w[1]),
        "each thread took the retired slab"
    );
    // An arena allocation on a slab-less thread is counted, never silent.
    assert_eq!(zk_alloc::stats().overflow, 0);
}

#[test]
fn arena_ownership_and_reuse() {
    // Slabs belong to threads permanently, so all scenarios share one harness thread.
    enable_arena();
    phase_reset_recycles_the_slab_and_spares_the_system_heap();
    guard_closes_the_phase_on_unwind();
    growth_preserves_contents_across_reallocation();
    zeroed_clears_a_recycled_slab();
    drop_runs_for_elements_that_need_it();
    zero_sized_elements_never_allocate();
    reuse_holds_a_rotation_at_its_live_set();
    a_foreign_release_never_enters_this_thread_s_free_list();
    recycled_blocks_never_back_two_live_buffers();
    escaped_buffers_keep_their_storage_until_release();
    failed_nested_open_preserves_the_active_phase();
    a_cross_thread_owner_blocks_reset_until_release();
    growth_after_closing_a_phase_releases_the_reset_barrier();
    a_panicking_element_destructor_releases_the_reset_barrier();
    exited_threads_hand_their_slabs_on();
}
