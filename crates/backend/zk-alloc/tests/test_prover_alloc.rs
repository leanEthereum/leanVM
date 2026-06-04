//! `ProverAlloc` drives the arena as an explicit `allocator_api2` allocator, with the
//! process keeping its **own** global allocator (none is installed here). Only
//! `ProverAlloc`-typed containers touch the arena; everything else is untouched by a
//! phase reset — the property that lets a library use the arena without forcing its
//! allocator on consumers.

use allocator_api2::vec::Vec as AVec;
use zk_alloc::{ProverAlloc, begin_phase, enable_arena, end_phase};

const N: usize = 4096;

#[test]
fn prover_alloc_arena_without_global_allocator() {
    // Opt into the arena: without this, begin_phase/end_phase are inert and ProverAlloc
    // would transparently use the system allocator (no slab reuse to observe).
    enable_arena();

    // Phase 1: one arena allocation on this (main) thread → claims the slab at its base.
    begin_phase();
    let mut v: AVec<u64, ProverAlloc> = AVec::with_capacity_in(N, ProverAlloc);
    v.resize(N, 0xABCD); // fits the reservation: no realloc, pointer stays put
    let p1 = v.as_ptr() as usize;
    end_phase();

    // Arena is off: this lands in the system allocator and must survive the next reset.
    let canary = vec![0xAB_u8; 8192];

    // Phase 2: the slab is reset, so an identically-shaped buffer reuses the same address.
    begin_phase();
    let mut w: AVec<u64, ProverAlloc> = AVec::with_capacity_in(N, ProverAlloc);
    w.resize(N, 0x1234);
    let p2 = w.as_ptr() as usize;
    end_phase();

    assert_eq!(
        p1, p2,
        "phase reset should recycle the slab — ProverAlloc must hit the arena"
    );
    assert!(
        canary.iter().all(|&b| b == 0xAB),
        "a system allocation was corrupted by the arena reset"
    );

    // Outside any phase, ProverAlloc transparently uses the system allocator (no panic).
    let mut off: AVec<u64, ProverAlloc> = AVec::new_in(ProverAlloc);
    off.extend(0..1000);
    assert_eq!(off.iter().sum::<u64>(), (0..1000).sum());

    drop(v);
    drop(w);
}
