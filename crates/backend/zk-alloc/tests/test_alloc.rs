//! `ArenaVec` drives the arena explicitly, with the process keeping its **own** allocator (no
//! `#[global_allocator]` is installed here). Only `ArenaVec`-backed buffers touch the arena;
//! everything else is untouched by a phase reset — the property that lets a library use the
//! arena without forcing its allocator on consumers.

use zk_alloc::{ArenaVec, begin_phase, enable_arena, end_phase};

const N: usize = 4096;

#[test]
fn arena_vec_without_global_allocator() {
    // Opt into the arena: without this, begin_phase/end_phase are inert and ArenaVec would
    // transparently use the system allocator (no slab reuse to observe).
    enable_arena();

    // Phase 1: one arena allocation on this (main) thread → claims the slab at its base.
    begin_phase();
    let mut v: ArenaVec<u64> = ArenaVec::with_capacity(N);
    v.resize(N, 0xABCD); // fits the reservation: no realloc, pointer stays put
    let p1 = v.as_ptr() as usize;
    end_phase();

    // Arena is off: this lands in the system allocator and must survive the next reset.
    let canary = vec![0xAB_u8; 8192];

    // Phase 2: the slab is reset, so an identically-shaped buffer reuses the same address.
    begin_phase();
    let mut w: ArenaVec<u64> = ArenaVec::with_capacity(N);
    w.resize(N, 0x1234);
    let p2 = w.as_ptr() as usize;
    end_phase();

    assert_eq!(
        p1, p2,
        "phase reset should recycle the slab — ArenaVec must hit the arena"
    );
    assert!(
        canary.iter().all(|&b| b == 0xAB),
        "a system allocation was corrupted by the arena reset"
    );

    // Outside any phase, ArenaVec transparently uses the system allocator (no panic).
    let mut off: ArenaVec<u64> = ArenaVec::new();
    off.extend(0..1000);
    assert_eq!(off.iter().sum::<u64>(), (0..1000).sum());

    drop(v);
    drop(w);
}
