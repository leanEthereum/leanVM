//! End-to-end proof verification across arena phase resets.
//!
//! This has its own binary because arena phases are process-global and cannot nest.

use primitives::bench::Plan;

#[test]
fn repeated_proofs_survive_phase_resets() {
    lean_vm::init_prover();
    assert!(
        zk_alloc::is_enabled(),
        "this test is meaningless unless the arena is engaged"
    );

    rec_aggregation::run_aggregation(3, 1, 1, lean_vm::pcs::TEST_LOG_INV_RATE, Plan::new(2, 0));

    let stats = zk_alloc::stats();
    assert!(stats.phases >= 3, "expected one phase per proof, got {stats:?}");
    assert!(
        stats.peak_bytes > 0,
        "no buffer reached the arena, so nothing was actually exercised: {stats:?}"
    );
    assert_eq!(
        stats.overflow, 0,
        "a slab overflowed into the system allocator, so SLAB_SIZE is undersized: {stats:?}"
    );
}
