use lean_multisig::{
    ZkAllocator, aggregate_single_msg_signatures, begin_phase, end_phase, setup_prover, verify_single_message_aggregate,
};
use xmss::signers_cache::{BENCHMARK_SLOT, get_benchmark_signatures, message_for_benchmark};

#[global_allocator]
static ALLOC: ZkAllocator = ZkAllocator;

// Exercise the full multi-phase arena lifecycle and verify every proof. Each `begin_phase`
// resets the slabs, overwriting the previous phase's arena memory — so if any persistent
// state (thread pool, compiled bytecode, twiddles, static caches) had leaked into the arena
// instead of the system allocator, a later phase's proof would be built on corrupted data and
// fail to verify. `setup_prover()` (called before the first phase) settles that state in the
// system allocator up front; this test guards that contract across several phases.
#[test]
#[allow(clippy::redundant_clone)]
fn test_aggregation_with_zk_alloc() {
    setup_prover();

    let log_inv_rate = 2;
    let slot: u32 = BENCHMARK_SLOT;
    let signatures = get_benchmark_signatures();
    let raw_xmss = signatures[0..6].to_vec();

    for _ in 0..3 {
        begin_phase();
        let aggregated =
            aggregate_single_msg_signatures(&[], raw_xmss.clone(), message_for_benchmark(), slot, log_inv_rate)
                .unwrap();
        end_phase();
        // IMPORTANT: clone to move the data out of the arena memory before the next reset.
        let aggregated = aggregated.clone();
        verify_single_message_aggregate(&aggregated).unwrap();
    }
}
