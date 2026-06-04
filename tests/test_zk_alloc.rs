use lean_multisig::{
    aggregate_single_msg_signatures, begin_phase, enable_arena, end_phase, setup_prover,
    verify_single_message_aggregate,
};
use xmss::signers_cache::{BENCHMARK_SLOT, get_benchmark_signatures, message_for_benchmark};

// No `#[global_allocator]`: the process keeps the system allocator. The proving arena is driven
// purely by the explicit `ProverAlloc`-typed proof buffers, so the whole pipeline (witness,
// trace, MLEs, stacked PCS, WHIR codeword + Merkle leaf) lands in the arena without `ZkAllocator`
// dictating the global allocator.
#[test]
#[allow(clippy::redundant_clone)]
fn test_aggregation_without_global_allocator() {
    enable_arena();
    setup_prover();

    let log_inv_rate = 2;
    let message = message_for_benchmark();
    let slot: u32 = BENCHMARK_SLOT;
    let signatures = get_benchmark_signatures();
    let raw_xmss = signatures[0..6].to_vec();

    begin_phase();
    let aggregated = aggregate_single_msg_signatures(&[], raw_xmss, message, slot, log_inv_rate).unwrap();
    end_phase();
    // IMPORTANT: clone to move the data out of the arena memory
    let aggregated = aggregated.clone();

    verify_single_message_aggregate(&aggregated).unwrap();
}
