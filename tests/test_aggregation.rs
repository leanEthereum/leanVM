use lean_multisig::{aggregate_single_msg_signatures, setup_prover, verify_single_message_aggregate};
use xmss::signers_cache::{BENCHMARK_SLOT, get_benchmark_signatures, message_for_benchmark};

// End-to-end prove+verify under the system allocator (no arena phases). Repeated to catch
// any cross-run state corruption. `test_zk_alloc.rs` is the matching arena-allocator run.
#[test]
fn test_aggregation_prove_verify() {
    setup_prover();

    let log_inv_rate = 2;
    let message = message_for_benchmark();
    let slot: u32 = BENCHMARK_SLOT;
    let signatures = get_benchmark_signatures();
    let raw_xmss = signatures[0..6].to_vec();

    for _ in 0..2 {
        let aggregated = aggregate_single_msg_signatures(&[], raw_xmss.clone(), message, slot, log_inv_rate).unwrap();
        verify_single_message_aggregate(&aggregated).unwrap();
    }
}
