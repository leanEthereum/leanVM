use lean_multisig::{aggregate_type_1, setup_prover, verify_type_1};
use xmss::signers_cache::{BENCHMARK_SLOT, get_benchmark_signatures, message_for_benchmark};

// End-to-end prove+verify under the default (mimalloc) allocator. Repeated to catch any
// cross-run state corruption. (Replaces the former `test_zk_alloc` arena regression test;
// the bump arena and its phase ceremony were removed in favor of a robust allocator.)
#[test]
fn test_aggregation_prove_verify() {
    setup_prover();

    let log_inv_rate = 2;
    let message = message_for_benchmark();
    let slot: u32 = BENCHMARK_SLOT;
    let signatures = get_benchmark_signatures();
    let raw_xmss = signatures[0..6].to_vec();

    for _ in 0..2 {
        let aggregated = aggregate_type_1(&[], raw_xmss.clone(), message, slot, log_inv_rate).unwrap();
        verify_type_1(&aggregated).unwrap();
    }
}
