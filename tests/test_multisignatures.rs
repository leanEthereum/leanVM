use std::sync::{Mutex, MutexGuard};
use std::time::Instant;

use lean_multisig::{
    MultiMessageAggregateSignature, SingleMessageAggregateSignature, aggregate_single_message_signatures,
    merge_single_message_aggregates, setup_prover, split_multi_message_aggregate, verify_multi_message_aggregate,
    verify_single_message_aggregate,
};
use rand::{RngExt, SeedableRng, rngs::StdRng};
use rec_aggregation::{
    benchmark::{AggregationTopology, run_aggregation_benchmark},
    split_multi_message_aggregate_by_message,
};
use xmss::{
    signers_cache::{BENCHMARK_SLOT, get_benchmark_signatures, message_for_benchmark},
    xmss_key_gen, xmss_sign, xmss_verify,
};

static ARENA_TEST_LOCK: Mutex<()> = Mutex::new(());

fn serialize_arena_tests() -> MutexGuard<'static, ()> {
    ARENA_TEST_LOCK.lock().unwrap()
}

#[test]
fn forbid_parallelism_is_active_in_tests() {
    let _forbid = parallel::forbid_parallelism();
    assert!(parallel::parallelism_forbidden());
}

#[test]
fn test_xmss_signature() {
    let activation_slot = 111;
    let num_active_slots = 90;
    let slot: u32 = 124;
    let mut rng: StdRng = StdRng::seed_from_u64(0);
    let message: [u8; 32] = rng.random();

    let (pub_key, secret_key) = xmss_key_gen(&mut rng, activation_slot, num_active_slots).unwrap();
    let signature = xmss_sign(&secret_key, slot, &message).unwrap();
    xmss_verify(&pub_key, slot, &message, &signature).unwrap();
}

#[test]
fn test_aggregation() {
    let _arena_guard = serialize_arena_tests();
    for n_signatures in [1, 2, 4, 8, 16, 32, 64, 128] {
        let topology = AggregationTopology {
            raw_xmss: n_signatures,
            children: vec![],
            log_inv_rate: 1,
            overlap: 0,
        };
        run_aggregation_benchmark(&topology, false, true, 1);
    }
}

#[test]
fn test_single_message_aggregation() {
    let _arena_guard = serialize_arena_tests();
    setup_prover();

    let log_inv_rate = 2; // [1, 2, 3 or 4] (lower = faster but bigger proofs)
    let message = message_for_benchmark();
    let slot: u32 = BENCHMARK_SLOT;
    let signatures = get_benchmark_signatures();

    let raws_a = signatures[0..3].to_vec();
    let single_message_a = aggregate_single_message_signatures(&[], raws_a, message, slot, log_inv_rate).unwrap();

    let raws_b = signatures[3..5].to_vec();
    let single_message_b = aggregate_single_message_signatures(&[], raws_b, message, slot, log_inv_rate).unwrap();

    let raws_c = signatures[5..6].to_vec();
    let final_sig = aggregate_single_message_signatures(
        &[single_message_a, single_message_b],
        raws_c,
        message,
        slot,
        log_inv_rate,
    )
    .unwrap();

    let serialized_proof = final_sig.to_bytes();
    println!("Serialized aggregated final: {} KiB", serialized_proof.len() / 1024);
    let recovered = SingleMessageAggregateSignature::from_bytes(&serialized_proof).unwrap();

    verify_single_message_aggregate(&recovered).unwrap();

    // Without-pubkeys serialization: smaller, and recoverable given the signer set.
    let without_pubkeys = final_sig.to_bytes_without_pubkeys();
    assert!(without_pubkeys.len() < serialized_proof.len());
    let reattached =
        SingleMessageAggregateSignature::from_bytes_without_pubkeys(&without_pubkeys, final_sig.info.pubkeys.clone())
            .unwrap();
    verify_single_message_aggregate(&reattached).unwrap();

    // A wrong signer set makes verification fail.
    let wrong_set =
        SingleMessageAggregateSignature::from_bytes_without_pubkeys(&without_pubkeys, vec![signatures[7].0.clone()])
            .unwrap();
    assert!(verify_single_message_aggregate(&wrong_set).is_err());

    // Context-free serialization relies on the outer protocol container for all semantics.
    let without_context = final_sig.to_bytes_without_context();
    let reattached = SingleMessageAggregateSignature::from_bytes_without_context(
        &without_context,
        message,
        slot,
        final_sig.info.pubkeys.clone(),
    )
    .unwrap();
    verify_single_message_aggregate(&reattached).unwrap();
    let wrong_context = SingleMessageAggregateSignature::from_bytes_without_context(
        &without_context,
        [0xff; xmss::MESSAGE_LEN_BYTES],
        slot,
        final_sig.info.pubkeys,
    )
    .unwrap();
    assert!(verify_single_message_aggregate(&wrong_context).is_err());
}

#[test]
fn test_multi_message_aggregation() {
    let _arena_guard = serialize_arena_tests();
    setup_prover();

    let log_inv_rate = 2; // [1, 2, 3 or 4] (lower = faster but bigger proofs)
    let slot_a = BENCHMARK_SLOT;
    let message_a = message_for_benchmark();
    let signatures = get_benchmark_signatures();
    let raws_a = signatures[0..3].to_vec();

    let slot_b = BENCHMARK_SLOT + 1;
    let mut rng_b: StdRng = StdRng::seed_from_u64(17);
    let message_b: [u8; 32] = rng_b.random();

    assert!(message_b != message_a && slot_b != slot_a);

    let raws_b: Vec<_> = (0..2)
        .map(|_| {
            let (pk, sk) = xmss_key_gen(&mut rng_b, u64::from(slot_b), 1).unwrap();
            let sig = xmss_sign(&sk, slot_b, &message_b).unwrap();
            (pk, sig)
        })
        .collect();

    let single_message_a = aggregate_single_message_signatures(&[], raws_a, message_a, slot_a, log_inv_rate).unwrap();
    let single_message_b = aggregate_single_message_signatures(&[], raws_b, message_b, slot_b, log_inv_rate).unwrap();

    verify_single_message_aggregate(&single_message_a).unwrap();
    verify_single_message_aggregate(&single_message_b).unwrap();

    let info_a = single_message_a.info.clone();
    let info_b = single_message_b.info.clone();

    let time = Instant::now();
    let multi_message =
        merge_single_message_aggregates(vec![single_message_a, single_message_b], log_inv_rate).unwrap();
    println!("merge_single_message_aggregates: {:.2}s", time.elapsed().as_secs_f64());
    assert_eq!(multi_message.info.len(), 2);
    assert_eq!(multi_message.info[0], info_a);
    assert_eq!(multi_message.info[1], info_b);

    let serialized_multi_message = multi_message.to_bytes();
    let multi_message = MultiMessageAggregateSignature::from_bytes(&serialized_multi_message).unwrap();
    verify_multi_message_aggregate(&multi_message).unwrap();

    // Without-pubkeys serialization roundtrip.
    let without_pubkeys = multi_message.to_bytes_without_pubkeys();
    let pubkeys_per_info: Vec<_> = multi_message.info.iter().map(|i| i.pubkeys.clone()).collect();
    let reattached =
        MultiMessageAggregateSignature::from_bytes_without_pubkeys(&without_pubkeys, pubkeys_per_info).unwrap();
    verify_multi_message_aggregate(&reattached).unwrap();

    // Context-free serialization relies on one externally resolved context per component.
    let without_context = multi_message.to_bytes_without_context();
    let contexts = multi_message
        .info
        .iter()
        .map(|info| (info.core.message, info.core.slot, info.pubkeys.clone()))
        .collect();
    let reattached = MultiMessageAggregateSignature::from_bytes_without_context(&without_context, contexts).unwrap();
    verify_multi_message_aggregate(&reattached).unwrap();

    let time = Instant::now();
    let split_a = split_multi_message_aggregate(multi_message.clone(), 0, log_inv_rate).unwrap();
    println!("split index 0: {:.2}s", time.elapsed().as_secs_f64());
    let time = Instant::now();
    let split_b = split_multi_message_aggregate_by_message(multi_message, message_b, log_inv_rate).unwrap();
    println!("split index 1: {:.2}s", time.elapsed().as_secs_f64());
    assert_eq!(
        (
            split_a.info.core.message,
            &split_a.info.core.slot,
            &split_a.info.pubkeys
        ),
        (info_a.core.message, &info_a.core.slot, &info_a.pubkeys)
    );
    assert_eq!(
        (
            split_b.info.core.message,
            &split_b.info.core.slot,
            &split_b.info.pubkeys
        ),
        (info_b.core.message, &info_b.core.slot, &info_b.pubkeys)
    );
    verify_single_message_aggregate(&split_a).expect("split index 0 failed verify");
    verify_single_message_aggregate(&split_b).expect("split index 1 failed verify");
}
