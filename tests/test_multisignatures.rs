use std::time::Instant;

use lean_multisig::{
    MultiMessageAggregateSignature, SingleMessageAggregateSignature, aggregate_single_msg_signatures,
    merge_single_message_aggregates, setup_prover, split_multi_message_aggregate, verify_multi_message_aggregate,
    verify_single_message_aggregate,
};
use rand::{RngExt, SeedableRng, rngs::StdRng};
use rec_aggregation::{
    benchmark::{AggregationTopology, run_aggregation_benchmark},
    split_multi_message_aggregate_by_msg,
};
use xmss::{
    signers_cache::{BENCHMARK_SLOT, get_benchmark_signatures, message_for_benchmark},
    xmss_key_gen, xmss_sign, xmss_verify,
};

#[test]
fn test_xmss_signature() {
    let start_slot = 111;
    let end_slot = 200;
    let slot: u32 = 124;
    let mut rng: StdRng = StdRng::seed_from_u64(0);
    let msg = rng.random();

    let (secret_key, pub_key) = xmss_key_gen(rng.random(), start_slot, end_slot).unwrap();
    let signature = xmss_sign(&mut rng, &secret_key, &msg, slot).unwrap();
    xmss_verify(&pub_key, &msg, &signature, slot).unwrap();
}

#[test]
fn test_aggregation() {
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
    setup_prover();

    let log_inv_rate = 2; // [1, 2, 3 or 4] (lower = faster but bigger proofs)
    let message = message_for_benchmark();
    let slot: u32 = BENCHMARK_SLOT;
    let signatures = get_benchmark_signatures();

    let raws_a = signatures[0..3].to_vec();
    let single_message_a = aggregate_single_msg_signatures(&[], raws_a, message, slot, log_inv_rate).unwrap();

    let raws_b = signatures[3..5].to_vec();
    let single_message_b = aggregate_single_msg_signatures(&[], raws_b, message, slot, log_inv_rate).unwrap();

    let raws_c = signatures[5..6].to_vec();
    let final_sig = aggregate_single_msg_signatures(
        &[single_message_a, single_message_b],
        raws_c,
        message,
        slot,
        log_inv_rate,
    )
    .unwrap();

    let serialized_proof = final_sig.compress();
    println!("Serialized aggregated final: {} KiB", serialized_proof.len() / 1024);
    let recovered = SingleMessageAggregateSignature::decompress(&serialized_proof).unwrap();

    verify_single_message_aggregate(&recovered).unwrap();
}

#[test]
fn test_multi_message_aggregation() {
    setup_prover();

    let log_inv_rate = 2; // [1, 2, 3 or 4] (lower = faster but bigger proofs)
    let slot_a = BENCHMARK_SLOT;
    let message_a = message_for_benchmark();
    let signatures = get_benchmark_signatures();
    let raws_a = signatures[0..3].to_vec();

    let slot_b = BENCHMARK_SLOT + 1;
    let mut rng_b: StdRng = StdRng::seed_from_u64(17);
    let message_b: [_; 8] = std::array::from_fn(|_| rng_b.random());

    assert!(message_b != message_a && slot_b != slot_a);

    let raws_b: Vec<_> = (0..2)
        .map(|_| {
            let (sk, pk) = xmss_key_gen(rng_b.random(), slot_b, slot_b).unwrap();
            let sig = xmss_sign(&mut rng_b, &sk, &message_b, slot_b).unwrap();
            (pk, sig)
        })
        .collect();

    let single_message_a = aggregate_single_msg_signatures(&[], raws_a, message_a, slot_a, log_inv_rate).unwrap();
    let single_message_b = aggregate_single_msg_signatures(&[], raws_b, message_b, slot_b, log_inv_rate).unwrap();

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

    let compressed_multi_message = multi_message.compress();
    let multi_message = MultiMessageAggregateSignature::decompress(&compressed_multi_message).unwrap();
    verify_multi_message_aggregate(&multi_message).unwrap();

    let time = Instant::now();
    let split_a = split_multi_message_aggregate(multi_message.clone(), 0, log_inv_rate).unwrap();
    println!("split index 0: {:.2}s", time.elapsed().as_secs_f64());
    let time = Instant::now();
    let split_b = split_multi_message_aggregate_by_msg(multi_message, message_b, log_inv_rate).unwrap();
    println!("split index 1: {:.2}s", time.elapsed().as_secs_f64());
    assert_eq!(
        (split_a.info.message, &split_a.info.slot, &split_a.info.pubkeys),
        (info_a.message, &info_a.slot, &info_a.pubkeys)
    );
    assert_eq!(
        (split_b.info.message, &split_b.info.slot, &split_b.info.pubkeys),
        (info_b.message, &info_b.slot, &info_b.pubkeys)
    );
    verify_single_message_aggregate(&split_a).expect("split index 0 failed verify_single_message_aggregate");
    verify_single_message_aggregate(&split_b).expect("split index 1 failed verify_single_message_aggregate");
}
