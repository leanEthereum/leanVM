use lean_multisig::{AggregatedXMSS, setup_prover, xmss_aggregate, xmss_verify_aggregation};
use leansig_wrapper::{xmss_keygen_fast, xmss_sign_fast, xmss_verify};
use rand::{SeedableRng, rngs::StdRng};
use rec_aggregation::benchmark::{AggregationTopology, run_aggregation_benchmark};
use rec_aggregation::signatures_cache::{BENCHMARK_SLOT, get_benchmark_signatures, message_for_benchmark};

#[test]
fn test_xmss_signature() {
    let activation_epoch = 111;
    let num_active_epochs = 39;
    let slot: u32 = 124;
    let mut rng: StdRng = StdRng::seed_from_u64(0);
    let msg = [42u8; leansig_wrapper::MESSAGE_LENGTH];

    let (secret_key, pub_key) = xmss_keygen_fast(&mut rng, activation_epoch, num_active_epochs);
    let signature = xmss_sign_fast(&secret_key, &msg, slot).unwrap();
    xmss_verify(&pub_key, slot, &msg, &signature).unwrap();
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
fn test_xmss_aggregate() {
    setup_prover();

    let log_inv_rate = 2; // [1, 2, 3 or 4] (lower = faster but bigger proofs)
    let message = message_for_benchmark();
    let slot: u32 = BENCHMARK_SLOT;
    let signatures = get_benchmark_signatures();

    let raws_a = signatures[0..3].to_vec();
    let (_, type1_a) = xmss_aggregate(&[], raws_a, &message, slot, log_inv_rate).unwrap();

    let raws_b = signatures[3..5].to_vec();
    let (_, type1_b) = xmss_aggregate(&[], raws_b, &message, slot, log_inv_rate).unwrap();

    let raws_c = signatures[5..6].to_vec();
    let pks_a = type1_a.info.pubkeys.clone();
    let pks_b = type1_b.info.pubkeys.clone();
    let (_, final_sig) = xmss_aggregate(
        &[(&pks_a, type1_a), (&pks_b, type1_b)],
        raws_c,
        &message,
        slot,
        log_inv_rate,
    )
    .unwrap();

    let serialized_proof = final_sig.compress();
    println!("Serialized aggregated final: {} KiB", serialized_proof.len() / 1024);
    let recovered = AggregatedXMSS::decompress(&serialized_proof).unwrap();

    xmss_verify_aggregation(recovered.info.pubkeys.clone(), &recovered, &message, slot).unwrap();
}

#[test]
fn test_type1_compression() {
    setup_prover();

    let log_inv_rate = 2;
    let message = message_for_benchmark();
    let slot = BENCHMARK_SLOT;
    let signatures = get_benchmark_signatures();

    // The pubkey set is shared between prover and verifier.
    let raws_a = signatures[..3].to_vec();
    let shared_pubkeys_a = raws_a.iter().map(|(pk, _)| pk.clone()).collect::<Vec<_>>();
    let (_, type1_a) = xmss_aggregate(&[], raws_a, &message, slot, log_inv_rate).unwrap();

    let type1_a_compressed_compact = type1_a.compress_without_pubkeys();
    let type1_a_compact_recovered =
        AggregatedXMSS::decompress_without_pubkeys(&type1_a_compressed_compact, shared_pubkeys_a)
            .expect("type-1 round-trip");
    xmss_verify_aggregation(
        type1_a_compact_recovered.info.pubkeys.clone(),
        &type1_a_compact_recovered,
        &message,
        slot,
    )
    .expect("recovered type-1 must verify");
    assert_eq!(type1_a_compact_recovered.info.pubkeys, type1_a.info.pubkeys);

    let type1_a_compressed_full = type1_a.compress();
    let type1_a_full_recovered = AggregatedXMSS::decompress(&type1_a_compressed_full).expect("type-1 round-trip");
    xmss_verify_aggregation(
        type1_a_full_recovered.info.pubkeys.clone(),
        &type1_a_full_recovered,
        &message,
        slot,
    )
    .expect("recovered type-1 must verify");
    assert_eq!(type1_a_full_recovered.info.pubkeys, type1_a.info.pubkeys);

    assert!(type1_a_compressed_compact.len() < type1_a_compressed_full.len());
}
