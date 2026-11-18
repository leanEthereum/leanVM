use lean_pq_comparison::{
    deterministic_key_material, lean_fixture_signer, lean_fixture_signers, lean_full_key_seed,
    BlsFixtureSet, FixtureSet, FIXTURE_FIRST_LEAF, FIXTURE_LAST_LEAF, MAX_SIGNERS,
    MIXED_CLAIM_COUNTS, MIXED_CLAIM_SIGNATURES,
};

#[test]
fn fixtures_have_the_requested_unique_signers() {
    let fixtures = FixtureSet::same_claim(3).unwrap();

    assert_eq!(fixtures.len(), 3);
    assert_eq!(fixtures.lean_public_keys().len(), 3);
    assert_eq!(fixtures.bls_public_keys().len(), 3);
    assert_ne!(
        fixtures.lean_public_keys()[0],
        fixtures.lean_public_keys()[1]
    );
    assert_ne!(
        fixtures.bls_public_keys()[0].serialize(),
        fixtures.bls_public_keys()[1].serialize()
    );
}

#[test]
fn bls_only_same_claim_fixtures_scale_to_512_signers() {
    let fixtures = BlsFixtureSet::same_claim(MAX_SIGNERS).unwrap();

    assert_eq!(fixtures.len(), MAX_SIGNERS);
    assert_eq!(fixtures.messages().len(), MAX_SIGNERS);
    assert_eq!(fixtures.keys().len(), MAX_SIGNERS);
    assert_eq!(fixtures.signatures().len(), MAX_SIGNERS);
    assert_eq!(fixtures.public_keys().len(), MAX_SIGNERS);
    assert!(fixtures.verify_same_claim_aggregate(&fixtures.aggregate()));
}

#[test]
fn bls_only_distinct_claim_fixtures_use_and_verify_distinct_messages() {
    let fixtures = BlsFixtureSet::distinct_claims(3).unwrap();
    let aggregate = fixtures.aggregate();

    assert_ne!(fixtures.messages()[0], fixtures.messages()[1]);
    assert!(fixtures.verify_distinct_claim_aggregate(&aggregate));
}

#[test]
fn bls_only_fixtures_expose_borrowed_signature_sets() {
    let fixtures = BlsFixtureSet::distinct_claims(3).unwrap();
    let signature_sets = fixtures.signature_sets();

    assert_eq!(signature_sets.len(), fixtures.len());
    assert!(lighthouse_bls::verify_signature_sets(signature_sets.iter()));
}

#[test]
#[ignore = "validates 512 XMSS fixtures and is intentionally slow"]
fn same_claim_fixtures_support_the_expanded_signer_limit() {
    let fixtures = FixtureSet::same_claim(MAX_SIGNERS).unwrap();

    assert_eq!(fixtures.lean_messages().len(), MAX_SIGNERS);
    assert_eq!(fixtures.lean_signatures().len(), MAX_SIGNERS);
    assert_eq!(fixtures.lean_public_keys().len(), MAX_SIGNERS);
    assert_eq!(fixtures.bls_messages().len(), MAX_SIGNERS);
    assert_eq!(fixtures.bls_keys().len(), MAX_SIGNERS);
    assert_eq!(fixtures.bls_signatures().len(), MAX_SIGNERS);
    assert_eq!(fixtures.bls_public_keys().len(), MAX_SIGNERS);
}

#[test]
fn distinct_fixtures_use_distinct_messages_and_leaf_indices() {
    let fixtures = FixtureSet::distinct_claims(3).unwrap();

    assert_eq!(fixtures.lean_signatures()[0].leaf_index(), 0);
    assert_eq!(fixtures.lean_signatures()[1].leaf_index(), 1);
    assert_ne!(fixtures.lean_messages()[0], fixtures.lean_messages()[1]);
    assert_ne!(fixtures.bls_messages()[0], fixtures.bls_messages()[1]);
}

#[test]
fn fixture_inputs_and_expected_claims_match_every_signer() {
    let fixtures = FixtureSet::mixed_claims(4, 2).unwrap();
    let inputs = fixtures.lean_inputs();
    let expected = fixtures.lean_expected_claims();

    assert_eq!(inputs.len(), 4);
    assert!(expected.windows(2).all(|pair| pair[0] < pair[1]));
    for (index, (public_key, message, signature)) in inputs.iter().enumerate() {
        assert_eq!(*public_key, fixtures.lean_public_keys()[index]);
        assert_eq!(*message, fixtures.lean_messages()[index]);
        assert_eq!(*signature, fixtures.lean_signatures()[index]);
        assert!(expected.contains(&(*public_key, *message)));
    }
}

#[test]
fn mixed_claim_fixtures_distribute_signers_evenly() {
    let fixtures = FixtureSet::mixed_claims(8, 2).unwrap();

    assert_eq!(fixtures.claim_count(), 2);
    assert_eq!(signers_per_message(&fixtures), [4, 4]);
    assert_eq!(fixtures.lean_messages()[0], fixtures.lean_messages()[2]);
    assert_ne!(fixtures.lean_messages()[0], fixtures.lean_messages()[1]);
    assert_eq!(fixtures.bls_messages()[0], fixtures.bls_messages()[2]);
    assert_ne!(fixtures.bls_messages()[0], fixtures.bls_messages()[1]);

    let bls_aggregate = fixtures.bls_aggregate();
    assert!(fixtures
        .verify_bls_grouped_claim_aggregate(&bls_aggregate)
        .unwrap());
}

#[test]
fn mixed_claim_fixtures_validate_the_requested_shape() {
    assert!(FixtureSet::mixed_claims(8, 0).is_err());
    assert!(FixtureSet::mixed_claims(8, 3).is_err());
    assert!(FixtureSet::mixed_claims(8, 9).is_err());
    assert!(FixtureSet::mixed_claims(MAX_SIGNERS + 1, 1).is_err());
    assert_eq!(MIXED_CLAIM_COUNTS, [8, 16]);
    assert_eq!(MIXED_CLAIM_SIGNATURES / MIXED_CLAIM_COUNTS[0], 64);
    assert_eq!(MIXED_CLAIM_SIGNATURES / MIXED_CLAIM_COUNTS[1], 32);
}

#[test]
#[ignore = "validates and groups two 512-signature XMSS fixtures and is intentionally slow"]
fn configured_mixed_claim_fixtures_have_even_signer_groups() {
    for claim_count in MIXED_CLAIM_COUNTS {
        let fixtures = FixtureSet::mixed_claims(MIXED_CLAIM_SIGNATURES, claim_count).unwrap();
        let groups = signers_per_message(&fixtures);

        assert_eq!(groups.len(), claim_count);
        assert!(groups
            .iter()
            .all(|signers| *signers == MIXED_CLAIM_SIGNATURES / claim_count));
    }
}

#[test]
fn fixture_signers_are_deterministic_real_signatures_in_the_fixture_range() {
    let (public_key, message, signature) = lean_fixture_signer(0, 1).unwrap();

    assert_eq!(
        lean_fixture_signer(0, 1).unwrap(),
        (public_key, message, signature.clone())
    );
    assert_eq!(message, deterministic_key_material(1).unwrap());
    assert!((FIXTURE_FIRST_LEAF..=FIXTURE_LAST_LEAF).contains(&signature.leaf_index()));
    public_key.verify(&message, &signature).unwrap();
}

#[test]
fn parallel_fixture_signers_match_sequential_ones_in_order() {
    let signers = lean_fixture_signers(3..6, |index| index % 2).unwrap();
    let sequential = (3..6)
        .map(|index| lean_fixture_signer(index, index % 2).unwrap())
        .collect::<Vec<_>>();

    assert_eq!(signers, sequential);
    assert!(lean_fixture_signers(0..0, |_| 0).unwrap().is_empty());
}

#[test]
fn fixture_signer_seeds_bind_one_message_and_avoid_full_keys() {
    let (first_message_key, _, _) = lean_fixture_signer(0, 0).unwrap();
    let (second_message_key, _, _) = lean_fixture_signer(0, 1).unwrap();
    let full_key = lean_pq::xmss::SecretKey::from_seed(lean_full_key_seed(0).unwrap());

    assert_ne!(first_message_key, second_message_key);
    assert_ne!(first_message_key, full_key.public_key());
    assert_ne!(
        lean_full_key_seed(0).unwrap(),
        lean_full_key_seed(1).unwrap()
    );
    assert_ne!(
        lean_full_key_seed(0).unwrap(),
        deterministic_key_material(0).unwrap()
    );
}

#[test]
fn fixtures_reject_empty_and_excessive_counts() {
    assert!(BlsFixtureSet::same_claim(0).is_err());
    assert!(BlsFixtureSet::distinct_claims(0).is_err());
    assert!(FixtureSet::same_claim(0).is_err());
    assert!(FixtureSet::distinct_claims(0).is_err());
    assert!(FixtureSet::distinct_claims(MAX_SIGNERS + 1).is_err());
}

#[test]
fn every_raw_fixture_is_valid_before_benchmarking() {
    FixtureSet::same_claim(3).unwrap().validate_raw().unwrap();
    FixtureSet::distinct_claims(3)
        .unwrap()
        .validate_raw()
        .unwrap();
}

#[test]
fn deterministic_key_material_is_stable_unique_and_nonzero() {
    let first = deterministic_key_material(0).unwrap();
    let second = deterministic_key_material(1).unwrap();

    assert_eq!(first, deterministic_key_material(0).unwrap());
    assert_ne!(first, second);
    assert_ne!(first, [0; 32]);
    lighthouse_bls::SecretKey::deserialize(&first).unwrap();
}

#[test]
fn same_claim_bls_aggregate_verifies_for_exact_fixture_context() {
    let fixtures = FixtureSet::same_claim(3).unwrap();
    let aggregate = fixtures.bls_aggregate();

    assert!(fixtures.verify_bls_same_claim_aggregate(&aggregate));

    let wrong = FixtureSet::same_claim(2).unwrap();
    assert!(!wrong.verify_bls_same_claim_aggregate(&aggregate));
}

#[test]
fn distinct_claim_bls_aggregate_verifies_for_exact_fixture_context() {
    let fixtures = FixtureSet::distinct_claims(3).unwrap();
    let aggregate = fixtures.bls_aggregate();

    assert!(fixtures.verify_bls_distinct_claim_aggregate(&aggregate));

    let wrong = FixtureSet::distinct_claims(2).unwrap();
    assert!(!wrong.verify_bls_distinct_claim_aggregate(&aggregate));
}

#[test]
fn borrowed_signature_sets_verify_as_a_batch() {
    let fixtures = FixtureSet::distinct_claims(3).unwrap();
    let signature_sets = fixtures.bls_signature_sets();

    assert_eq!(signature_sets.len(), fixtures.len());
    assert!(lighthouse_bls::verify_signature_sets(signature_sets.iter()));
}

fn signers_per_message(fixtures: &FixtureSet) -> Vec<usize> {
    let mut counts = std::collections::BTreeMap::new();
    for message in fixtures.lean_messages() {
        *counts.entry(*message).or_insert(0) += 1;
    }
    counts.into_values().collect()
}
