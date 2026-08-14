use lean_multisig_api::{
    Claim, ClaimSigners, MultiClaimSignature, PublicKey, SecretKey, Signature, aggregate, merge_claims,
    verified_signers, verify, verify_claims,
};
use std::collections::BTreeSet;
use std::sync::Barrier;

#[test]
fn signatures_and_aggregates_share_one_opaque_api() {
    let claim = Claim::new([42u8; 32], 100);
    let alice = SecretKey::from_seed([1u8; 32], 100..=115).unwrap();
    let bob = SecretKey::from_seed([2u8; 32], 100..=115).unwrap();

    let alice_signature = alice.sign(&claim).unwrap();
    let bob_signature = bob.sign(&claim).unwrap();

    let alice_signature = Signature::from_bytes(&alice_signature.to_bytes()).unwrap();
    let aggregate = aggregate(vec![alice_signature, bob_signature], &claim).unwrap();
    let aggregate = Signature::from_bytes(&aggregate.to_bytes()).unwrap();

    let _: [u8; 32] = alice.public_key();
    let expected: Vec<PublicKey> = vec![alice.public_key(), bob.public_key()];
    verify(&aggregate, &expected, &claim).unwrap();

    assert_eq!(
        verified_signers(&aggregate, &claim)
            .unwrap()
            .into_iter()
            .collect::<BTreeSet<_>>(),
        expected.into_iter().collect()
    );
}

#[test]
fn multiple_claims_share_one_self_contained_signature() {
    let attestation = Claim::new([0xa1; 32], 100);
    let proposal = Claim::new([0xb2; 32], 101);
    let alice = SecretKey::from_seed([1; 32], 100..=115).unwrap();
    let bob = SecretKey::from_seed([2; 32], 100..=115).unwrap();
    let proposer = SecretKey::from_seed([3; 32], 100..=115).unwrap();

    let signature = merge_claims(vec![
        alice.sign(&attestation).unwrap(),
        bob.sign(&attestation).unwrap(),
        proposer.sign(&proposal).unwrap(),
    ])
    .unwrap();
    let signature = MultiClaimSignature::from_bytes(&signature.to_bytes()).unwrap();

    verify_claims(
        &signature,
        &[
            ClaimSigners {
                claim: attestation,
                signers: vec![alice.public_key(), bob.public_key()],
            },
            ClaimSigners {
                claim: proposal,
                signers: vec![proposer.public_key()],
            },
        ],
    )
    .unwrap();
}

#[test]
fn a_single_claim_aggregate_can_be_merged_with_another_claim() {
    let attestation = Claim::new([0xc1; 32], 100);
    let proposal = Claim::new([0xd2; 32], 101);
    let alice = SecretKey::from_seed([4; 32], 100..=115).unwrap();
    let bob = SecretKey::from_seed([5; 32], 100..=115).unwrap();
    let proposer = SecretKey::from_seed([6; 32], 100..=115).unwrap();

    let attestation_signature = aggregate(
        vec![alice.sign(&attestation).unwrap(), bob.sign(&attestation).unwrap()],
        &attestation,
    )
    .unwrap();
    let signature = merge_claims(vec![attestation_signature, proposer.sign(&proposal).unwrap()]).unwrap();
    let signature = MultiClaimSignature::from_bytes(&signature.to_bytes()).unwrap();

    verify_claims(
        &signature,
        &[
            ClaimSigners {
                claim: attestation,
                signers: vec![alice.public_key(), bob.public_key()],
            },
            ClaimSigners {
                claim: proposal,
                signers: vec![proposer.public_key()],
            },
        ],
    )
    .unwrap();
}

#[test]
fn concurrent_proving_without_the_arena_does_not_panic() {
    const THREADS: usize = 2;
    let barrier = Barrier::new(THREADS);

    std::thread::scope(|scope| {
        let handles = (0..THREADS)
            .map(|index| {
                let barrier = &barrier;
                scope.spawn(move || {
                    let byte = u8::try_from(index + 10).unwrap();
                    let slot = u32::try_from(index + 200).unwrap();
                    let claim = Claim::new([byte; 32], slot);
                    let key = SecretKey::from_seed([byte; 32], slot..=slot).unwrap();
                    let signature = key.sign(&claim).unwrap();

                    barrier.wait();
                    aggregate(vec![signature], &claim).unwrap()
                })
            })
            .collect::<Vec<_>>();

        for handle in handles {
            handle.join().unwrap();
        }
    });
}
