use lean_multisig_api::{Claim, PublicKey, SecretKey, Signature, aggregate, verified_signers, verify};
use std::collections::BTreeSet;

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
