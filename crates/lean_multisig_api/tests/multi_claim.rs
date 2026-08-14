use lean_multisig_api::{
    Claim, ClaimSigners, Error, MAX_CLAIMS, MultiClaimProof, SecretKey, aggregate, merge_claims, setup,
    verified_claims, verify_claims,
};
use std::sync::OnceLock;

const ATTESTATION: Claim = Claim::new([0xa1; 32], 100);
const PROPOSAL: Claim = Claim::new([0xb2; 32], 101);

struct Fixture {
    proof: MultiClaimProof,
    expected: Vec<ClaimSigners>,
}

fn fixture() -> &'static Fixture {
    static FIXTURE: OnceLock<Fixture> = OnceLock::new();
    FIXTURE.get_or_init(|| {
        setup();
        let alice = SecretKey::from_seed([1; 32], 100..=115).unwrap();
        let bob = SecretKey::from_seed([2; 32], 100..=115).unwrap();
        let proposer = SecretKey::from_seed([3; 32], 100..=115).unwrap();
        let attestation_child = aggregate(vec![alice.sign(&ATTESTATION).unwrap()], &ATTESTATION).unwrap();
        let proof = merge_claims(vec![
            proposer.sign(&PROPOSAL).unwrap(),
            bob.sign(&ATTESTATION).unwrap(),
            attestation_child,
        ])
        .unwrap();
        let expected = vec![
            ClaimSigners {
                claim: ATTESTATION,
                signers: vec![alice.public_key(), bob.public_key()],
            },
            ClaimSigners {
                claim: PROPOSAL,
                signers: vec![proposer.public_key()],
            },
        ];
        Fixture { proof, expected }
    })
}

#[test]
fn mixed_signatures_are_grouped_by_claim_and_verified_as_one_bundle() {
    let Fixture { proof, expected } = fixture();

    verify_claims(proof, expected).unwrap();
    let proved = verified_claims(proof).unwrap();
    assert_eq!(proved.len(), 2);
    assert!(
        proved
            .iter()
            .any(|group| group.claim == ATTESTATION && group.signers.len() == 2)
    );
    assert!(
        proved
            .iter()
            .any(|group| group.claim == PROPOSAL && group.signers.len() == 1)
    );
}

#[test]
fn self_contained_bundle_round_trips_without_external_claim_context() {
    let Fixture { proof, expected } = fixture();

    let restored = MultiClaimProof::from_bytes(&proof.to_bytes()).unwrap();

    verify_claims(&restored, expected).unwrap();
}

#[test]
fn authorization_rejects_a_wrong_claim_signer_mapping() {
    let Fixture { proof, expected } = fixture();
    let mut wrong = expected.clone();
    wrong[0].signers.pop();

    assert!(matches!(verify_claims(proof, &wrong), Err(Error::ClaimSetMismatch)));
}

#[test]
fn authorization_is_order_independent_but_rejects_repeated_claim_groups() {
    let Fixture { proof, expected } = fixture();
    let mut reordered = expected.clone();
    reordered.reverse();
    reordered[1].signers.reverse();
    let duplicate = reordered[1].signers[0];
    reordered[1].signers.push(duplicate);
    verify_claims(proof, &reordered).unwrap();

    let mut repeated = expected.clone();
    repeated.push(expected[0].clone());
    assert!(matches!(verify_claims(proof, &repeated), Err(Error::ClaimSetMismatch)));
}

#[test]
fn malformed_multi_claim_envelopes_are_rejected() {
    assert!(matches!(
        MultiClaimProof::from_bytes(b"not a multi-claim proof"),
        Err(Error::MalformedMultiClaimProof)
    ));
    assert!(matches!(
        MultiClaimProof::from_bytes(b"LMCM\x01"),
        Err(Error::MalformedMultiClaimProof)
    ));
}

#[test]
fn decoding_is_structural_and_verification_rejects_a_tampered_bundle() {
    let mut bytes = fixture().proof.to_bytes();
    *bytes.last_mut().unwrap() ^= 1;

    match MultiClaimProof::from_bytes(&bytes) {
        Err(Error::MalformedMultiClaimProof) => {}
        Ok(proof) => assert!(verified_claims(&proof).is_err()),
        Err(other) => panic!("unexpected error: {other:?}"),
    }
}

#[test]
fn merging_no_signatures_is_rejected_before_proving() {
    assert!(matches!(merge_claims(Vec::new()), Err(Error::Empty)));
}

#[test]
fn a_proposer_only_bundle_can_contain_one_claim() {
    setup();
    let claim = Claim::new([0xc3; 32], 200);
    let proposer = SecretKey::from_seed([4; 32], 200..=215).unwrap();
    let proof = merge_claims(vec![proposer.sign(&claim).unwrap()]).unwrap();

    verify_claims(
        &proof,
        &[ClaimSigners {
            claim,
            signers: vec![proposer.public_key()],
        }],
    )
    .unwrap();
}

#[test]
fn too_many_distinct_claims_are_rejected_before_proving() {
    let key = SecretKey::from_seed([9; 32], 0..=u32::try_from(MAX_CLAIMS).unwrap()).unwrap();
    let signatures = (0..=u32::try_from(MAX_CLAIMS).unwrap())
        .map(|slot| key.sign(&Claim::new([u8::try_from(slot).unwrap(); 32], slot)).unwrap())
        .collect();

    assert!(matches!(
        merge_claims(signatures),
        Err(Error::TooManyClaims { got, max }) if got == MAX_CLAIMS + 1 && max == MAX_CLAIMS
    ));
}
