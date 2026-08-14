//! End-to-end tests for the opaque signature boundary.
//!
//! The two ignored tests pin the planner's 1500-signature leaf boundary and are run explicitly
//! by CI. Run them locally with:
//!
//! ```text
//! cargo test --release -p lean_multisig_api --test round_trip -- --ignored
//! ```

use lean_multisig_api::{Claim, Error, PublicKey, SecretKey, Signature, aggregate, verified_signers, verify};
use ssz::Encode;
use std::collections::BTreeSet;
use std::sync::{Mutex, OnceLock};

const CLAIM: Claim = Claim::new([42u8; 32], 100);
static PROVE_LOCK: Mutex<()> = Mutex::new(());
static BASE: OnceLock<Signature> = OnceLock::new();

fn signers(n: u8) -> Vec<SecretKey> {
    (0..n)
        .map(|seed| SecretKey::from_seed([seed; 32], 100..=115).unwrap())
        .collect()
}

fn lone_key(seed: u8) -> SecretKey {
    assert!(seed >= 200);
    SecretKey::from_seed([seed; 32], 100..=115).unwrap()
}

fn prove(signatures: Vec<Signature>, claim: &Claim) -> Result<Signature, Error> {
    let _guard = PROVE_LOCK.lock().unwrap();
    aggregate(signatures, claim)
}

fn base() -> &'static Signature {
    BASE.get_or_init(|| {
        let signatures = signers(2).iter().map(|key| key.sign(&CLAIM).unwrap()).collect();
        prove(signatures, &CLAIM).unwrap()
    })
}

fn base_public_keys() -> Vec<PublicKey> {
    signers(2).iter().map(SecretKey::public_key).collect()
}

fn signer_set(signature: &Signature, claim: &Claim) -> BTreeSet<PublicKey> {
    verified_signers(signature, claim).unwrap().into_iter().collect()
}

#[test]
fn aggregate_round_trips_through_the_public_wire_format() {
    let aggregate = Signature::from_bytes(&base().to_bytes()).unwrap();
    let expected = base_public_keys();

    verify(&aggregate, &expected, &CLAIM).unwrap();
    assert_eq!(signer_set(&aggregate, &CLAIM), expected.into_iter().collect());
}

#[test]
fn verification_binds_the_claim_and_signer_set() {
    let wrong_claim = Claim::new([7u8; 32], CLAIM.slot());
    assert!(matches!(
        verify(base(), &base_public_keys(), &wrong_claim),
        Err(Error::MessageMismatch)
    ));

    let outsider = lone_key(200).public_key();
    assert!(matches!(
        verify(base(), &[base_public_keys()[0].clone(), outsider], &CLAIM),
        Err(Error::SignerSetMismatch)
    ));
}

#[test]
fn folding_an_aggregate_with_a_fresh_signature_hides_the_representation_split() {
    let fresh = lone_key(201);
    let combined = prove(vec![base().clone(), fresh.sign(&CLAIM).unwrap()], &CLAIM).unwrap();

    let mut expected: BTreeSet<PublicKey> = base_public_keys().into_iter().collect();
    expected.insert(fresh.public_key());
    assert_eq!(signer_set(&combined, &CLAIM), expected);
}

#[test]
fn duplicate_signers_collapse_to_one() {
    let keys = signers(2);
    let combined = prove(
        vec![
            keys[0].sign(&CLAIM).unwrap(),
            keys[0].sign(&CLAIM).unwrap(),
            keys[1].sign(&CLAIM).unwrap(),
        ],
        &CLAIM,
    )
    .unwrap();

    assert_eq!(signer_set(&combined, &CLAIM), base_public_keys().into_iter().collect());
}

#[test]
fn a_signer_shared_by_a_child_and_fresh_input_appears_once() {
    let keys = signers(2);
    let fresh = lone_key(202);
    let combined = prove(
        vec![
            base().clone(),
            keys[0].sign(&CLAIM).unwrap(),
            fresh.sign(&CLAIM).unwrap(),
        ],
        &CLAIM,
    )
    .unwrap();

    let mut expected: BTreeSet<PublicKey> = base_public_keys().into_iter().collect();
    expected.insert(fresh.public_key());
    assert_eq!(signer_set(&combined, &CLAIM), expected);
}

#[test]
fn mismatched_inputs_are_rejected_before_a_new_proof() {
    let other_claim = Claim::new([9u8; 32], CLAIM.slot());
    let key = lone_key(203);
    let other = prove(vec![key.sign(&other_claim).unwrap()], &other_claim).unwrap();

    assert!(matches!(
        prove(vec![other, key.sign(&CLAIM).unwrap()], &CLAIM),
        Err(Error::MessageMismatch)
    ));
}

#[test]
fn malformed_and_tampered_envelopes_are_rejected() {
    assert!(matches!(
        Signature::from_bytes(b"not a signature"),
        Err(Error::MalformedSignature)
    ));

    let mut bytes = base().to_bytes();
    *bytes.last_mut().unwrap() ^= 0xff;
    match Signature::from_bytes(&bytes) {
        Err(Error::MalformedSignature) => {}
        Ok(signature) => assert!(verified_signers(&signature, &CLAIM).is_err()),
        Err(other) => panic!("unexpected error: {other:?}"),
    }
}

#[test]
fn decoding_is_structural_and_verification_rejects_a_tampered_raw_signature() {
    let key = lone_key(204);
    let mut bytes = key.sign(&CLAIM).unwrap().to_bytes();
    *bytes.last_mut().unwrap() ^= 1;

    let signature = Signature::from_bytes(&bytes).expect("the tagged envelope is still structurally valid");
    assert!(matches!(
        verify(&signature, &[key.public_key()], &CLAIM),
        Err(Error::InvalidSignature { index: 0, .. })
    ));
}

#[test]
fn a_multi_level_tree_round_trips() {
    let keys = signers(17);
    let children = keys
        .iter()
        .map(|key| prove(vec![key.sign(&CLAIM).unwrap()], &CLAIM).unwrap())
        .collect();
    let root = prove(children, &CLAIM).unwrap();

    let expected = keys.iter().map(SecretKey::public_key).collect::<BTreeSet<_>>();
    assert_eq!(signer_set(&root, &CLAIM), expected);
}

const LEAF_TARGET: usize = 1500;

fn cached_batch(n: usize) -> (Vec<Signature>, Vec<PublicKey>, Claim) {
    let cached = xmss::signers_cache::get_benchmark_signatures();
    assert!(cached.len() >= n);
    let claim = Claim::new(
        xmss::signers_cache::message_for_benchmark(),
        xmss::signers_cache::BENCHMARK_SLOT,
    );
    let mut public_keys = Vec::with_capacity(n);
    let signatures = cached[..n]
        .iter()
        .map(|(public_key, signature)| {
            let public_key_bytes = public_key.as_ssz_bytes();
            public_keys.push(public_key_bytes.as_slice().try_into().unwrap());
            let mut bytes = b"LMSI\x01\x00".to_vec();
            bytes.extend_from_slice(claim.message());
            bytes.extend_from_slice(&claim.slot().to_le_bytes());
            bytes.extend(public_key_bytes);
            bytes.extend(signature.as_ssz_bytes());
            Signature::from_bytes(&bytes).unwrap()
        })
        .collect();
    (signatures, public_keys, claim)
}

#[test]
#[ignore = "slow: proves a full 1500-signature leaf"]
fn a_leaf_target_sized_batch_proves() {
    let (signatures, public_keys, claim) = cached_batch(LEAF_TARGET);
    let aggregate = prove(signatures, &claim).unwrap();
    verify(&aggregate, &public_keys, &claim).unwrap();
}

#[test]
#[ignore = "slow: proves two leaves and a root over 1501 signatures"]
fn a_batch_one_past_leaf_target_splits_and_proves() {
    let (signatures, public_keys, claim) = cached_batch(LEAF_TARGET + 1);
    let aggregate = prove(signatures, &claim).unwrap();
    verify(&aggregate, &public_keys, &claim).unwrap();
}
