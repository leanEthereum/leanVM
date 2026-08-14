use lean_multisig_api::{Claim, Error, MultiClaimProof, SecretKey, Signature, aggregate, setup};

#[test]
fn proof_operations_require_explicit_setup_without_initializing_themselves() {
    let claim = Claim::new([0u8; 32], 0);
    let key = SecretKey::from_seed([1u8; 32], 0..=15).unwrap();

    assert!(matches!(
        aggregate(vec![key.sign(&claim).unwrap()], &claim),
        Err(Error::NotInitialized)
    ));
    assert!(matches!(
        Signature::from_bytes(b"LMSI\x01\x01proof"),
        Err(Error::NotInitialized)
    ));
    assert!(matches!(
        MultiClaimProof::from_bytes(b"LMCM\x01proof"),
        Err(Error::NotInitialized)
    ));
    setup();
    aggregate(vec![key.sign(&claim).unwrap()], &claim).unwrap();
}
