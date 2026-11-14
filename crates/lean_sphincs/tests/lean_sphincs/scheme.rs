use lean_sphincs::*;

fn seed(x: u8) -> Seed {
    std::array::from_fn(|i| x.wrapping_mul(31).wrapping_add(i as u8))
}

#[test]
fn signatures_verify_and_tampered_ones_do_not() {
    let (sk, pk) = key_gen_from_seed(seed(3));
    // The seed is SK.seed, and PK.seed = H("leanSPHINCS" || SK.seed || 0) cut to N bytes.
    let derive = |domain: u8| primitives::hash::hash(&[b"leanSPHINCS".as_slice(), &seed(3), &[domain]].concat());
    assert_eq!(pk.__pk_seed()[..], derive(0)[..N]);
    assert_eq!(LeanSphincsSecretKey::from_bytes(&sk.to_bytes()).public_key(), pk);
    let message: Message = std::array::from_fn(|i| (3 + i) as u8);
    let signature = sign(&sk, &message);
    assert!(verify(&pk, &message, &signature));
    assert_eq!(LeanSphincsSignature::from_bytes(&signature.to_bytes()), signature);

    let mut other = message;
    other[0] ^= 1;
    assert!(!verify(&pk, &other, &signature));
    let mut bytes = pk.to_bytes();
    bytes[0] ^= 1;
    let key = LeanSphincsPublicKey::from_bytes(&bytes);
    assert!(!verify(&key, &message, &signature));
    // Every value of the signature is bound: a flipped bit in any of them, or in
    // a counter, is refused.
    let bytes = signature.to_bytes();
    let mut values = (0..N + FORS_TREES * FORS_OPENING_SIZE).step_by(N).collect::<Vec<_>>();
    let mut at = N + FORS_TREES * FORS_OPENING_SIZE;
    for height in LAYER_HEIGHTS {
        values.extend((at..at + COUNTER_LEN).chain((at + COUNTER_LEN..at + layer_sig_size(height)).step_by(N)));
        at += layer_sig_size(height);
    }
    for at in values {
        let mut bad = bytes;
        bad[at] ^= 1;
        let bad = LeanSphincsSignature::from_bytes(&bad);
        assert!(!verify(&pk, &message, &bad), "byte {at}");
    }
}
