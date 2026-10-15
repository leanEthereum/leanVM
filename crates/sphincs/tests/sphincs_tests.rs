use sphincs::*;

fn seed(x: u8) -> MasterSecret {
    std::array::from_fn(|i| x.wrapping_mul(31).wrapping_add(i as u8))
}

fn hex(bytes: &[u8]) -> String {
    bytes.iter().map(|b| format!("{b:02x}")).collect()
}

#[test]
fn signatures_verify_and_tampered_ones_do_not() {
    // At 20 the key stores its subtree from level 1: a signature rebuilds below it.
    for b in [3, 10, 20] {
        let (sk, pk) = key_gen_from_seed(seed(b as u8), b);
        assert_eq!(SphincsSecretKey::from_bytes(&sk.to_bytes()).unwrap().public_key(), pk);
        let message: Message = std::array::from_fn(|i| (b + i) as u8);
        let signature = sign(&sk, &message).unwrap();
        assert_eq!(verify(&pk, &message, &signature), Ok(()));
        assert_eq!(SphincsSignature::from_bytes(&signature.to_bytes()), signature);

        let mut other = message;
        other[0] ^= 1;
        assert!(verify(&pk, &other, &signature).is_err());
        let mut key = pk;
        key.public_param[0] ^= 1;
        assert!(verify(&key, &message, &signature).is_err());
        // Every value of the signature is bound: a flipped bit in any of them,
        // or in the counter, is refused.
        let bytes = signature.to_bytes();
        let counter = RANDOMIZER_LEN + FOREST_TREES * TREE_VALUES * N;
        for at in (0..counter).step_by(N).chain((counter..SIG_SIZE).step_by(N)) {
            let mut bad = bytes;
            bad[at] ^= 1;
            let bad = SphincsSignature::from_bytes(&bad);
            assert!(verify(&pk, &message, &bad).is_err(), "byte {at}");
        }
    }
}

/// Pins the key and the signature bytes of one pruned key, so that a change to
/// the addresses, the hash inputs, the codeword table or the serialization
/// cannot pass unnoticed.
#[test]
fn known_answer() {
    let (sk, pk) = key_gen_from_seed(seed(1), 11);
    let message: Message = std::array::from_fn(|i| (7 * i) as u8);
    let signature = sign(&sk, &message).unwrap();
    assert_eq!(
        hex(&pk.flatten()),
        "7066d47a61f9c2a228f81d33414f773384d69cadea1e1374ab3bd20be993910c"
    );
    assert_eq!(
        hex(&primitives::hash::hash(&signature.to_bytes())),
        "b76d90bb1f04661724f5f759f7e198fed50a19f8d89c70122ad7eaa3b2902258"
    );
}

#[test]
fn the_counter_is_the_least_admissible() {
    let (sk, pk) = key_gen_from_seed(seed(4), 4);
    let signature = sign(&sk, &[9; MESSAGE_LEN]).unwrap();
    let pp = &pk.public_param;
    let (idx, marks) = message_digest(pp, &signature.randomizer, &[9; MESSAGE_LEN]);
    let forest_key = forest_recover(pp, idx as u32, &marks, &signature.forest);
    assert!(encode(pp, idx as u32, &forest_key, signature.counter).is_some());
    assert!((0..signature.counter).all(|c| encode(pp, idx as u32, &forest_key, c).is_none()));
}
