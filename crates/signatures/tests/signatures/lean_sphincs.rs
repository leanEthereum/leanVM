use signatures::lean_sphincs::*;

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
        assert_eq!(
            LeanSphincsSecretKey::from_bytes(&sk.to_bytes()).unwrap().public_key(),
            pk
        );
        let message: Message = std::array::from_fn(|i| (b + i) as u8);
        let signature = sign(&sk, &message).unwrap();
        assert_eq!(verify(&pk, &message, &signature), Ok(()));
        assert_eq!(LeanSphincsSignature::from_bytes(&signature.to_bytes()), signature);

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
            let bad = LeanSphincsSignature::from_bytes(&bad);
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
        "7054a989f4814412beb7aa92a27754cc9d167007f63d9d5be961a15c88cd93d6"
    );
    assert_eq!(
        hex(&primitives::hash::hash(&signature.to_bytes())),
        "238e7fa60d2e215b00053855769a00e2bebb1d36955311d1bba56e0aae02faaf"
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
    // The signer grinds from the hash state before the counter; the encoding is
    // still `Th(P, A_enc(idx), K | LE_32(c))` in one piece.
    let payload = [
        forest_key.as_flattened().as_flattened(),
        &signature.counter.to_le_bytes(),
    ]
    .concat();
    let digest = th(pp, &tweak(TWEAK_ENC, 0, idx as u32), &payload);
    let d = u128::from_le_bytes(digest);
    let word: [u8; V] = std::array::from_fn(|i| ((d >> (W * i)) & (CHAIN_LEN as u128 - 1)) as u8);
    assert_eq!(encode(pp, idx as u32, &forest_key, signature.counter), Some(word));
    assert!((0..signature.counter).all(|c| encode(pp, idx as u32, &forest_key, c).is_none()));
}
