use signatures::lean_sphincs::*;

fn seed(x: u8) -> MasterSecret {
    std::array::from_fn(|i| x.wrapping_mul(31).wrapping_add(i as u8))
}

fn unhex(s: &str) -> Vec<u8> {
    (0..s.len())
        .step_by(2)
        .map(|i| u8::from_str_radix(&s[i..i + 2], 16).unwrap())
        .collect()
}

/// A known answer, byte for byte: the key of the seed `S[i] = 37 i + 11` and its
/// signature of the message `m[i] = 7 i + 3`.
#[test]
fn known_answer() {
    let vector = include_str!("lean_sphincs_known_answer.hex");
    let mut lines = vector.lines();
    let (pk_bytes, sig_bytes) = (unhex(lines.next().unwrap()), unhex(lines.next().unwrap()));
    let (sk, pk) = key_gen_from_seed(std::array::from_fn(|i| (37 * i + 11) as u8));
    let message: Message = std::array::from_fn(|i| (7 * i + 3) as u8);
    assert_eq!(pk.flatten()[..], pk_bytes[..]);
    let signature = sign(&sk, &message).unwrap();
    assert_eq!(signature.to_bytes()[..], sig_bytes[..]);
    assert_eq!(
        message_digest(&pk.public_param, &signature.randomizer, &message).0,
        65963065
    );
    assert_eq!(verify(&pk, &message, &signature), Ok(()));
}

#[test]
fn signatures_verify_and_tampered_ones_do_not() {
    let (sk, pk) = key_gen_from_seed(seed(3));
    assert_eq!(LeanSphincsSecretKey::from_bytes(&sk.to_bytes()).public_key(), pk);
    let message: Message = std::array::from_fn(|i| (3 + i) as u8);
    let signature = sign(&sk, &message).unwrap();
    assert_eq!(verify(&pk, &message, &signature), Ok(()));
    assert_eq!(LeanSphincsSignature::from_bytes(&signature.to_bytes()), signature);

    let mut other = message;
    other[0] ^= 1;
    assert!(verify(&pk, &other, &signature).is_err());
    let mut key = pk;
    key.public_param[0] ^= 1;
    assert!(verify(&key, &message, &signature).is_err());
    // Every value of the signature is bound: a flipped bit in any of them, or in
    // a counter, is refused.
    let bytes = signature.to_bytes();
    let mut values = (0..RANDOMIZER_LEN + FORS_TREES * FORS_OPENING_SIZE)
        .step_by(N)
        .collect::<Vec<_>>();
    let mut at = RANDOMIZER_LEN + FORS_TREES * FORS_OPENING_SIZE;
    for height in LAYER_HEIGHTS {
        values.extend((at..at + COUNTER_LEN).chain((at + COUNTER_LEN..at + layer_sig_size(height)).step_by(N)));
        at += layer_sig_size(height);
    }
    for at in values {
        let mut bad = bytes;
        bad[at] ^= 1;
        let bad = LeanSphincsSignature::from_bytes(&bad);
        assert!(verify(&pk, &message, &bad).is_err(), "byte {at}");
    }
}

#[test]
fn the_counter_is_the_least_admissible() {
    let (sk, pk) = key_gen_from_seed(seed(4));
    let message = [9; MESSAGE_LEN];
    let signature = sign(&sk, &message).unwrap();
    let pp = &pk.public_param;
    let (idx, leaves) = message_digest(pp, &signature.randomizer, &message);
    let fors_key = fors_recover(pp, idx as u32, &leaves, &signature.fors);
    let key = OtsKey::of_index(0, idx);
    let signed = fors_key_bytes(&fors_key);
    let counter = signature.layers[0].counter;
    // The signer grinds from the hash state before the counter; the encoding is
    // still `Th(P, A_enc(K), M | LE_32(c))` in one piece.
    let digest = th(pp, &key.tweak(TWEAK_ENC, 0), &[signed, &counter.to_le_bytes()].concat());
    let d = u128::from_le_bytes(digest);
    let word: [u8; V] = std::array::from_fn(|i| ((d >> (W * i)) & (CHAIN_LEN as u128 - 1)) as u8);
    assert_eq!(encode(pp, &key, signed, counter), Some(word));
    assert!((0..counter).all(|c| encode(pp, &key, signed, c).is_none()));
}
