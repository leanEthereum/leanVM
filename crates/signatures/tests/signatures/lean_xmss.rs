use rand::{Rng, SeedableRng, rngs::StdRng};
use signatures::lean_xmss::*;

fn test_message() -> Message {
    std::array::from_fn(|i| (i * 3 + 7) as u8)
}

/// A full key: the whole top tree, and signatures in two bottom trees, each with
/// its own top-layer signature.
#[test]
fn full_key_signs_and_verifies() {
    let (sk, pk) = key_gen_from_seed([1; SEED_LEN]);
    let message = test_message();
    let first = sign(&sk, &message, 5).unwrap();
    verify(&pk, &message, &first).unwrap();
    let other_tree = sign(&sk, &message, (7 << LAYER_HEIGHT) + 3).unwrap();
    verify(&pk, &message, &other_tree).unwrap();
    assert_ne!(first.top, other_tree.top);
    assert_eq!(sign(&sk, &message, 5).unwrap(), first, "signing is deterministic");
}

/// Pins a full key's public key and one signature's bytes, so that a change to the
/// seed derivation, the addresses, the hash inputs or the serialization cannot pass
/// unnoticed. An implementation of `doc/lean_xmss` written from the text alone gives
/// the same bytes.
#[test]
fn known_answer() {
    let hex = |bytes: &[u8]| bytes.iter().map(|b| format!("{b:02x}")).collect::<String>();
    let seed: Seed = std::array::from_fn(|i| (i as u8).wrapping_mul(37).wrapping_add(11));
    let (sk, pk) = key_gen_from_seed(seed);
    let message: Message = std::array::from_fn(|i| (i * 7 + 3) as u8);
    let signature = sign(&sk, &message, 0xA5C3_7E19).unwrap();
    assert_eq!(
        hex(&pk.as_ssz_bytes()),
        "b60df5557dd72654da9b26eb5aee454fbb8b8839d80d6d0ab29a4226fc2c910f"
    );
    assert_eq!(
        hex(&primitives::hash::hash(&signature.as_ssz_bytes())),
        "76fe28fc5609099765d1289f0a75b397d8698e9abfe74d3f83bf01118e2db831"
    );
}

#[test]
fn mock_keys_sign_in_range() {
    let message = test_message();
    // A range across two bottom trees.
    let start = (3 << LAYER_HEIGHT) - 2;
    let (sk, pk) = mock::key_gen_from_seed([2; SEED_LEN], start, start + 5);
    for leaf_index in start..=start + 5 {
        let sig = mock::sign(&sk, &message, leaf_index).unwrap();
        assert_eq!(sig.leaf_index, leaf_index);
        verify(&pk, &message, &sig).unwrap();
    }
    let (_, same) = mock::key_gen_from_seed([2; SEED_LEN], start, start + 5);
    assert_eq!(pk, same);
}

/// The leaf index rides the signature, so the verifier hashes at it: moved to a
/// neighbour, or the message changed, the signature no longer verifies.
#[test]
fn signature_is_bound_to_its_leaf_index_and_message() {
    let (sk, pk) = mock::key_gen_from_seed([4; SEED_LEN], 0, 7);
    let message = test_message();
    let sig = mock::sign(&sk, &message, 5).unwrap();
    let mut moved = sig.clone();
    moved.leaf_index = 4;
    assert!(verify(&pk, &message, &moved).is_err());
    let mut other = message;
    other[0] ^= 1;
    assert!(verify(&pk, &other, &sig).is_err());
}

#[test]
fn serialize_deserialize_and_size() {
    let (sk, pk) = mock::key_gen_from_seed([5; SEED_LEN], 100, 115);
    let message = test_message();
    let sig = mock::sign(&sk, &message, 110).unwrap();

    let public_key_bytes = bincode::serialize(&pk).unwrap();
    assert_eq!(public_key_bytes.len(), PUB_KEY_SIZE);
    assert_eq!(
        bincode::deserialize::<LeanXmssPublicKey>(&public_key_bytes).unwrap(),
        pk
    );

    let signature_bytes = bincode::serialize(&sig).unwrap();
    assert_eq!(signature_bytes.len(), SIG_SIZE);
    let decoded: LeanXmssSignature = bincode::deserialize(&signature_bytes).unwrap();
    assert_eq!(decoded, sig);
    verify(&pk, &message, &decoded).unwrap();
}

/// A secret key encodes as its seed, and the reloaded key signs exactly as the
/// original does.
#[test]
fn secret_key_survives_a_round_trip() {
    let seed = [6; SEED_LEN];
    let (sk, pk) = key_gen_from_seed(seed);
    let bytes = bincode::serialize(&sk).unwrap();
    assert_eq!(bytes, seed);
    let reloaded: LeanXmssSecretKey = bincode::deserialize(&bytes).unwrap();
    assert_eq!(reloaded.public_key(), pk);
    let message = test_message();
    assert_eq!(sign(&reloaded, &message, 43).unwrap(), sign(&sk, &message, 43).unwrap());
}

/// The SSZ encoding is the container's fields concatenated, in declaration order.
/// Assembled independently here, so a reordered or resized field cannot be
/// mirrored by the impl.
#[test]
fn ssz_layout_is_exact() {
    let (sk, pk) = mock::key_gen_from_seed([7; SEED_LEN], 290, 310);
    let message = test_message();
    let sig = mock::sign(&sk, &message, 300).unwrap();

    assert_eq!(pk.as_ssz_bytes(), [pk.merkle_root, pk.public_param].concat());

    let mut expected = sig.leaf_index.to_le_bytes().to_vec();
    for layer in [&sig.bottom, &sig.top] {
        expected.extend_from_slice(&layer.randomizer);
        for value in layer.chain_values.iter().chain(&layer.path) {
            expected.extend_from_slice(value);
        }
    }
    assert_eq!(expected.len(), SIGNATURE_SSZ_LEN);
    assert_eq!(sig.as_ssz_bytes(), expected);
    assert_eq!(LeanXmssSignature::from_ssz_bytes(&expected).unwrap(), sig);
    assert_eq!(LeanXmssPublicKey::from_ssz_bytes(&pk.as_ssz_bytes()).unwrap(), pk);
}

/// A fixed-length container rejects any other length, and only that.
#[test]
fn ssz_rejects_wrong_lengths() {
    for len in [0, PUB_KEY_SSZ_LEN - 1, PUB_KEY_SSZ_LEN + 1] {
        assert!(matches!(
            LeanXmssPublicKey::from_ssz_bytes(&vec![0u8; len]),
            Err(DecodeError::InvalidByteLength { .. })
        ));
    }
    for len in [0, SIGNATURE_SSZ_LEN - 1, SIGNATURE_SSZ_LEN + 1] {
        assert!(matches!(
            LeanXmssSignature::from_ssz_bytes(&vec![0u8; len]),
            Err(DecodeError::InvalidByteLength { .. })
        ));
    }
    LeanXmssSignature::from_ssz_bytes(&[0xcd; SIGNATURE_SSZ_LEN]).unwrap();
}

/// The address layout is leanSPHINCS's, and `Th` is BLAKE2s of `P | A | M`.
#[test]
fn address_layout() {
    let tw = tweak(TWEAK_NODE, layer_hi(1, 0x12), 0x89abcdef).step(5);
    assert_eq!(address(&tw)[..8], [0xef, 0xcd, 0xab, 0x89, 0x12, 0x00, 0x80, 0xa3]);
    assert_eq!(address(&tw)[8..], [0; 8]);
    let pp: PublicParam = std::array::from_fn(|i| i as u8 + 1);
    let payload = [9u8; N];
    let input = [&pp[..], &address(&tw), &payload].concat();
    assert_eq!(th(&pp, &tw, &payload)[..], primitives::hash::hash(&input)[..N]);
}

/// Detect changes to the encoding predicate through its grinding cost.
#[test]
#[ignore]
fn encoding_grinding_bits() {
    let n = 1 << 26;
    let mut rng = StdRng::seed_from_u64(0);
    let hits = (0..n).filter(|_| codeword(&rng.random()).is_some()).count();
    let bits = (n as f64 / hits as f64).log2();
    println!("Average grinding bits: {bits:.1}");
    assert!((19.0..21.0).contains(&bits), "grinding cost moved: {bits:.2} bits");
}
