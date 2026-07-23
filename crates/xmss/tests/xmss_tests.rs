use backend::*;
use rand::{SeedableRng, rngs::StdRng};
use xmss::*;

type F = KoalaBear;

#[test]
fn test_xmss_serialize_deserialize() {
    let message: [u8; MESSAGE_LEN_BYTES] = std::array::from_fn(|i| (i * 3 + 7) as u8);
    let slot = 110;

    let (pk, sk) = xmss_key_gen(&mut StdRng::seed_from_u64(0), 100, 16).unwrap();
    let sig = xmss_sign(&sk, slot, &message).unwrap();

    let pk_bytes = postcard::to_allocvec(&pk).unwrap();
    let pk2: XmssPublicKey = postcard::from_bytes(&pk_bytes).unwrap();
    assert_eq!(pk, pk2);

    let sig_bytes = postcard::to_allocvec(&sig).unwrap();
    let sig2: XmssSignature = postcard::from_bytes(&sig_bytes).unwrap();
    assert_eq!(sig, sig2);

    xmss_verify(&pk2, slot, &message, &sig2).unwrap();

    // Secret key: persist and reload, then check the reloaded key behaves identically.
    let sk_bytes = postcard::to_allocvec(&sk).unwrap();
    let sk2: XmssSecretKey = postcard::from_bytes(&sk_bytes).unwrap();
    assert_eq!(sk2.public_key(), pk);
    assert_eq!(xmss_sign(&sk2, slot, &message).unwrap(), sig);

    // A top tree whose shape does not match the slot range must be rejected.
    let (version, seed, start, end, mut top): (u8, [u8; 32], u32, u32, Vec<Vec<Digest>>) =
        postcard::from_bytes(&sk_bytes).unwrap();
    top.pop();
    let corrupted = postcard::to_allocvec(&(version, seed, start, end, top)).unwrap();
    assert!(postcard::from_bytes::<XmssSecretKey>(&corrupted).is_err());

    // An unknown format version must be rejected.
    let mut wrong_version = sk_bytes.clone();
    wrong_version[0] ^= 1;
    assert!(postcard::from_bytes::<XmssSecretKey>(&wrong_version).is_err());
}

#[test]
fn keygen_sign_verify() {
    let message: [u8; MESSAGE_LEN_BYTES] = std::array::from_fn(|i| (i * 3 + 7) as u8);

    for slot in [0, 1234, u32::MAX] {
        let activation_slot = (slot as u64).saturating_sub(1);
        let num_active_slots = (slot as u64 + 3).min(1 << LOG_LIFETIME) - activation_slot;
        let mut rng = StdRng::seed_from_u64(slot as u64);
        let (pk, sk) = xmss_key_gen(&mut rng, activation_slot, num_active_slots).unwrap();
        let sig = xmss_sign(&sk, slot, &message).unwrap();
        xmss_verify(&pk, slot, &message, &sig).unwrap();

        let mut other_message = message;
        other_message[0] ^= 1;
        assert!(xmss_verify(&pk, slot, &other_message, &sig).is_err());
    }
}

#[test]
fn signing_is_deterministic() {
    let message: [u8; MESSAGE_LEN_BYTES] = std::array::from_fn(|i| i as u8);
    let (_, sk) = xmss_key_gen(&mut StdRng::seed_from_u64(7), 40, 10).unwrap();
    assert_eq!(
        xmss_sign(&sk, 42, &message).unwrap(),
        xmss_sign(&sk, 42, &message).unwrap()
    );
    assert_eq!(
        xmss_sign(&sk, 39, &message).unwrap_err(),
        XmssSignatureError::SlotOutOfRange
    );
    assert_eq!(
        xmss_sign(&sk, 50, &message).unwrap_err(),
        XmssSignatureError::SlotOutOfRange
    );
}

#[test]
fn prepare_warms_the_signing_cache() {
    let message: [u8; MESSAGE_LEN_BYTES] = std::array::from_fn(|i| i as u8);
    let (pk, sk) = xmss_key_gen(&mut StdRng::seed_from_u64(3), 1000, 300).unwrap();

    // Signatures are unaffected by preparation (it only warms the cache).
    let cold = xmss_sign(&sk, 1299, &message).unwrap();
    sk.prepare(1000).unwrap(); // different subtree: rebuilds the cache
    sk.prepare(1299).unwrap(); // back again
    let warm = xmss_sign(&sk, 1299, &message).unwrap();
    assert_eq!(cold, warm);
    xmss_verify(&pk, 1299, &message, &warm).unwrap();

    assert_eq!(sk.prepare(999).unwrap_err(), XmssSignatureError::SlotOutOfRange);
    assert_eq!(sk.prepare(1300).unwrap_err(), XmssSignatureError::SlotOutOfRange);
}

/// One key shared between signers inside pool tasks and on a plain thread. Bottom-subtree
/// builds during signing are always sequential, so a signer holding the cache mutex never
/// waits on the pool (which would deadlock with the pool tasks blocked on the same key).
/// Derandomization makes the signatures identical regardless of who produced them.
#[test]
fn concurrent_signing_on_shared_key() {
    let message: [u8; MESSAGE_LEN_BYTES] = std::array::from_fn(|i| i as u8);
    let (pk, sk) = xmss_key_gen(&mut StdRng::seed_from_u64(9), 0, 1 << 10).unwrap();
    let (pk, sk) = (&pk, &sk);

    std::thread::scope(|scope| {
        let plain_thread = scope.spawn(move || {
            (0..1024u32)
                .step_by(97)
                .map(|slot| (slot, xmss_sign(sk, slot, &message).unwrap()))
                .collect::<Vec<_>>()
        });
        parallel::for_each_index(64, |i| {
            let slot = (i * 61 % 1024) as u32;
            let sig = xmss_sign(sk, slot, &message).unwrap();
            xmss_verify(pk, slot, &message, &sig).unwrap();
        });
        for (slot, sig) in plain_thread.join().unwrap() {
            xmss_verify(pk, slot, &message, &sig).unwrap();
            assert_eq!(sig, xmss_sign(sk, slot, &message).unwrap());
        }
    });
}

#[test]
fn keygen_from_seed_is_deterministic() {
    let message: [u8; MESSAGE_LEN_BYTES] = std::array::from_fn(|i| i as u8);
    let seed = [42u8; 32];

    let (pk1, sk1) = xmss_key_gen_from_seed(seed, 100, 16).unwrap();
    let (pk2, sk2) = xmss_key_gen_from_seed(seed, 100, 16).unwrap();
    assert_eq!(pk1, pk2);
    assert_eq!(sk1.activation_slots(), 100..=115);
    assert_eq!(
        xmss_sign(&sk1, 110, &message).unwrap(),
        xmss_sign(&sk2, 110, &message).unwrap()
    );

    // Same seed, different activation range: a different key.
    let (pk3, _) = xmss_key_gen_from_seed(seed, 100, 32).unwrap();
    assert_ne!(pk1, pk3);
}

#[test]
fn keygen_rejects_invalid_ranges() {
    let mut rng = StdRng::seed_from_u64(0);
    assert_eq!(xmss_key_gen(&mut rng, 0, 0).unwrap_err(), XmssKeyGenError::InvalidRange);
    assert_eq!(
        xmss_key_gen(&mut rng, (1 << LOG_LIFETIME) - 1, 2).unwrap_err(),
        XmssKeyGenError::InvalidRange
    );
    assert_eq!(
        xmss_key_gen(&mut rng, u64::MAX, u64::MAX).unwrap_err(),
        XmssKeyGenError::InvalidRange
    );
}

#[test]
fn ssz_roundtrip() {
    use ssz::{Decode, Encode};

    let message: [u8; MESSAGE_LEN_BYTES] = std::array::from_fn(|i| i as u8);
    let slot = 110;
    let (pk, sk) = xmss_key_gen(&mut StdRng::seed_from_u64(1), 100, 16).unwrap();
    let sig = xmss_sign(&sk, slot, &message).unwrap();

    // Public key: fixed 32 bytes.
    let pk_bytes = pk.as_ssz_bytes();
    assert_eq!(pk_bytes.len(), PUB_KEY_SSZ_LEN);
    assert_eq!(pk_bytes.len(), 32);
    assert_eq!(XmssPublicKey::from_ssz_bytes(&pk_bytes).unwrap(), pk);

    // Signature: fixed 1208 bytes.
    let sig_bytes = sig.as_ssz_bytes();
    assert_eq!(sig_bytes.len(), SIGNATURE_SSZ_LEN);
    assert_eq!(sig_bytes.len(), 1208);
    assert_eq!(XmssSignature::from_ssz_bytes(&sig_bytes).unwrap(), sig);

    // Non-canonical field elements are rejected.
    let mut bad_pk = pk_bytes.clone();
    bad_pk[..4].copy_from_slice(&u32::MAX.to_le_bytes());
    assert!(XmssPublicKey::from_ssz_bytes(&bad_pk).is_err());

    // Wrong lengths are rejected.
    assert!(XmssPublicKey::from_ssz_bytes(&pk_bytes[1..]).is_err());
    assert!(XmssSignature::from_ssz_bytes(&sig_bytes[..SIGNATURE_SSZ_LEN - 1]).is_err());
}
