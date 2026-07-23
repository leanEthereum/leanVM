use backend::*;
use rand::{RngExt, SeedableRng, rngs::StdRng};
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
#[ignore]
fn encoding_grinding_bits() {
    let n = 100;
    let xmss_pub_key = XmssPublicKey {
        merkle_root: Default::default(),
        public_param: Default::default(),
    };
    let total_iters = parallel::map_reduce(
        n,
        || 0usize,
        |i| {
            let message: [F; MESSAGE_LEN_FE] = Default::default();
            let slot = i as u32;
            let mut rng = StdRng::seed_from_u64(i as u64);
            let mut num_iters = 0;
            loop {
                num_iters += 1;
                let randomness: [F; RANDOMNESS_LEN_FE] = rng.random();
                if wots_encode(&message, slot, &xmss_pub_key, &randomness).is_some() {
                    break num_iters;
                }
            }
        },
        |a, b| a + b,
    );
    let grinding = ((total_iters as f64) / (n as f64)).log2();
    println!("Average grinding bits: {:.1}", grinding);
}
