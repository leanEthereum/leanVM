use rand::{Rng, SeedableRng, rngs::StdRng};
use sphincs::*;

fn test_message() -> Message {
    std::array::from_fn(|i| (i * 5 + 3) as u8)
}

fn test_key(seed: u64) -> (SphincsSecretKey, SphincsPublicKey) {
    key_gen(&mut StdRng::seed_from_u64(seed))
}

#[test]
fn keygen_sign_verify() {
    let (sk, pk) = test_key(0);
    assert_eq!(sk.public_key(), pk);
    let message = test_message();
    for round in 0..2 {
        let signature = sign(&mut StdRng::seed_from_u64(round), &sk, &message).unwrap();
        verify(&pk, &message, &signature).unwrap();
    }
}

#[test]
fn serialized_sizes_and_roundtrip() {
    let (sk, pk) = test_key(1);
    let message = test_message();
    let signature = sign(&mut StdRng::seed_from_u64(7), &sk, &message).unwrap();

    let public_key_bytes = pk.flatten();
    assert_eq!(public_key_bytes.len(), 32);
    assert_eq!(SphincsPublicKey::from_bytes(&public_key_bytes), pk);

    let signature_bytes = signature.to_bytes();
    assert_eq!(signature_bytes.len(), 4924);
    let decoded = SphincsSignature::from_bytes(&signature_bytes);
    assert_eq!(decoded, signature);
    verify(&pk, &message, &decoded).unwrap();
}

#[test]
fn tampered_signatures_rejected() {
    let (sk, pk) = test_key(2);
    let message = test_message();
    let signature = sign(&mut StdRng::seed_from_u64(3), &sk, &message).unwrap();
    verify(&pk, &message, &signature).unwrap();

    let mut other_message = message;
    other_message[0] ^= 1;
    assert!(verify(&pk, &other_message, &signature).is_err());

    let mut other_key = pk;
    other_key.root[0] ^= 1;
    assert!(verify(&other_key, &message, &signature).is_err());

    // Verification recomputes the digest, so a tampered randomizer asks for
    // another index, and asks it of a digest that is admissible only one time in
    // 2^a.
    let mut tampered = signature.clone();
    tampered.randomizer[0] ^= 1;
    assert_eq!(
        verify(&pk, &message, &tampered),
        Err(SphincsVerifyError::InadmissibleDigest)
    );

    // Everything the bottom layers carry feeds the message a layer above signs,
    // and a counter is admissible for one message in 2^13.6, so tampering
    // surfaces as an inadmissible encoding rather than as a wrong root.
    for tamper in [
        (|s: &mut SphincsSignature| s.fts.secrets[5][0] ^= 1) as fn(&mut SphincsSignature),
        |s: &mut SphincsSignature| s.fts.paths[9][4][0] ^= 1,
        |s: &mut SphincsSignature| s.counters[2] ^= 1,
        |s: &mut SphincsSignature| s.ots[1][17][0] ^= 1,
        |s: &mut SphincsSignature| s.paths[H - 1][0] ^= 1,
    ] {
        let mut tampered = signature.clone();
        tamper(&mut tampered);
        assert_eq!(
            verify(&pk, &message, &tampered),
            Err(SphincsVerifyError::InadmissibleEncoding)
        );
    }

    // Layer 0's path is the exception: nothing is signed above it, so it can
    // only fail the root comparison.
    let mut tampered = signature.clone();
    tampered.paths[0][0] ^= 1;
    assert_eq!(verify(&pk, &message, &tampered), Err(SphincsVerifyError::RootMismatch));

    let mut tampered = signature.clone();
    tampered.ots[0][17][0] ^= 1;
    assert_eq!(verify(&pk, &message, &tampered), Err(SphincsVerifyError::RootMismatch));
}

/// One key signs one codeword, on which the whole one-time argument rests: the
/// counter is the least admissible one, not any admissible one.
#[test]
fn ots_counter_is_the_least_admissible() {
    let mut rng = StdRng::seed_from_u64(4);
    let public_param: PublicParam = rng.random();
    let master: MasterSecret = rng.random();
    let pos = Pos::new(2, 1234, 56);
    let message: Digest = rng.random();

    let (counter, signature) = ots_sign(&public_param, &master, pos, &message).unwrap();
    assert!((0..counter).all(|c| encode(&public_param, pos, &message, c).is_none()));
    assert_eq!(
        ots_leaf(&public_param, pos, &message, counter, &signature),
        Some(ots_public_leaf(&public_param, &master, pos))
    );
}

#[test]
fn index_decomposition_is_a_bijection_onto_the_bottom_layer() {
    let mut rng = StdRng::seed_from_u64(5);
    for _ in 0..1000 {
        let idx = rng.random::<u64>() % (1 << H);
        // Every layer's tree is the one whose root sits at the leaf its parent
        // layer uses.
        for lay in 1..D {
            let expected =
                u64::from(tree_of(idx, lay - 1)) * (1 << HEIGHTS[lay - 1]) + u64::from(leaf_of(idx, lay - 1));
            assert_eq!(u64::from(tree_of(idx, lay)), expected);
        }
        assert_eq!(tree_of(idx, 0), 0);
        assert_eq!(
            u64::from(tree_of(idx, D - 1)) * (1 << HEIGHTS[D - 1]) + u64::from(leaf_of(idx, D - 1)),
            idx
        );
    }
}

/// The counter search and the digest resampling are the signer's two grinding
/// loops; both costs are a property of the predicates, so a drift here is a
/// change of scheme.
#[test]
#[ignore]
fn grinding_bits() {
    let mut rng = StdRng::seed_from_u64(6);
    let public_param: PublicParam = rng.random();
    let master: MasterSecret = rng.random();

    let samples = 200;
    let counters: u64 = (0..samples)
        .map(|i| {
            let message: Digest = rng.random();
            let pos = Pos::new(i % D, i as u32, i as u32);
            u64::from(ots_sign(&public_param, &master, pos, &message).unwrap().0)
        })
        .sum();
    // A codeword is one admissible digest, so 1/p is the number of them over
    // 2^128: 2^13.60 for T = 191.
    let encoding_bits = ((counters as f64 / samples as f64) + 1.0).log2();
    println!("counter search: 2^{encoding_bits:.2} attempts");
    assert!(
        (12.6..14.6).contains(&encoding_bits),
        "encoding cost moved: {encoding_bits:.2} bits"
    );

    let root: Digest = rng.random();
    let message = test_message();
    let mut attempts = 0u64;
    for _ in 0..samples {
        loop {
            attempts += 1;
            let randomizer: Randomizer = rng.random();
            if message_digest(&public_param, &root, &randomizer, &message).1[K - 1] == 0 {
                break;
            }
        }
    }
    let digest_bits = (attempts as f64 / samples as f64).log2();
    println!("digest resampling: 2^{digest_bits:.2} attempts");
    assert!(
        ((A as f64 - 1.0)..(A as f64 + 1.0)).contains(&digest_bits),
        "digest cost moved: {digest_bits:.2} bits"
    );
}

/// A reloaded secret key must sign exactly as the original does: `key_gen`
/// samples the master secret itself, so these bytes are the only way back to a
/// key it produced.
#[test]
fn secret_key_survives_a_round_trip() {
    let (sk, pk) = test_key(7);
    let reloaded = SphincsSecretKey::from_bytes(&sk.to_bytes());

    assert_eq!(reloaded.public_key(), pk);
    let message = test_message();
    let sig = sign(&mut StdRng::seed_from_u64(1), &reloaded, &message).unwrap();
    verify(&pk, &message, &sig).unwrap();
}

#[test]
fn secret_derivation_uses_full_master() {
    let pp = [3; PUBLIC_PARAM_LEN];
    let master = [7; MASTER_SECRET_LEN];
    let pos = Pos::new(2, 5, 6);
    let ots = ots_secret(&pp, &master, pos, 4);
    let (fts, _) = fts_open(&pp, &master, 5, &[0; K]);
    for byte in 0..MASTER_SECRET_LEN {
        let mut changed = master;
        changed[byte] ^= 1;
        assert_ne!(ots_secret(&pp, &changed, pos, 4), ots);
        assert_ne!(fts_open(&pp, &changed, 5, &[0; K]).0, fts);
    }
}

/// The split between the two entry points: the seed alone determines the key,
/// and the rng one draws a fresh seed per call rather than a fixed one.
#[test]
fn key_gen_entry_points() {
    let seed = [17u8; 32];
    let (_, from_seed) = key_gen_from_seed(seed);
    assert_eq!(key_gen_from_seed(seed).1, from_seed);

    let mut rng = StdRng::seed_from_u64(31);
    let (_, first) = key_gen(&mut rng);
    let (_, second) = key_gen(&mut rng);
    assert_ne!(first, second);

    // The rng path is exactly a drawn seed, so it reproduces under a fixed rng.
    let drawn: [u8; 32] = StdRng::seed_from_u64(31).random();
    assert_eq!(key_gen_from_seed(drawn).1, first);
}
