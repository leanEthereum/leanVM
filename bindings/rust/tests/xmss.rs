//! leanXMSS keys, signatures and their byte encodings.

use lean_pq::xmss::{LeafIndex, PublicKey, SecretKey, Signature, SIGNATURE_LEN};
use lean_pq::{Encoding, Error, PUBLIC_KEY_LEN};
use proptest::collection::vec;
use proptest::prelude::*;

#[test]
fn signs_and_verifies_at_the_boundary_leaf_indices() {
    let key = SecretKey::from_seed([1; 32]);
    let message = [0x42; 32];

    // Leaf index = bottom tree (high 16 bits) | leaf in it (low 16 bits).
    //
    //     0            first leaf of the first bottom tree
    //     2^16 + 3     a leaf of the second bottom tree, prepared ahead
    //     2^32 - 1     last leaf of the last bottom tree
    for leaf_index in [0, (1 << 16) + 3, LeafIndex::MAX] {
        // Preparing only moves the bottom-tree build earlier.
        key.prepare(leaf_index);
        let signature = key.sign(&message, leaf_index);

        // The signature carries its leaf index, and verifies under the key.
        assert_eq!(signature.leaf_index(), leaf_index);
        key.public_key().verify(&message, &signature).unwrap();
    }
}

#[test]
fn verify_rejects_another_message_and_another_key() {
    let key = SecretKey::from_seed([2; 32]);
    let other_key = SecretKey::from_seed([3; 32]);
    let message = [0x42; 32];
    let signature = key.sign(&message, 7);

    // Mutation: change the message, then the key.
    //
    //     (key,       other message)  -> reject
    //     (other key, same message)   -> reject
    //
    // Both name the leaf index the signature claims.
    for (public_key, message) in [
        (key.public_key(), [0x43; 32]),
        (other_key.public_key(), message),
    ] {
        let error = public_key.verify(&message, &signature).unwrap_err();
        assert_eq!(error, Error::XmssVerify { leaf_index: 7 });
    }
}

#[test]
fn secret_key_encodes_as_its_seed() {
    let seed = [4; 32];
    let key = SecretKey::from_seed(seed);

    // The encoding is the seed itself: 32 bytes, no expanded state.
    assert_eq!(key.to_bytes(), seed);

    // Decoding regenerates the same key, which signs verifiably.
    let restored = SecretKey::from_bytes(&key.to_bytes()).unwrap();
    assert_eq!(restored.public_key(), key.public_key());
    let signature = restored.sign(&[7; 32], 9);
    key.public_key().verify(&[7; 32], &signature).unwrap();
}

#[test]
fn key_loads_from_its_tree_cache() {
    let seed = [5; 32];
    let key = SecretKey::from_seed(seed);
    let message = [0x42; 32];
    let leaf_index = (3 << 16) + 7;

    // The cache holds the top tree, and the bottom tree prepared here.
    key.prepare(leaf_index);
    let cache = key.cache_to_bytes();
    let loaded = SecretKey::from_cache_bytes(seed, &key.public_key(), &cache).unwrap();

    // The loaded key is the same key: same public key, same cache, same signature.
    assert_eq!(loaded.public_key(), key.public_key());
    assert_eq!(loaded.cache_to_bytes(), cache);
    let signature = loaded.sign(&message, leaf_index);
    assert_eq!(signature, key.sign(&message, leaf_index));
    key.public_key().verify(&message, &signature).unwrap();

    // A truncated cache, a tampered one, or another key's is refused.
    let mut tampered = cache.clone();
    tampered[0] ^= 1;
    let other = SecretKey::from_seed([6; 32]).public_key();
    for (public_key, bytes) in [
        (key.public_key(), &cache[1..]),
        (key.public_key(), &tampered[..]),
        (other, &cache[..]),
    ] {
        assert_eq!(
            SecretKey::from_cache_bytes(seed, &public_key, bytes).unwrap_err(),
            Error::InvalidXmssCache
        );
    }
}

#[test]
fn debug_output_never_contains_the_seed() {
    let key = SecretKey::from_seed([0xab; 32]);

    // The rendering is exactly the public key and an elision marker: nothing else.
    //
    //     SecretKey { public_key: PublicKey(..), .. }
    let public_key = key.public_key();
    assert_eq!(
        format!("{key:?}"),
        format!("SecretKey {{ public_key: {public_key:?}, .. }}")
    );
}

proptest! {
    #[test]
    fn public_key_bytes_round_trip(bytes in any::<[u8; PUBLIC_KEY_LEN]>()) {
        // Decoding is a plain split, so every 32-byte string round-trips exactly.
        let key = PublicKey::from_bytes(&bytes).unwrap();
        prop_assert_eq!(key.to_bytes(), bytes);
    }

    #[test]
    fn signature_bytes_round_trip(bytes in vec(any::<u8>(), SIGNATURE_LEN)) {
        // Every 2404-byte string decodes, and re-encodes to itself.
        let signature = Signature::from_bytes(&bytes).unwrap();
        prop_assert_eq!(&signature.to_bytes()[..], &bytes[..]);

        // Layout: the leaf index is the first 4 bytes, little-endian.
        let leaf_index = LeafIndex::from_le_bytes(bytes[..4].try_into().unwrap());
        prop_assert_eq!(signature.leaf_index(), leaf_index);
    }

    #[test]
    fn decoders_reject_every_other_length(len in 0..2 * SIGNATURE_LEN) {
        let bytes = vec![0; len];

        // Fixture state: each decoder accepts exactly one length.
        //
        //     public key   32
        //     secret key   32
        //     signature    2404
        let cases = [
            (Encoding::XmssPublicKey, PUBLIC_KEY_LEN, PublicKey::from_bytes(&bytes).err()),
            (Encoding::XmssSecretKey, 32, SecretKey::from_bytes(&bytes).err()),
            (Encoding::XmssSignature, SIGNATURE_LEN, Signature::from_bytes(&bytes).err()),
        ];
        for (encoding, expected, error) in cases {
            // Any other length fails, and the error names all three facts.
            if len != expected {
                let error = error.unwrap();
                prop_assert_eq!(
                    &error,
                    &Error::InvalidLength { encoding, expected, actual: len }
                );
                prop_assert_eq!(
                    error.to_string(),
                    format!("{encoding} must be {expected} bytes, got {len}")
                );
            }
        }
    }
}
