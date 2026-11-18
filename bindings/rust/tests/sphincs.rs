//! leanSPHINCS keys, signatures and their byte encodings.

use lean_pq::sphincs::{PublicKey, SecretKey, Signature, SECRET_KEY_LEN, SIGNATURE_LEN};
use lean_pq::{Encoding, Error, PUBLIC_KEY_LEN};
use proptest::collection::vec;
use proptest::prelude::*;

#[test]
fn signs_verifies_and_rejects_another_message() {
    let key = SecretKey::from_seed([1; 32]);
    let message = [0x42; 32];
    let signature = key.sign(&message);
    key.public_key().verify(&message, &signature).unwrap();

    // Signing is deterministic: the randomizer derives from the seed and the message.
    assert_eq!(key.sign(&message), signature);

    // Mutation: verify the same signature against another message.
    let error = key
        .public_key()
        .verify(&[0x43; 32], &signature)
        .unwrap_err();
    assert_eq!(error, Error::SphincsVerify);
}

#[test]
fn secret_key_encodes_as_its_seed() {
    let seed = [2; 32];
    let key = SecretKey::from_seed(seed);
    assert_eq!(key.to_bytes(), seed);

    // Decoding regenerates the same key, and signs as it does.
    let restored = SecretKey::from_bytes(&key.to_bytes()).unwrap();
    assert_eq!(restored.public_key(), key.public_key());
    let message = [7; 32];
    assert_eq!(restored.sign(&message), key.sign(&message));
}

#[test]
fn generated_keys_are_distinct() {
    // Two keys from the operating system's randomness share no seed.
    let first = SecretKey::generate();
    let second = SecretKey::generate();
    assert_ne!(first.to_bytes(), second.to_bytes());
    assert_ne!(first.public_key(), second.public_key());
}

#[test]
fn debug_output_never_contains_the_seed() {
    let key = SecretKey::from_seed([0xab; 32]);

    // The rendering is exactly the public data and an elision marker.
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
        // Every 7740-byte string decodes, and re-encodes to itself.
        let signature = Signature::from_bytes(&bytes).unwrap();
        prop_assert_eq!(&signature.to_bytes()[..], &bytes[..]);
    }

    #[test]
    fn decoders_reject_every_other_length(len in 0..2 * SIGNATURE_LEN) {
        let bytes = vec![0; len];

        // Fixture state: each decoder accepts exactly one length.
        //
        //     public key   32
        //     secret key   32
        //     signature    7740
        let cases = [
            (Encoding::SphincsPublicKey, PUBLIC_KEY_LEN, PublicKey::from_bytes(&bytes).err()),
            (Encoding::SphincsSecretKey, SECRET_KEY_LEN, SecretKey::from_bytes(&bytes).err()),
            (Encoding::SphincsSignature, SIGNATURE_LEN, Signature::from_bytes(&bytes).err()),
        ];
        for (encoding, expected, error) in cases {
            // Any other length fails, and the error names all three facts.
            if len != expected {
                prop_assert_eq!(
                    error.unwrap(),
                    Error::InvalidLength { encoding, expected, actual: len }
                );
            }
        }
    }
}
