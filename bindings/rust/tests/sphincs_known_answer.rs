//! leanSPHINCS known answers, pinning the byte encodings to the FIPS 205 layout.
//!
//! The known answer is `crates/lean_sphincs`'s, shared with `ethereum/EthLib`
//! (`tests/cryptography/sphincs`): seed `37i + 11`, message `7i + 3`, both reduced mod 256.
//!
//! ```text
//!     crates/lean_sphincs/.../known_answer.hex   public key PK.seed || PK.root, then the signature
//!     fixtures/lean_sphincs_pre_fips205.hex      the same seed and message in the layout before
//!                                                FIPS 205 (ed7d2b9): root || public parameter
//! ```

use lean_pq::sphincs::{PublicKey, SecretKey, Signature, SIGNATURE_LEN};
use lean_pq::{Error, PUBLIC_KEY_LEN};

const KNOWN_ANSWER: &str = "crates/lean_sphincs/tests/lean_sphincs/known_answer.hex";
const PRE_FIPS205: &str = "bindings/rust/tests/fixtures/lean_sphincs_pre_fips205.hex";

/// The known answer's seed: `37i + 11`.
fn seed() -> [u8; 32] {
    std::array::from_fn(|i| u8::try_from((37 * i + 11) % 256).unwrap())
}

/// The known answer's message: `7i + 3`.
fn message() -> [u8; 32] {
    std::array::from_fn(|i| u8::try_from((7 * i + 3) % 256).unwrap())
}

/// Reads a fixture, by its path from the repository root: a public key, then a signature, one hex
/// line each.
fn fixture(path: &str) -> ([u8; PUBLIC_KEY_LEN], [u8; SIGNATURE_LEN]) {
    let path = format!("{}/../../{path}", env!("CARGO_MANIFEST_DIR"));
    let text = std::fs::read_to_string(&path).unwrap();
    let mut lines = text.split_whitespace().map(|line| {
        (0..line.len())
            .step_by(2)
            .map(|i| u8::from_str_radix(&line[i..i + 2], 16).unwrap())
            .collect::<Vec<u8>>()
    });
    let public_key = lines.next().unwrap().try_into().unwrap();
    let signature = lines.next().unwrap().try_into().unwrap();
    (public_key, signature)
}

#[test]
fn reproduces_the_known_answer() {
    let (public_key, signature) = fixture(KNOWN_ANSWER);
    let key = SecretKey::from_seed(seed());

    // The same seed grows the same public key, and signing is deterministic.
    assert_eq!(key.public_key().to_bytes(), public_key);
    assert_eq!(key.sign(&message()).to_bytes(), signature);

    // The vector verifies on its own, decoded from bytes.
    let public_key = PublicKey::from_bytes(&public_key).unwrap();
    let signature = Signature::from_bytes(&signature).unwrap();
    public_key.verify(&message(), &signature).unwrap();
}

#[test]
fn rejects_the_previous_layout() {
    let (public_key, signature) = fixture(PRE_FIPS205);
    let key = SecretKey::from_seed(seed());

    // The previous layout grew another public key from the same seed.
    assert_ne!(key.public_key().to_bytes(), public_key);

    // Its signature no longer verifies.
    let public_key = PublicKey::from_bytes(&public_key).unwrap();
    let signature = Signature::from_bytes(&signature).unwrap();
    assert_eq!(
        public_key.verify(&message(), &signature).unwrap_err(),
        Error::SphincsVerify
    );
}

#[test]
fn rejects_a_key_with_its_halves_swapped() {
    let (public_key, signature) = fixture(KNOWN_ANSWER);

    // Mutation: PK.root || PK.seed, the previous order of the two halves.
    let mut swapped = [0; PUBLIC_KEY_LEN];
    swapped[..16].copy_from_slice(&public_key[16..]);
    swapped[16..].copy_from_slice(&public_key[..16]);

    let swapped = PublicKey::from_bytes(&swapped).unwrap();
    let signature = Signature::from_bytes(&signature).unwrap();
    assert!(swapped.verify(&message(), &signature).is_err());
}
