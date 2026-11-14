//! leanSPHINCS against the test vectors of EthLib, the Lean specification of the scheme.
//!
//! `ethlib/` is EthLib's `tests/cryptography/sphincs/`, vendored by `ethlib/sync.sh`.
//! `ethlib/COMMIT` names the EthLib commit it comes from.
//!
//! Every case runs, and each must give EthLib's output byte for byte:
//!
//! - `key_gen`: the public key of a seed.
//! - `sign`: the signature of a message.
//! - `verify`: whether a signature verifies.
//!
//! An output of `null` marks an input EthLib rejects.
//! Here such an input has the wrong length, so it does not fit the API's fixed-size arrays.

use crate::ethlib_cases::{Value, cases, exact};

use lean_sphincs::*;

#[test]
fn key_gen_matches_ethlib() {
    for case in cases("key_gen") {
        let output = match exact::<SECRET_KEY_LEN>(case.bytes("seed")) {
            Some(seed) => Value::Bytes(key_gen(&seed).to_bytes().to_vec()),
            None => Value::Null,
        };
        assert_eq!(output, case.output, "{}", case.name);
    }
}

#[test]
fn sign_matches_ethlib() {
    for case in cases("sign") {
        let output = match (
            exact::<SECRET_KEY_LEN>(case.bytes("seed")),
            exact::<MESSAGE_LEN>(case.bytes("message")),
        ) {
            (Some(seed), Some(message)) => Value::Bytes(sign(&seed, &message).to_bytes().to_vec()),
            _ => Value::Null,
        };
        assert_eq!(output, case.output, "{}", case.name);
    }
}

#[test]
fn verify_matches_ethlib() {
    for case in cases("verify") {
        let output = match (
            exact::<PUB_KEY_SIZE>(case.bytes("public_key")),
            exact::<MESSAGE_LEN>(case.bytes("message")),
            exact::<SIG_SIZE>(case.bytes("signature")),
        ) {
            (Some(pk), Some(message), Some(sig)) => Value::Bool(verify(
                &LeanSphincsPublicKey::from_bytes(&pk),
                &message,
                &LeanSphincsSignature::from_bytes(&sig),
            )),
            _ => Value::Null,
        };
        assert_eq!(output, case.output, "{}", case.name);
    }
}
