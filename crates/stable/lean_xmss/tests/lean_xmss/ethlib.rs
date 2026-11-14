//! leanXMSS against the test vectors of EthLib, the Lean specification of the scheme.
//!
//! `ethlib/` is EthLib's `tests/cryptography/xmss/`, vendored by `ethlib/sync.sh`.
//! `ethlib/COMMIT` names the EthLib commit it comes from.
//!
//! Every case runs, and each must give EthLib's output byte for byte:
//!
//! - `key_gen`: the public key of a seed.
//! - `sign`: the signature of a message at a leaf index.
//! - `verify`: whether a signature verifies.
//! - `signature_index`: the leaf index a signature names.
//!
//! An output of `null` marks an input EthLib rejects.
//! Here such an input has the wrong length, so it does not fit the API's fixed-size arrays.

use std::collections::HashMap;

use crate::ethlib_cases::{Case, Value, cases, exact};

/// The integer input `key`.
fn int(case: &Case, key: &str) -> u64 {
    match case.input.get(key) {
        Some(Value::Int(n)) => *n,
        other => panic!("{}: input {key} is {other:?}, not an integer", case.name),
    }
}

use lean_xmss::*;

#[test]
fn key_gen_matches_ethlib() {
    for case in cases("key_gen") {
        let output = match exact::<SECRET_KEY_LEN>(case.bytes("seed")) {
            Some(seed) => Value::Bytes(key_gen(&seed).1.to_bytes().to_vec()),
            None => Value::Null,
        };
        assert_eq!(output, case.output, "{}", case.name);
    }
}

#[test]
fn sign_matches_ethlib() {
    // A key is generated once per seed: generation builds the whole top tree.
    let mut keys: HashMap<SecretKey, LeanXmssExpandedSecretKey> = HashMap::new();
    for case in cases("sign") {
        let leaf_index = LeafIndex::try_from(int(&case, "leaf_index")).expect("a 32-bit leaf index");
        let output = match (
            exact::<SECRET_KEY_LEN>(case.bytes("seed")),
            exact::<MESSAGE_LEN>(case.bytes("message")),
        ) {
            (Some(seed), Some(message)) => {
                let sk = keys.entry(seed).or_insert_with(|| key_gen(&seed).0);
                Value::Bytes(sign(sk, &message, leaf_index).to_bytes().to_vec())
            }
            _ => Value::Null,
        };
        assert_eq!(output, case.output, "{}", case.name);
    }
}

#[test]
fn signature_index_matches_ethlib() {
    for case in cases("signature_index") {
        let output = match exact::<SIG_SIZE>(case.bytes("signature")) {
            Some(sig) => Value::Int(u64::from(LeanXmssSignature::from_bytes(&sig).leaf_index())),
            None => Value::Null,
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
                &LeanXmssPublicKey::from_bytes(&pk),
                &message,
                &LeanXmssSignature::from_bytes(&sig),
            )),
            _ => Value::Null,
        };
        assert_eq!(output, case.output, "{}", case.name);
    }
}
