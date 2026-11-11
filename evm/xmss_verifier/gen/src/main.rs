//! Reference values for the Solidity leanXMSS verifier, from `crates/signatures`. Run with `--release`.
//!
//! - `trace` prints the intermediate values of verifying `verify_valid_first_leaf`, to compare against the Solidity.
//! - `fixture` writes `test/fixtures/registration.json`: an EIP-8483 add whose leanXMSS key signs, at leaf index 0,
//!   `M = keccak256(chain_id | bls_pubkey | xmss_public_key)`, the chain ID a 32-byte big-endian word.

use std::fs;
use std::path::Path;

use primitives::hash::hash;
use signatures::lean_xmss::*;

const VECTOR: &str = "../../../crates/signatures/tests/signatures/ethlib/xmss/verify/verify_valid_first_leaf/data.yaml";
const FIXTURE: &str = "../test/fixtures/registration.json";

/// The default of both `forge test` and anvil.
const CHAIN_ID: u64 = 31337;
/// BLS12-381's G1 generator, compressed: a valid BLS public key.
const BLS_PUBKEY: &str =
    "97f1d3a73197d7942695638c4fa9ac0fc3688c4f9774b905a14e3a3f171bac586c55e83ff97a1aeffb3af00adb22c6bb";
const SEED: Seed = *b"leanXMSS proof of possession key";

fn main() {
    match std::env::args().nth(1).as_deref() {
        Some("trace") => trace(),
        Some("fixture") => fixture(),
        _ => {
            eprintln!("usage: xmss-verifier-gen trace|fixture");
            std::process::exit(2);
        }
    }
}

fn trace() {
    let yaml = fs::read_to_string(Path::new(env!("CARGO_MANIFEST_DIR")).join(VECTOR)).unwrap();
    let [_, pk, _, message, _, signature, _] = yaml.split('\'').collect::<Vec<_>>()[..] else {
        panic!("unexpected data.yaml");
    };
    let pk = LeanXmssPublicKey::from_bytes(&unhex(pk).try_into().unwrap());
    let message: Message = unhex(message).try_into().unwrap();
    let signature = LeanXmssSignature::from_bytes(&unhex(signature).try_into().unwrap());
    verify(&pk, &message, &signature).expect("the vector verifies");

    let pp = pk.public_param();
    println!("leaf index {}", signature.leaf_index());
    let mut signed = message.to_vec();
    let layers = [("bottom", signature.bottom()), ("top", signature.top())];
    for (layer, (name, sig)) in layers.into_iter().enumerate() {
        let e = layer_index(signature.leaf_index(), layer);
        let digest = message_digest(pp, layer, e, sig.randomizer(), &signed);
        let (codeword, leaf) = wots_leaf(pp, layer, e, &signed, sig.randomizer(), sig.chain_values()).unwrap();
        let (_, root) = layer_root(pp, layer, e, &signed, sig, |_| {}).unwrap();
        println!("{name} e {e}");
        println!("{name} digest 0x{}", hex(&digest));
        let digits: String = codeword.iter().map(|&d| char::from(b'0' + d)).collect();
        println!("{name} codeword {digits}");
        println!("{name} leaf 0x{}", hex(&leaf));
        println!("{name} root 0x{}", hex(&root));
        signed = root.to_vec();
    }
}

fn fixture() {
    let bls_pubkey = unhex(BLS_PUBKEY);
    let (sk, pk) = key_gen_from_seed(SEED);
    let pk = pk.to_bytes();
    let vrf_root = hash(b"stand-in for the VRF root");
    let pq_data = [pk, vrf_root].concat();

    let mut chain_id = [0; 32];
    chain_id[24..].copy_from_slice(&CHAIN_ID.to_be_bytes());
    let message = hash(&[&chain_id[..], &bls_pubkey, &pk].concat());
    let signature = sign(&sk, &message, 0).unwrap().to_bytes();
    verify(
        &LeanXmssPublicKey::from_bytes(&pk),
        &message,
        &LeanXmssSignature::from_bytes(&signature),
    )
    .expect("the fixture verifies");

    let json = format!(
        "{{\n  \"chain_id\": {CHAIN_ID},\n  \"bls_pubkey\": \"0x{}\",\n  \"pq_data\": \"0x{}\",\n  \"message\": \"0x{}\",\n  \"signature\": \"0x{}\"\n}}\n",
        hex(&bls_pubkey),
        hex(&pq_data),
        hex(&message),
        hex(&signature),
    );
    fs::write(Path::new(env!("CARGO_MANIFEST_DIR")).join(FIXTURE), json).unwrap();
}

fn hex(bytes: &[u8]) -> String {
    bytes.iter().map(|b| format!("{b:02x}")).collect()
}

fn unhex(s: &str) -> Vec<u8> {
    let s = s.strip_prefix("0x").unwrap_or(s);
    (0..s.len())
        .step_by(2)
        .map(|i| u8::from_str_radix(&s[i..i + 2], 16).unwrap())
        .collect()
}
