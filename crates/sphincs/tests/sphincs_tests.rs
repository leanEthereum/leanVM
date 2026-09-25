use rand::{SeedableRng, rngs::StdRng};
use sphincs::*;

fn hex_bytes(hex: &str) -> Vec<u8> {
    let hex = hex.trim().trim_start_matches("0x");
    (0..hex.len() / 2)
        .map(|i| u8::from_str_radix(&hex[2 * i..2 * i + 2], 16).unwrap())
        .collect()
}

/// The string value of `"key": "…"` in the vector file.
fn field(json: &str, key: &str) -> Vec<u8> {
    let at = json.find(&format!("\"{key}\"")).unwrap();
    let rest = &json[at + key.len() + 2..];
    let open = rest.find('"').unwrap() + 1;
    let close = open + rest[open..].find('"').unwrap();
    hex_bytes(&rest[open..close])
}

/// NiceTry's reference vector (Post-Quantum-AA-Infra 67b04de,
/// `test/vectors/sphincs-v2-reference-0.json`, written by
/// `scripts/sphincs_v2_reference.py` and accepted by `SphincsVerifier_v2` in
/// `test/SphincsVerifier_v2.t.sol`). It verifies here, and the same seeds
/// (`SK.seed = 0x11…`, `SK.prf = 0x22…`, `PK.seed = 0x5eed…`) reproduce the key and
/// the signature byte for byte.
#[test]
fn matches_the_reference_vector() {
    let json = include_str!("vectors/sphincs-v2-reference-0.json");
    let (pk_seed, pk_root) = (field(json, "pkSeed"), field(json, "pkRoot"));
    assert_eq!((&pk_seed[N..], &pk_root[N..]), (&[0; N][..], &[0; N][..]));
    let pk = SphincsPublicKey {
        root: pk_root[..N].try_into().unwrap(),
        public_param: pk_seed[..N].try_into().unwrap(),
    };
    let message: Message = field(json, "message").try_into().unwrap();
    let blob = field(json, "signature");
    assert_eq!(blob.len(), SIG_SIZE);
    let reference = SphincsSignature::from_bytes(blob.as_slice().try_into().unwrap());
    assert_eq!(reference.to_bytes().to_vec(), blob);
    verify(&pk, &message, &reference).unwrap();

    let mut other = message;
    other[31] ^= 1;
    assert_eq!(verify(&pk, &other, &reference), Err(SphincsVerifyError::RootMismatch));

    let (derived, signature) = sign_with_seeds([0x11; N], [0x22; N], pk.public_param, &message);
    assert_eq!(derived, pk);
    assert_eq!(signature, reference);
}

#[test]
fn keygen_sign_verify_roundtrip() {
    let (sk, pk) = key_gen(&mut StdRng::seed_from_u64(1));
    assert_eq!(sk.public_key(), pk);
    for message in [[0xA7; MESSAGE_LEN], [0; MESSAGE_LEN]] {
        let signature = sign(&sk, &message);
        verify(&pk, &message, &signature).unwrap();
        assert_eq!(sign(&sk, &message), signature);
        let bytes = signature.to_bytes();
        assert_eq!(SphincsSignature::from_bytes(&bytes), signature);
    }
    assert_eq!(SphincsPublicKey::from_bytes(&pk.flatten()), pk);
    let (seed_word, root_word) = pk.to_bytes32();
    assert_eq!((&seed_word[N..], &root_word[N..]), (&[0; N][..], &[0; N][..]));
    assert_eq!(sk.to_bytes().len(), MASTER_SECRET_LEN);
    assert_eq!(SphincsSecretKey::from_bytes(&sk.to_bytes()).public_key(), pk);
    assert_eq!(
        key_gen_from_seed([3; MASTER_SECRET_LEN]).1,
        key_gen_from_seed([3; MASTER_SECRET_LEN]).1
    );
}

#[test]
fn trace_matches_the_signature() {
    let (sk, pk) = key_gen_from_seed([7; MASTER_SECRET_LEN]);
    let message = [0x5A; MESSAGE_LEN];
    let signature = sign(&sk, &message);
    let trace = verify_trace(&pk, &message, &signature);
    assert_eq!(trace.signed[D], pk.root);
    assert_eq!(
        trace.digest,
        h_msg(&pk.public_param, &pk.root, &signature.randomizer, &message)
    );
    for digits in &trace.digits {
        let sum: usize = digits[..LEN1].iter().map(|&d| usize::from(d)).sum();
        let csum: usize = (0..LEN2)
            .map(|j| usize::from(digits[LEN1 + j]) << (LOG_W * (LEN2 - 1 - j)))
            .sum();
        assert_eq!(sum + csum, MAX_CSUM);
    }
}

#[test]
fn tampered_signatures_rejected() {
    let (sk, pk) = key_gen_from_seed([9; MASTER_SECRET_LEN]);
    let message = [0x33; MESSAGE_LEN];
    let signature = sign(&sk, &message);
    verify(&pk, &message, &signature).unwrap();

    let mut other_key = pk;
    other_key.root[0] ^= 1;
    assert!(verify(&other_key, &message, &signature).is_err());
    let mut other_key = pk;
    other_key.public_param[15] ^= 1;
    assert!(verify(&other_key, &message, &signature).is_err());

    for tamper in [
        (|s: &mut SphincsSignature| s.randomizer[0] ^= 1) as fn(&mut SphincsSignature),
        |s: &mut SphincsSignature| s.fors_secrets[3][0] ^= 1,
        |s: &mut SphincsSignature| s.fors_paths[K - 1][A - 1][0] ^= 1,
        |s: &mut SphincsSignature| s.layers[0].chains[17][0] ^= 1,
        |s: &mut SphincsSignature| s.layers[2].chains[L - 1][9] ^= 1,
        |s: &mut SphincsSignature| s.layers[D - 1].path[SUBTREE_H - 1][15] ^= 1,
    ] {
        let mut tampered = signature.clone();
        tamper(&mut tampered);
        assert_eq!(verify(&pk, &message, &tampered), Err(SphincsVerifyError::RootMismatch));
    }
}

/// The digest's bit fields are the verifier's `shr`/`and` on a big-endian
/// `uint256`, and the address is FIPS 205's big-endian layout.
#[test]
fn digest_fields_and_address_layout() {
    let mut d = [0u8; 32];
    d[31] = 0xA5;
    d[30] = 0x3C;
    assert_eq!(digest_bits(&d, 0, 4), 0x5);
    assert_eq!(digest_bits(&d, 4, 4), 0xA);
    assert_eq!(digest_bits(&d, 8, 4), 0xC);
    assert_eq!(digest_bits(&d, 0, 9), 0x0A5);
    let mut top = [0u8; 32];
    top[0] = 0x80;
    assert_eq!(digest_bits(&top, 255, 1), 1);
    assert_eq!(
        Adrs::new(1, 0x0203, TREE, 4, 5, 6).to_bytes(),
        [
            0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 3, 0, 0, 0, 2, 0, 0, 0, 4, 0, 0, 0, 5, 0, 0, 0, 6
        ]
    );
}
