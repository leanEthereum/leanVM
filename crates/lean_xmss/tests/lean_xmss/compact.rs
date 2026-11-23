use std::sync::OnceLock;

use lean_xmss::internals::*;
use lean_xmss::*;

const SEED: SecretKey = [1; SECRET_KEY_LEN];
const SLOT_LEAVES: LeafIndex = (1 << 15) + (1 << 29) + (1 << 30);

fn key() -> &'static (LeanXmssExpandedSecretKey, LeanXmssPublicKey) {
    static KEY: OnceLock<(LeanXmssExpandedSecretKey, LeanXmssPublicKey)> = OnceLock::new();
    KEY.get_or_init(|| key_gen(&SEED))
}

fn message() -> Message {
    std::array::from_fn(|i| (i * 3 + 7) as u8)
}

fn assert_same(state: &LeanXmssCompactState) {
    let (sk, pk) = key();
    let signature = sign_compact(&SEED, state, &message());
    assert_eq!(signature, sign(sk, &message(), state.leaf_index()));
    assert!(verify(pk, &message(), &signature));
}

/// One leaf after the other, as attestations use them, from the middle of a tree.
#[test]
fn compact_consecutive_leaves() {
    let (sk, pk) = key();
    let mut state = sk.compact_state(1 << 15);
    assert_eq!(state.public_key(&SEED), Some(*pk));
    assert_same(&state);
    for _ in 0..70 {
        state = state.advance(&SEED, state.leaf_index() + 1).unwrap();
        assert_same(&state);
    }
}

/// Jumps of thousands of leaves, as a proposer's slots are apart, to the tree's last leaves.
#[test]
fn compact_jumps() {
    let (sk, _) = key();
    let mut state = sk.compact_state(SLOT_LEAVES);
    assert_same(&state);
    for slot in [997, 2003, 2999, 4001, 4095] {
        state = state.advance(&SEED, SLOT_LEAVES + slot * 8).unwrap();
        assert_same(&state);
    }
    assert_eq!(
        state.advance(&SEED, SLOT_LEAVES + 4096 * 8),
        None,
        "another bottom tree"
    );
}

/// Across the middle of a tree, where half of it is recomputed, and never back.
#[test]
fn compact_crosses_the_half_and_never_goes_back() {
    let (sk, _) = key();
    let state = sk.compact_state((1 << 15) - 1);
    let state = state.advance(&SEED, 1 << 15).unwrap();
    assert_same(&state);
    assert_eq!(state.advance(&SEED, 12345), None);
    assert_eq!(state.advance(&SEED, 1 << 15).as_ref(), Some(&state));
}

/// The encoding, pinned to the bytes go-leanxmss gives for the same seed and leaf.
#[test]
fn compact_encoding() {
    let hex = |bytes: &[u8]| bytes.iter().map(|b| format!("{b:02x}")).collect::<String>();
    let (sk, pk) = key();
    let state = sk.compact_state((1 << 15) + 5);
    let bytes = state.to_bytes();
    assert_eq!(bytes[..4], ((1u32 << 15) + 5).to_le_bytes());
    assert_eq!(
        hex(&keccak256::hash(&bytes)),
        "c9979d311e6da0f883c030237aa0f12a59610f5fcd1b5c24fb2060765e12d4f4"
    );
    let decoded = LeanXmssCompactState::from_bytes(&bytes);
    assert_eq!(decoded, state);
    assert_eq!(decoded.public_key(&SEED), Some(*pk));
    assert_same(&decoded.advance(&SEED, (1 << 15) + 900).unwrap());
    let mut wrong = bytes;
    wrong[4 + LAYER_HEIGHT * N] ^= 1;
    assert_ne!(LeanXmssCompactState::from_bytes(&wrong).public_key(&SEED), Some(*pk));
}
