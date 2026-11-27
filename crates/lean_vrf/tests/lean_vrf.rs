use std::ops::Range;

use lean_vrf::*;

fn seed() -> [u8; 32] {
    keccak256::hash(b"leanxmss vrf test")
}

fn hex(bytes: &[u8]) -> String {
    bytes.iter().map(|byte| format!("{byte:02x}")).collect()
}

const HIGH: u32 = (1 << 31) - 3000;

/// Ranges that do and do not start at zero or end at a power of two, low and high in the tree, and one
/// that ends at `2^31`.
const RANGES: [Range<u32>; 8] = [
    0..1,
    0..1024,
    5..6,
    3..1000,
    700..1701,
    1023..1025,
    HIGH..HIGH + 2000,
    (1 << 31) - 5..1 << 31,
];
const ROOTS: [&str; 8] = [
    "a642d9ee60c7f8f63e57df2c93caf0a7644e611311e534f800254039c0a324c2",
    "74f00d092cb667bd3ebc3ca8d1c32f902bdef39eb0bbaff2bc07e119142aedc1",
    "d2b0026ddf95eebe4a37660ccd1f7d089b573dbe4e348b6addf08bde1bc886f6",
    "6fd3d4c73573774044def0e5399b7c4340d43175a600f578a3042d17448100c0",
    "e870a61f65ce148b9c46ed0694fee8c5c042a27b0e3d7234bfcca3ec5198142f",
    "232652ab99dc9a5ab82bb1d8d36c0840d033c84b198f3725e01023e7dda1aee6",
    "de9cb110436d10e78d34af89ab3e3bec5133e62f9104ab35746ff926d5254be9",
    "40b1326b90b44a5d63b0117a81025f1bdcc6cade43ad1af3adba58867b6f2ab7",
];

/// A range of many 512-slot cached nodes, partial at both ends: its root, and proofs at its ends
/// and either side of the boundaries between a partial and a whole node and between two whole ones.
#[test]
fn vrf_many_cached_nodes() {
    let slots = 12_345..162_345;
    let key = VrfKey::new(seed(), slots.clone()).unwrap();
    let root = key.root();
    assert_eq!(
        hex(&root),
        "b2a20b8e5d0a0b5ef079f5d0a73e64a46ce8c8970d8de1c06bfcd80dd6e73b55"
    );
    for slot in [slots.start, 12_799, 12_800, 51_199, 51_200, slots.end - 1] {
        assert!(
            verify_vrf_proof(&root, slot.into(), &key.proof(slot).unwrap()),
            "slot {slot}"
        );
    }
}

/// Every slot of each range opens under the root, and no slot outside it has a proof.
#[test]
fn vrf_ranges() {
    for (slots, expected) in RANGES.into_iter().zip(ROOTS) {
        let key = VrfKey::new(seed(), slots.clone()).unwrap();
        let root = key.root();
        assert_eq!(hex(&root), expected, "{slots:?}");
        for slot in slots.clone() {
            assert!(
                verify_vrf_proof(&root, slot.into(), &key.proof(slot).unwrap()),
                "{slots:?}, slot {slot}"
            );
        }
        assert!(key.proof(slots.start.wrapping_sub(1)).is_none() && key.proof(slots.end).is_none());
    }
}

#[test]
fn vrf_bounds() {
    assert!(VrfKey::new(seed(), 0..(1 << 31) + 1).is_none());
    assert!(VrfKey::new(seed(), 5..5).is_none());
    let key = VrfKey::new(seed(), 0..16).unwrap();
    let proof = key.proof(9).unwrap();
    assert!(verify_vrf_proof(&key.root(), 9, &proof));
    assert!(!verify_vrf_proof(&key.root(), 10, &proof));
    // The leaf commits to the whole slot, not only to the 31 bits that choose its path.
    assert!(!verify_vrf_proof(&key.root(), 9 + (1 << 31), &proof));
}

/// A key rebuilt from its cache has the same root, cache and proofs; a malformed cache, a wrong
/// root and a wrong seed are refused, and no cache holds a secret.
#[test]
fn vrf_cache_bytes() {
    for (slots, expected) in RANGES.into_iter().zip(ROOTS) {
        let built = VrfKey::new(seed(), slots.clone()).unwrap();
        let (cache, root) = (built.cache_to_bytes(), built.root());
        let secret = built.proof(slots.start).unwrap()[0];
        assert!(
            !cache.windows(32).any(|window| window == secret),
            "{slots:?}: the cache holds a secret"
        );

        let key = VrfKey::from_cache_bytes(seed(), &root, &cache).unwrap();
        assert_eq!(hex(&key.root()), expected, "{slots:?}");
        assert_eq!(key.cache_to_bytes(), cache);
        assert_eq!(key.proof(slots.start), built.proof(slots.start));

        assert!(VrfKey::from_cache_bytes(seed(), &[0; 32], &cache).is_none());
        assert!(VrfKey::from_cache_bytes([0; 32], &root, &cache).is_none());
        assert!(VrfKey::from_cache_bytes(seed(), &root, &cache[..cache.len() - 1]).is_none());
        assert!(VrfKey::from_cache_bytes(seed(), &root, &[&cache[..], &[0; 32]].concat()).is_none());
        // Ranges with as many cached nodes, which the root alone does not tell apart.
        for (start, end) in [
            (slots.start.wrapping_sub(1), slots.end),
            (slots.start + 1, slots.end),
            (slots.start, slots.end - 1),
            (slots.start, slots.end + 1),
        ] {
            let wrong_range = [&start.to_le_bytes(), &end.to_le_bytes(), &cache[8..]].concat();
            assert!(
                VrfKey::from_cache_bytes(seed(), &root, &wrong_range).is_none(),
                "{slots:?} loaded as {start}..{end}"
            );
        }
    }
}
