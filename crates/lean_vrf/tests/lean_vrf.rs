use std::ops::Range;

use lean_vrf::*;

fn seed() -> [u8; 32] {
    keccak256::hash(b"leanxmss vrf test")
}

fn hex(bytes: &[u8]) -> String {
    bytes.iter().map(|byte| format!("{byte:02x}")).collect()
}

const HIGH: u32 = (1 << 31) - 3000;

/// Ranges that do and do not start at zero or end at a power of two, low and high in the tree.
const RANGES: [Range<u32>; 7] = [0..1, 0..1024, 5..6, 3..1000, 700..1701, 1023..1025, HIGH..HIGH + 2000];
const ROOTS: [&str; 7] = [
    "1c12fd39b5b356060c926e711c4888c14d402943252baf8d67fc33977ef8e0fd",
    "e050b497244e9721d5a75c9307251c584268c48dea722a55faeee46daf408590",
    "24541e0748c0adb26ac4397eff0dd249df326e9059a848d5e0fa7b911feaaa25",
    "ca635576797ef7c55943417d1dd9903ffdf34cafad3d5a97b6992a82755d7d03",
    "b8be99ea7b2e970afb79627735de036a5ff4c567b37dfcaa23c71a72fdc16366",
    "a38f5578b21bc431a6059162c7451ad1e298db4c765907dc168c9b20cb482908",
    "14d1137999ab81416606d9aecbc906f631415dd450f0b43ec6b35dee4d6ef754",
];

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
    assert!(verify_vrf_proof(&key.root(), 9 + (1 << 31), &proof));
    assert!(!verify_vrf_proof(&key.root(), 10, &proof));
}

/// A key rebuilt from its cache has the same root, cache and proofs; a malformed cache, a wrong
/// root and a wrong seed are refused, and no cache holds a leaf.
#[test]
fn vrf_cache_bytes() {
    for (slots, expected) in RANGES.into_iter().zip(ROOTS) {
        let built = VrfKey::new(seed(), slots.clone()).unwrap();
        let (cache, root) = (built.cache_to_bytes(), built.root());
        let leaf = built.proof(slots.start).unwrap()[0];
        assert!(
            !cache.windows(32).any(|window| window == leaf),
            "{slots:?}: the cache holds a leaf"
        );

        let key = VrfKey::from_cache_bytes(seed(), &cache, &root).unwrap();
        assert_eq!(hex(&key.root()), expected, "{slots:?}");
        assert_eq!(key.cache_to_bytes(), cache);
        assert_eq!(key.proof(slots.start), built.proof(slots.start));

        assert!(VrfKey::from_cache_bytes(seed(), &cache, &[0; 32]).is_none());
        assert!(VrfKey::from_cache_bytes([0; 32], &cache, &root).is_none());
        assert!(VrfKey::from_cache_bytes(seed(), &cache[..cache.len() - 1], &root).is_none());
        assert!(VrfKey::from_cache_bytes(seed(), &[&cache[..], &[0; 32]].concat(), &root).is_none());
        let mut wrong_range = cache.clone();
        wrong_range[4..8].copy_from_slice(&(slots.end + (1 << 20)).to_le_bytes());
        assert!(VrfKey::from_cache_bytes(seed(), &wrong_range, &root).is_none());
    }
}
