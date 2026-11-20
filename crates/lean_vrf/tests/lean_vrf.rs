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
    "5d43cb6bf6e3b7e305053fa3a0ff56dd6d1c0eeac6e2b2ee59c3be2605028054",
    "c90b187e2d1984a093092e92c7982419757473f602971cdf26a661d7bd724fb2",
    "2b6899e17ab21595a51398deb188d6aac2a1da59c76cd232560176a36462817c",
    "703c3ca172c5433067149861f1f411c1a00d5dea6ebdb721902027defc8c96bb",
    "bbe357f5b683095456513e38b7dca8f7546383ea973bff7c8e17bb4bbb5babed",
    "61a322fb9027ad56d3c46aeddb3d8a24e36c4eaa48842b0df1781050c0d972d8",
    "46e50f866a7fe18e81b40ad87c0a06d79ba60e7fb82f7c86e12536ab97e6a546",
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
