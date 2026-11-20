//! VRF keys and proofs.

use std::fmt::Write;

use lean_pq::vrf::{verify, Key};
use lean_pq::Error;

#[test]
fn proofs_open_under_the_root_and_nowhere_else() {
    let key = Key::new([1; 32], 10..20).unwrap();
    let root = key.root();
    for slot in 10..20 {
        let proof = key.proof(slot).unwrap();
        verify(&root, slot.into(), &proof).unwrap();
        let next = u64::from(slot) + 1;
        assert_eq!(
            verify(&root, next, &proof),
            Err(Error::VrfVerify { slot: next })
        );
    }
}

/// The root every binding's tests pin.
#[test]
fn shared_vector() {
    let key = Key::new([9; 32], 100..200).unwrap();
    let root = key.root().iter().fold(String::new(), |mut hex, byte| {
        write!(hex, "{byte:02x}").unwrap();
        hex
    });
    assert_eq!(
        root,
        "c7e3eaa5a1af5e528e56beb589b4d1c579f5fb8939ddd7f6b1ce2141bc096b45"
    );
}

#[test]
fn rejects_bad_ranges_and_slots_outside_the_range() {
    assert_eq!(
        Key::new([1; 32], 5..5).unwrap_err(),
        Error::InvalidVrfRange { start: 5, end: 5 }
    );
    let key = Key::new([1; 32], 10..20).unwrap();
    assert_eq!(key.proof(20).unwrap_err(), Error::VrfSlot { slot: 20 });
    assert_eq!(key.proof(9).unwrap_err(), Error::VrfSlot { slot: 9 });
}

#[test]
fn loads_from_its_cache() {
    let key = Key::new([9; 32], 100..200).unwrap();
    let cache = key.cache_to_bytes();
    let loaded = Key::from_cache_bytes([9; 32], &key.root(), &cache).unwrap();
    assert_eq!(loaded.proof(150).unwrap(), key.proof(150).unwrap());
    assert_eq!(
        Key::from_cache_bytes([9; 32], &key.root(), &cache[1..]).unwrap_err(),
        Error::InvalidVrfCache
    );
    assert!(Key::from_cache_bytes([9; 32], &[0; 32], &cache).is_err());
}
