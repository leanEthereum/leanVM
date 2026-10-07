//! The tweakable hash `Th(P, A, M) = Truncate_n(BLAKE2s(P | A | M))`, and the
//! address that names one hash call in the whole structure.
//!
//! The public parameter and the address are 16 bytes each, as every value
//! hashed after them is: a chain step and a Merkle node are one compression,
//! and a prover whose words are 16 bytes never has to cut a value in two.

use primitives::hash::Hasher;

use crate::*;

pub const ADDRESS_LEN: usize = 16;

// Hash types (the low five bits of the address's last byte).
pub const TWEAK_PRF: u8 = 0;
pub const TWEAK_CHAIN: u8 = 1;
pub const TWEAK_LEAF: u8 = 2;
pub const TWEAK_NODE: u8 = 3;
pub const TWEAK_ENC: u8 = 4;
pub const TWEAK_PARAMETER: u8 = 5;
pub const TWEAK_RANDOMIZER: u8 = 7;
pub const TWEAK_MSG: u8 = 12;
/// A pruned key's surrogate siblings.
pub const TWEAK_SURROGATE: u8 = 13;
pub const TWEAK_FOREST_PRF: u8 = 14;
pub const TWEAK_FOREST_CHAIN: u8 = 15;
/// The leaf of a subtree: a small WOTS key's chain tops.
pub const TWEAK_FOREST_KEY_LEAF: u8 = 16;
pub const TWEAK_FOREST_SUBNODE: u8 = 17;
/// The leaf of a tree: the top nodes of its two subtrees.
pub const TWEAK_FOREST_TREE_LEAF: u8 = 18;
pub const TWEAK_FOREST_NODE: u8 = 19;
/// The few-time public key: the top nodes of the trees.
pub const TWEAK_FOREST_KEY: u8 = 20;

/// The address of a hash call: its type, a chain step, and two fields,
/// `hi < 2^24` and `lo`.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct Tweak {
    t: u8,
    step: u8,
    hi: u32,
    lo: u32,
}

pub fn tweak(t: u8, hi: u32, lo: u32) -> Tweak {
    debug_assert!(t < 32 && hi < 1 << 24);
    Tweak { t, step: 0, hi, lo }
}

impl Tweak {
    /// The same address at chain step `step < 8`.
    pub fn step(self, step: usize) -> Self {
        debug_assert!(step < 8);
        Self {
            step: step as u8,
            ..self
        }
    }
}

/// The 16 bytes that follow `P` in a hash input:
/// `[lo:4 | hi:3 | t + 32 step:1 | zero:8]`, the fields little endian.
pub fn address(tw: &Tweak) -> [u8; ADDRESS_LEN] {
    let mut out = [0u8; ADDRESS_LEN];
    out[..4].copy_from_slice(&tw.lo.to_le_bytes());
    out[4..7].copy_from_slice(&tw.hi.to_le_bytes()[..3]);
    out[7] = tw.t | tw.step << 5;
    out
}

/// Compressions BLAKE2s spends on a hash input whose payload is `payload` bytes.
pub const fn blocks(payload: usize) -> usize {
    (PUBLIC_PARAM_LEN + ADDRESS_LEN + payload).div_ceil(64)
}

/// A hasher that has absorbed `P | A`.
pub fn hasher(pp: &PublicParam, tw: &Tweak) -> Hasher {
    let mut hasher = Hasher::new();
    hasher.update(pp).update(&address(tw));
    hasher
}

fn truncate(output: [u8; 32]) -> Digest {
    output[..N].try_into().unwrap()
}

/// `Th` over a byte payload.
pub fn th(pp: &PublicParam, tw: &Tweak, payload: &[u8]) -> Digest {
    truncate(hasher(pp, tw).update(payload).finalize())
}

/// Two secrets for one hash: the two halves of the untruncated hash of the seed.
pub fn th_pair(pp: &PublicParam, tw: &Tweak, master: &MasterSecret) -> [Digest; 2] {
    let output = hasher(pp, tw).update(master).finalize();
    [output[..N].try_into().unwrap(), output[N..].try_into().unwrap()]
}

/// `Th` over a concatenation of digests: a Merkle node, a leaf, a few-time key.
pub fn th_digests(pp: &PublicParam, tw: &Tweak, values: &[Digest]) -> Digest {
    truncate(hasher(pp, tw).update(values.as_flattened()).finalize())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn address_layout() {
        let tw = tweak(TWEAK_FOREST_NODE, 0x123456, 0x89abcdef).step(5);
        assert_eq!(address(&tw)[..8], [0xef, 0xcd, 0xab, 0x89, 0x56, 0x34, 0x12, 0xb3]);
        assert_eq!(address(&tw)[8..], [0; 8]);
        let pp: PublicParam = std::array::from_fn(|i| i as u8 + 1);
        let payload = [9u8; N];
        let input = [&pp[..], &address(&tw), &payload].concat();
        assert_eq!(th(&pp, &tw, &payload)[..], primitives::hash::hash(&input)[..N]);
    }
}
