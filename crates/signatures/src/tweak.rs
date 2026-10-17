//! What the two schemes share: the tweakable hash
//! `Th(P, A, M) = Truncate_n(BLAKE2s(P | A | M))`, its address and the address
//! types, so the recursion guest builds both schemes' addresses alike.
//!
//! The public parameter and the address are 16 bytes each, as every value hashed
//! after them is: a chain step and a Merkle node are one compression, and a prover
//! whose words are 16 bytes never has to cut a value in two.

use primitives::hash::Hasher;

/// `n`: hash value and Merkle node length, in bytes.
pub const N: usize = 16;
pub type Digest = [u8; N];

pub const PUBLIC_PARAM_LEN: usize = 16;
pub type PublicParam = [u8; PUBLIC_PARAM_LEN];

pub const ADDRESS_LEN: usize = 16;

// Hash types (the low five bits of the address's last field byte); each scheme adds
// its own.
pub const TWEAK_PRF: u8 = 0;
pub const TWEAK_CHAIN: u8 = 1;
pub const TWEAK_LEAF: u8 = 2;
pub const TWEAK_NODE: u8 = 3;
pub const TWEAK_PARAMETER: u8 = 5;
pub const TWEAK_RANDOMIZER: u8 = 7;
pub const TWEAK_MSG: u8 = 12;

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

/// `Th` over a byte payload.
pub fn th(pp: &PublicParam, tw: &Tweak, payload: &[u8]) -> Digest {
    hasher(pp, tw).update(payload).finalize()[..N].try_into().unwrap()
}

/// `Th` over a concatenation of digests: a Merkle node, a leaf, a few-time key.
pub fn th_digests(pp: &PublicParam, tw: &Tweak, values: &[Digest]) -> Digest {
    th(pp, tw, values.as_flattened())
}

/// Two secrets for one hash: the two halves of the untruncated hash of the seed.
pub fn th_pair(pp: &PublicParam, tw: &Tweak, seed: &[u8; 32]) -> [Digest; 2] {
    let output = hasher(pp, tw).update(seed).finalize();
    [output[..N].try_into().unwrap(), output[N..].try_into().unwrap()]
}

/// The seed a scheme derives from: the hash of the scheme's `tag` then the key's
/// seed, so no two schemes derive from the same bytes.
pub fn tagged_seed(tag: &[u8], seed: &[u8; 32]) -> [u8; 32] {
    Hasher::new().update(tag).update(seed).finalize()
}

/// The public parameter, derived from the scheme's seed under `P = 0`.
pub fn public_param(seed: &[u8; 32]) -> PublicParam {
    th(&[0; PUBLIC_PARAM_LEN], &tweak(TWEAK_PARAMETER, 0, 0), seed)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn address_layout() {
        let tw = tweak(19, 0x123456, 0x89abcdef).step(5);
        assert_eq!(address(&tw)[..8], [0xef, 0xcd, 0xab, 0x89, 0x56, 0x34, 0x12, 0xb3]);
        assert_eq!(address(&tw)[8..], [0; 8]);
        let pp: PublicParam = std::array::from_fn(|i| i as u8 + 1);
        let payload = [9u8; N];
        let input = [&pp[..], &address(&tw), &payload].concat();
        assert_eq!(th(&pp, &tw, &payload)[..], primitives::hash::hash(&input)[..N]);
    }
}
