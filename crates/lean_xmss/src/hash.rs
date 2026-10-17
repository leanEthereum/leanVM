//! The tweakable hash `Th(P, A, M) = Truncate_n(BLAKE2s(P | A | M))` and its
//! address, laid out as leanSPHINCS lays them out (`crates/sphincs`), with the same
//! type codes, so the recursion guest builds both schemes' addresses alike. A chain
//! step is the exception: its address leaves out the chain index, which follows the
//! value instead (`wots::chain`), so a key's chains share their step addresses.
//!
//! The two layers share one public parameter, so the address separates them: the
//! top layer sets [`TOP`] in `hi`. A bottom address's `lo` is the leaf index, or a
//! node's index `leaf_index >> level`, which also separates the bottom trees; a top
//! address's is the top tree's own.

use primitives::hash::Hasher;

use crate::*;

pub const ADDRESS_LEN: usize = 16;

// Hash types (the low five bits of the address's last field byte).
pub const TWEAK_PRF: u8 = 0;
pub const TWEAK_CHAIN: u8 = 1;
pub const TWEAK_LEAF: u8 = 2;
pub const TWEAK_NODE: u8 = 3;
pub const TWEAK_PARAMETER: u8 = 5;
pub const TWEAK_RANDOMIZER: u8 = 7;
pub const TWEAK_MSG: u8 = 12;
/// A node outside a mock key's range.
pub const TWEAK_FILLER: u8 = 13;

/// The top layer's flag in `hi`.
pub const TOP: u32 = 1 << 23;

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

/// `hi` for `field` on layer `layer` (0 the bottom, 1 the top).
pub fn layer_hi(layer: usize, field: u32) -> u32 {
    field | (layer as u32 * TOP)
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
pub fn th_pair(pp: &PublicParam, tw: &Tweak, seed: &Seed) -> [Digest; 2] {
    let output = hasher(pp, tw).update(seed).finalize();
    [output[..N].try_into().unwrap(), output[N..].try_into().unwrap()]
}

/// `Th` over a concatenation of digests: a Merkle node, a one-time leaf.
pub fn th_digests(pp: &PublicParam, tw: &Tweak, values: &[Digest]) -> Digest {
    truncate(hasher(pp, tw).update(values.as_flattened()).finalize())
}
