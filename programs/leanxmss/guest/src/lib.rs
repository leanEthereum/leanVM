//! leanXMSS: WOTS with a target-sum encoding, under a Merkle tree of `2^32` one-time keys.
//!
//! The generalized XMSS of [DKKW25] (Constructions 3 and 6), with 16-byte digests as in SLH-DSA.
//!
//! The target sum fixes the verifier's work: every valid signature costs the same hashes.
//!
//! Every hash is standard BLAKE2s of `tweak | public_param | payload`, cut to 16 bytes.
//!
//! The tweak names the call site, so no two hash calls share a function.
//!
//! Values are little-endian 64-bit words, whose bytes are the specification's.
//!
//! The machine loads a word in one instruction, and a byte-aligned value in eight.
//!
//! Signatures, public keys and verification are the [XMSS specification]'s, byte for byte.
//!
//! Key generation is not: it makes keys for one leaf index, whose other tree nodes are fillers.
//!
//! [DKKW25]: https://eprint.iacr.org/2025/055
//! [XMSS specification]: https://github.com/leanEthereum/leanVM/releases/download/doc-latest/XMSS.pdf
#![no_std]

mod sign;

pub use sign::{SecretKey, SignError, key_gen};

use leanvm_guest::Blake2s;

/// A hash value: 128 bits.
pub type Digest = [u64; 2];
/// The per-key public parameter, which separates users' hash functions.
pub type PublicParam = [u64; 2];
/// The per-signature randomness the message is encoded under: 192 bits.
pub type Randomness = [u64; 3];
/// The message to sign: a 256-bit message hash.
pub type Message = [u64; 4];
/// The Merkle leaf, and so the one-time key, a signature uses: each leaf index signs at most one message.
pub type LeafIndex = u32;

/// `v`: hash chains, one per encoding digit.
pub const V: usize = 42;
/// `w`: bits per digit.
pub const W: usize = 3;
/// Values on one chain: a chain has 7 steps.
pub const CHAIN_LENGTH: usize = 1 << W;
/// Chain steps a verifier walks in all, fixed by the target sum.
pub const NUM_CHAIN_HASHES: usize = 99;
/// What the digits of every valid encoding sum to: 195.
///
/// Above the mean 147, so a verifier walks fewer steps than a signer.
pub const TARGET_SUM: usize = V * (CHAIN_LENGTH - 1) - NUM_CHAIN_HASHES;
/// Merkle tree height: a key covers `2^32` leaf indices.
pub const LOG_LIFETIME: usize = 32;

/// Serialized public key: `merkle_root | public_param`.
pub const PUB_KEY_SIZE: usize = size_of::<PublicKey>();
/// Serialized signature: `chain_tips | randomness | merkle_proof`.
pub const SIG_SIZE: usize = size_of::<Signature>();

// The digest's 128 bits are the 42 digits and one pinned top bit per 64-bit half.
const _: () = assert!(V * W + 2 == 8 * size_of::<Digest>());
const _: () = assert!(PUB_KEY_SIZE == 32 && SIG_SIZE == 1208);

/// Byte 0 of every tweak: 0 for leanXMSS, so none of its hashes is a leanSPHINCS one.
const PROTOCOL_DOMAIN_SEP: u8 = 0;

// Tweak types, byte 1 of a tweak.
const TWEAK_PRF: u8 = 0;
const TWEAK_CHAIN: u8 = 1;
const TWEAK_WOTS_PK: u8 = 2;
const TWEAK_MERKLE: u8 = 3;
const TWEAK_ENCODING: u8 = 4;
const TWEAK_PARAMETER: u8 = 5;
const TWEAK_FILLER: u8 = 6;
const TWEAK_RANDOMIZER: u8 = 7;

/// A public key.
///
/// Its fields are words, so it has no padding and any 32 bytes are one.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(C)]
pub struct PublicKey {
    /// The root of the tree of one-time keys.
    pub merkle_root: Digest,
    /// The parameter every hash of the key is taken under.
    pub public_param: PublicParam,
}

/// A signature: a WOTS signature and the authentication path of its one-time key.
///
/// Its fields are words, so it has no padding and any 1208 bytes are one.
#[derive(Clone, Debug, PartialEq, Eq)]
#[repr(C)]
pub struct Signature {
    /// Chain `i` opened at the message's digit `i`.
    pub chain_tips: [Digest; V],
    /// What the message is encoded under, ground by the signer until the encoding is valid.
    pub randomness: Randomness,
    /// The sibling at each level, leaf first.
    pub merkle_proof: [Digest; LOG_LIFETIME],
}

/// Why a signature is rejected.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum VerifyError {
    /// The randomness gives the message no valid encoding.
    InvalidEncoding,
    /// The recovered one-time key does not reach the root.
    InvalidMerklePath,
}

/// Check a signature on a message at a leaf index: 133 hash calls, 144 compressions.
///
/// ```text
///   calls  compressions
///   1      2              encode the message
///   99     99             walk each chain from its digit to its end
///   1      11             hash the chain ends into the leaf
///   32     32             fold the leaf up the tree
/// ```
pub fn verify(
    pk: &PublicKey,
    leaf_index: LeafIndex,
    message: &Message,
    signature: &Signature,
) -> Result<(), VerifyError> {
    let pp = &pk.public_param;
    // The digits say where each chain was opened.
    let digits = encode(pp, leaf_index, message, &signature.randomness).ok_or(VerifyError::InvalidEncoding)?;
    // Walk each chain the rest of the way: chain `i` from value `digit_i` to value 7.
    let ends = core::array::from_fn(|i| {
        let start = digits[i] as usize;
        chain(
            pp,
            leaf_index,
            i,
            start,
            CHAIN_LENGTH - 1 - start,
            signature.chain_tips[i],
        )
    });
    // The chain ends are the one-time public key: its leaf, folded up to the root.
    let root = merkle_root(
        pp,
        leaf_index,
        wots_leaf(pp, leaf_index, &ends),
        &signature.merkle_proof,
    );
    if root == pk.merkle_root {
        Ok(())
    } else {
        Err(VerifyError::InvalidMerklePath)
    }
}

/// A tweak as two words.
///
/// ```text
///   bytes  0      1     2      3     4..8      8..12  12..16
///          domain type  layer  zero  position  tree   index
/// ```
///
/// XMSS leaves `layer` and `tree` zero.
fn tweak(ty: u8, position: u32, index: u32) -> [u64; 2] {
    [
        u64::from(PROTOCOL_DOMAIN_SEP) | u64::from(ty) << 8 | u64::from(position) << 32,
        u64::from(index) << 32,
    ]
}

/// BLAKE2s of `tweak | pp | payload`, cut to a digest.
///
/// Inlined with its length known, a call folds to the words it hashes and the compressions.
#[inline(always)]
fn tweak_hash<const N: usize>(pp: &PublicParam, ty: u8, position: u32, index: u32, payload: &[u64; N]) -> Digest {
    let mut hasher = Blake2s::new();
    hasher
        .update_words(&tweak(ty, position, index))
        .update_words(pp)
        .update_words(payload);
    // A digest is the first 16 bytes of the 32.
    let digest = hasher.finalize_words();
    [digest[0], digest[1]]
}

/// The target-sum encoding: the message's 42 digits, or `None` if they are not valid.
///
/// The encoding digest is two words of 21 three-bit digits each.
///
/// It is valid iff each word's top bit is zero and the digits sum to 195.
fn encode(pp: &PublicParam, leaf_index: LeafIndex, message: &Message, randomness: &Randomness) -> Option<[u8; V]> {
    // The payload is `message | randomness | zeros`: 64 bytes, so two compressions in all.
    let [m0, m1, m2, m3] = *message;
    let [r0, r1, r2] = *randomness;
    let digest = tweak_hash(pp, TWEAK_ENCODING, 0, leaf_index, &[m0, m1, m2, m3, r0, r1, r2, 0]);

    let mut digits = [0; V];
    let mut sum = 0;
    for (half, word) in digest.into_iter().enumerate() {
        // Bits 0..63 are 21 digits, bit 63 is pinned to zero.
        //
        // Why pinned: with it, the digits determine the word.
        if word >> (W * V / 2) != 0 {
            return None;
        }
        // Digit `i` of the half is bits `3i..3i+3`.
        for i in 0..V / 2 {
            let digit = (word >> (W * i)) as u8 & (CHAIN_LENGTH as u8 - 1);
            digits[half * V / 2 + i] = digit;
            sum += digit as usize;
        }
    }
    (sum == TARGET_SUM).then_some(digits)
}

/// Walk chain `i` for `steps` steps from value number `start`.
///
/// The step out of value `s` is hashed at position `8i + s`, so no two steps share a tweak.
fn chain(pp: &PublicParam, leaf_index: LeafIndex, i: usize, start: usize, steps: usize, value: Digest) -> Digest {
    (start..start + steps).fold(value, |value, s| {
        tweak_hash(pp, TWEAK_CHAIN, (i * CHAIN_LENGTH + s) as u32, leaf_index, &value)
    })
}

/// The Merkle leaf of a one-time key: its 42 chain ends in one hash, 11 compressions.
fn wots_leaf(pp: &PublicParam, leaf_index: LeafIndex, ends: &[Digest; V]) -> Digest {
    tweak_hash::<{ 2 * V }>(
        pp,
        TWEAK_WOTS_PK,
        0,
        leaf_index,
        ends.as_flattened().try_into().unwrap(),
    )
}

/// The parent at a level, the leaves being level 0, and an index within it.
fn merkle_node(pp: &PublicParam, level: usize, index: u64, left: &Digest, right: &Digest) -> Digest {
    // Both children fill one block with the tweak and the parameter: one compression.
    tweak_hash(
        pp,
        TWEAK_MERKLE,
        level as u32,
        index as u32,
        &[left[0], left[1], right[0], right[1]],
    )
}

/// Fold a leaf, at index `leaf_index`, up its authentication path.
fn merkle_root(pp: &PublicParam, leaf_index: LeafIndex, leaf: Digest, path: &[Digest; LOG_LIFETIME]) -> Digest {
    path.iter().enumerate().fold(leaf, |node, (level, sibling)| {
        // The node's index at this level: its low bit says which child it is.
        let index = u64::from(leaf_index) >> level;
        let (left, right) = if index & 1 == 0 {
            (&node, sibling)
        } else {
            (sibling, &node)
        };
        merkle_node(pp, level + 1, index >> 1, left, right)
    })
}
