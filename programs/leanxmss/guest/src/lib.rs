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

pub use sign::{SecretKey, XmssSignError, key_gen};

use leanvm_guest::{Blake2s, Template, hash_with};

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
#[derive(Clone, Copy, Debug, PartialEq, Eq, thiserror::Error)]
pub enum XmssVerifyError {
    /// The randomness gives the message no valid encoding.
    #[error("the randomness gives the message no valid encoding")]
    InvalidEncoding,
    /// The recovered one-time key does not reach the root.
    #[error("the recovered one-time key does not reach the root")]
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
) -> Result<(), XmssVerifyError> {
    let pp = &pk.public_param;
    // The digits say where each chain was opened.
    let digits = encode(pp, leaf_index, message, &signature.randomness).ok_or(XmssVerifyError::InvalidEncoding)?;
    // Walk each chain the rest of the way, chain `i` from value `digit_i` to value 7: its end is the leaf's. The leaf
    // takes the chains one by one, unrolled, so each digit's shift and each position are constants.
    let mut chains = Chains::new(pp, leaf_index);
    let leaf = wots_leaf(pp, leaf_index, |i| {
        chains.walk(i, digits.get(i)..CHAIN_LENGTH - 1, signature.chain_tips[i])
    });
    // The chain ends are the one-time public key: its leaf, folded up to the root.
    let root = merkle_root(pp, leaf_index, leaf, &signature.merkle_proof);
    if root == pk.merkle_root {
        Ok(())
    } else {
        Err(XmssVerifyError::InvalidMerklePath)
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
#[inline(always)]
fn tweak_hash<const N: usize>(pp: &PublicParam, ty: u8, position: u32, index: u32, payload: &[u64; N]) -> Digest {
    digest(hash_with(|message| {
        message.write(tweak(ty, position, index)).write(*pp).write(*payload);
    }))
}

/// A digest is the first 16 bytes of the 32.
#[inline(always)]
const fn digest([d0, d1, ..]: [u64; 4]) -> Digest {
    [d0, d1]
}

/// Where the payload starts in a one-block message `tweak | pp | payload`.
const PAYLOAD: usize = 4;
/// Bytes 4..8 of a tweak: its position.
const TWEAK_POSITION: usize = 4;

/// The target-sum encoding: 42 three-bit digits, 21 to a word, where each chain is opened.
#[derive(Clone, Copy)]
struct Digits([u64; 2]);

impl Digits {
    /// Digit `i`: bits `3j..3j+3` of word `i / 21`, `j = i % 21`.
    #[inline(always)]
    const fn get(self, i: usize) -> usize {
        (self.0[i / (V / 2)] >> (W * (i % (V / 2)))) as usize & (CHAIN_LENGTH - 1)
    }

    /// The sum of the digits, by adding neighbouring fields in place.
    ///
    /// No field overflows into the next: the top bits are zero, a digit is at most 7, and all of them sum to at most 294.
    const fn sum(self) -> u64 {
        let [low, high] = self.0;
        // 7 in every 6-bit field: the even digits.
        const EVEN: u64 = 0x71C7_1C71_C71C_71C7;
        // 63 in every 12-bit field.
        const LOW6: u64 = 0xF03F_03F0_3F03_F03F;
        // Four digits to a 6-bit field, two of each word: at most 28.
        let s = (low & EVEN) + (low >> W & EVEN) + (high & EVEN) + (high >> W & EVEN);
        // Two fields to a 12-bit field: at most 56.
        let s = (s & LOW6) + (s >> 6 & LOW6);
        // The six fields, folded into the lowest.
        let s = s + (s >> 12);
        let s = s + (s >> 24);
        (s + (s >> 48)) & 0xFFF
    }
}

/// The target-sum encoding of a message, or `None` if it is not valid.
///
/// It is valid iff each word's top bit is zero and the digits sum to 195.
fn encode(pp: &PublicParam, leaf_index: LeafIndex, message: &Message, randomness: &Randomness) -> Option<Digits> {
    let ([m0, m1, m2, m3], [r0, r1, r2]) = (*message, *randomness);
    let [low, high] = tweak_hash(pp, TWEAK_ENCODING, 0, leaf_index, &[m0, m1, m2, m3, r0, r1, r2, 0]);
    // Bits 0..63 are 21 digits, bit 63 is pinned to zero.
    //
    // Why pinned: with it, the digits determine the word.
    if (low | high) >> (W * V / 2) != 0 {
        return None;
    }
    let digits = Digits([low, high]);
    (digits.sum() == TARGET_SUM as u64).then_some(digits)
}

/// The hash every chain step is, `tweak | pp | value`, kept across steps and chains.
struct Chains {
    step: Template<6>,
}

impl Chains {
    fn new(pp: &PublicParam, leaf_index: LeafIndex) -> Self {
        let [t0, t1] = tweak(TWEAK_CHAIN, 0, leaf_index);
        Self {
            step: Template::new([t0, t1, pp[0], pp[1], 0, 0]),
        }
    }

    /// Walk chain `i` from value number `values.start` to value number `values.end`.
    ///
    /// The step out of value `s` is hashed at position `8i + s`, so no two steps share a tweak. Only the tweak's
    /// position field changes: its second word, the leaf index, is the template's.
    #[inline(always)]
    fn walk(&mut self, i: usize, values: core::ops::Range<usize>, value: Digest) -> Digest {
        let first = (i * CHAIN_LENGTH) as u32;
        let positions = first + values.start as u32..first + values.end as u32;
        self.step.chain::<TWEAK_POSITION, { 8 * PAYLOAD }>(positions, value)
    }
}

/// The Merkle leaf of a one-time key, `tweak | pp | ends`: chain `i`'s end `end(i)`, the chains in order, in one hash.
///
/// Unrolled over the chains, so each end's place in the stream's blocks is a constant.
#[inline(always)]
fn wots_leaf(pp: &PublicParam, leaf_index: LeafIndex, mut end: impl FnMut(usize) -> Digest) -> Digest {
    const { assert!(V == 42, "the ends below are one a chain") };
    digest(hash_with(|message| {
        message.write(tweak(TWEAK_WOTS_PK, 0, leaf_index)).write(*pp);
        macro_rules! ends {
            ($($i:literal)*) => { $( message.write(end($i)); )* };
        }
        ends!(0 1 2 3 4 5 6 7 8 9 10 11 12 13 14 15 16 17 18 19 20 21 22 23 24 25 26 27 28 29 30 31 32 33 34 35 36 37 38 39 40 41);
    }))
}

/// Fold a leaf, at index `leaf_index`, up its authentication path: each node `tweak | pp | left | right`.
///
/// Unrolled, so each level's tweak position and shifts are constants and the loop bookkeeping is gone. Across levels
/// only the tweak's position and index fields change, so each is one 32-bit store.
fn merkle_root(pp: &PublicParam, leaf_index: LeafIndex, leaf: Digest, path: &[Digest; LOG_LIFETIME]) -> Digest {
    const { assert!(LOG_LIFETIME == 32, "one node a level below") };
    let [t0, t1] = tweak(TWEAK_MERKLE, 0, 0);
    let mut node = Template::new([t0, t1, pp[0], pp[1], 0, 0, 0, 0]);
    let (bits, mut child) = (u64::from(leaf_index), leaf);
    macro_rules! levels {
        ($($level:literal)*) => { $( child = merkle_node::<$level>(&mut node, bits, child, &path[$level]); )* };
    }
    levels!(0 1 2 3 4 5 6 7 8 9 10 11 12 13 14 15 16 17 18 19 20 21 22 23 24 25 26 27 28 29 30 31);
    child
}

/// Bytes 12..16 of a tweak: its index.
const TWEAK_INDEX: usize = 12;

/// The parent of `child` at level `LEVEL`, the leaves being level 0, and its `sibling`, `bits` the leaf index.
///
/// Bit `LEVEL` of the leaf index is the child's side: the child and the sibling go to the slots it picks, with no
/// branch. The side is kept in bytes, a multiple of a word, so turning it into an address takes no shift.
#[inline(always)]
fn merkle_node<const LEVEL: usize>(node: &mut Template<8>, bits: u64, child: Digest, sibling: &Digest) -> Digest {
    let side = (bits << 4 >> LEVEL & 16) as usize;
    // The parent is at the next level up, at half the index.
    node.write(TWEAK_POSITION, (LEVEL + 1) as u32);
    node.write(TWEAK_INDEX, (bits >> (LEVEL + 1)) as u32);
    node.write(8 * PAYLOAD + side, child);
    node.write(8 * PAYLOAD + 16 - side, *sibling);
    digest(node.digest())
}
