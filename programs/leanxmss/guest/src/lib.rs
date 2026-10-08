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
use core::ops::Range;
use leanvm_guest::{Blake2s, Template, hash_with};
use thiserror::Error;

mod sign;

pub use sign::{SecretKey, XmssSignError, key_gen};

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
#[derive(Clone, Copy, Debug, PartialEq, Eq, Error)]
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
    Verifier::new().verify(pk, leaf_index, message, signature)
}

/// A verifier of many signatures, which keeps what depends on the leaf index alone for the next signature at the same
/// one (signers attesting to one slot all sign at one leaf index), and its hash templates, whose fixed words it writes
/// once.
pub struct Verifier {
    /// The leaf index `parents` is for, or one no `LeafIndex` is before the first signature.
    leaf_index: u64,
    /// The tweak index at each Merkle level: the parent's index, `leaf_index >> (level + 1)`.
    parents: [u64; LOG_LIFETIME],
    /// The chain step's template, its tweak at leaf index `leaf_index`: a signature writes only its parameter.
    chains: Chains,
    /// The Merkle node's template: a signature writes only its parameter, and each level its tweak's fields.
    node: Template<8>,
}

impl Default for Verifier {
    fn default() -> Self {
        Self::new()
    }
}

impl Verifier {
    pub fn new() -> Self {
        Self {
            leaf_index: u64::MAX,
            parents: [0; LOG_LIFETIME],
            chains: Chains::new(&[0; 2], 0),
            node: merkle_template(&[0; 2]),
        }
    }

    /// [`verify`], reusing the Merkle tweak indices of the previous signature if it had the same leaf index.
    pub fn verify(
        &mut self,
        pk: &PublicKey,
        leaf_index: LeafIndex,
        message: &Message,
        signature: &Signature,
    ) -> Result<(), XmssVerifyError> {
        let pp = &pk.public_param;
        // The digits say where each chain was opened.
        let digits = encode(pp, leaf_index, message, &signature.randomness).ok_or(XmssVerifyError::InvalidEncoding)?;
        // Walk each chain the rest of the way, chain `i` from value `digit_i` to value 7: its end is the leaf's. The
        // leaf takes the chains one by one, unrolled, so each position is a constant.
        let bits = u64::from(leaf_index);
        if self.leaf_index != bits {
            self.leaf_index = bits;
            self.parents = parent_indices(leaf_index);
            self.chains.step.set(1, [bits << 32]);
        }
        let Self {
            parents, chains, node, ..
        } = self;
        chains.step.set(2, *pp);
        node.set(2, *pp);
        let (mut remaining, mut counter) = (Remaining::new(digits), Chains::counter());
        let leaf = wots_leaf(pp, leaf_index, |i| {
            chains.walk_to_end(&mut counter, remaining.next(i), signature.chain_tips[i])
        });
        // The chain ends are the one-time public key: its leaf, folded up to the root.
        let root = merkle_root(node, leaf_index, parents, leaf, &signature.merkle_proof);
        if root == pk.merkle_root {
            Ok(())
        } else {
            Err(XmssVerifyError::InvalidMerklePath)
        }
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

/// `x`, which the compiler can no longer see through, so a running shift stays one shift a step rather than folding
/// into each step's own constant shift.
#[inline(always)]
fn opaque(mut x: u64) -> u64 {
    #[cfg(all(target_arch = "riscv64", target_os = "none"))]
    // SAFETY: an empty instruction sequence, which leaves `x` as it is.
    unsafe {
        core::arch::asm!("/* {0} */", inout(reg) x, options(pure, nomem, nostack, preserves_flags));
    }
    x
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
        // The six fields, folded into the lowest. The sum is under 2^11, so an 11-bit mask (one `andi`) takes it.
        let s = s + (s >> 12);
        let s = s + (s >> 24);
        (s + (s >> 48)) & 0x7FF
    }
}

/// What remains of each chain, in order: `7 - digit` steps, times `2^32`, where a position sits in a tweak's first
/// word. A chain's start is then its end less this, with no constant to add.
///
/// A word is read in three runs of its complement, its digits 0 to 9, 10, and 11 to 20, each run moved down a digit
/// at a time, so a chain costs one shift and one mask: digit 10 straddles bit 32, which the run shifted up by 32 loses.
struct Remaining([u64; 6]);

impl Remaining {
    const fn new(Digits([low, high]): Digits) -> Self {
        let (low, high) = (!low, !high);
        Self([low << 32, low << 2, low >> 1, high << 32, high << 2, high >> 1])
    }

    /// Chain `i`'s steps times `2^32`, the chains taken in order.
    #[inline(always)]
    fn next(&mut self, i: usize) -> u64 {
        let j = i % (V / 2);
        let run = &mut self.0[3 * (i / (V / 2)) + usize::from(j >= 10) + usize::from(j > 10)];
        // The complement's digit is `7 - digit`.
        let steps = *run & ((CHAIN_LENGTH as u64 - 1) << 32);
        *run = opaque(*run >> W);
        steps
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

/// The tweak's first word as [`Chains::walk_to_end`] counts it, apart from the template so that it stays in registers.
struct Counter {
    /// The tweak's first word at the next chain's end: the position `8i + 7` of chain `i`.
    end: u64,
    /// One position, `2^32` in the tweak's first word.
    one: u64,
    /// One chain's positions, `8 * 2^32`.
    eight: u64,
}

impl Chains {
    fn new(pp: &PublicParam, leaf_index: LeafIndex) -> Self {
        let [t0, t1] = tweak(TWEAK_CHAIN, 0, leaf_index);
        Self {
            step: Template::new([t0, t1, pp[0], pp[1], 0, 0]),
        }
    }

    /// The counter at chain 0's end.
    fn counter() -> Counter {
        Counter {
            end: tweak(TWEAK_CHAIN, CHAIN_LENGTH as u32 - 1, 0)[0],
            one: opaque(1 << 32),
            eight: opaque((CHAIN_LENGTH as u64) << 32),
        }
    }

    /// Walk the next chain to its end, `steps` the steps left (times `2^32`), the chains taken in order.
    ///
    /// The tweak's whole first word is the counter: one 64-bit store a step, rather than a 32-bit store of the
    /// position. Its value at each chain's end is kept as a running sum, as its constant would take a shift.
    #[inline(always)]
    fn walk_to_end(&mut self, counter: &mut Counter, steps: u64, value: Digest) -> Digest {
        let end = counter.end;
        counter.end = opaque(end + counter.eight);
        self.step
            .chain_word::<0, { 8 * PAYLOAD }>(end - steps, end, counter.one, value)
    }

    /// Walk chain `i` from value number `values.start` to value number `values.end`.
    ///
    /// The step out of value `s` is hashed at position `8i + s`, so no two steps share a tweak. Only the tweak's
    /// position field changes: its second word, the leaf index, is the template's.
    #[inline(always)]
    fn walk(&mut self, i: usize, values: Range<usize>, value: Digest) -> Digest {
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

/// Fold a leaf, at index `leaf_index`, up its authentication path: each node `tweak | pp | left | right`, `parents`
/// the tweak index at each level.
///
/// Unrolled, so each level's shifts are constants and the loop bookkeeping is gone. Across levels only the tweak's
/// fields change: its first word, the position in its high half, is one 64-bit store of a running sum, and its index
/// one 32-bit store.
fn merkle_root(
    node: &mut Template<8>,
    leaf_index: LeafIndex,
    parents: &[u64; LOG_LIFETIME],
    leaf: Digest,
    path: &[Digest; LOG_LIFETIME],
) -> Digest {
    const { assert!(LOG_LIFETIME == 32, "one node a level below") };
    let (bits, mut child) = (u64::from(leaf_index), leaf);
    let (mut first, one) = (tweak(TWEAK_MERKLE, 0, 0)[0], opaque(1 << 32));
    macro_rules! levels {
        ($($level:literal)*) => { $( first = opaque(first + one); child = merkle_node::<$level>(node, bits, first, parents, child, &path[$level]); )* };
    }
    levels!(0 1 2 3 4 5 6 7 8 9 10 11 12 13 14 15 16 17 18 19 20 21 22 23 24 25 26 27 28 29 30 31);
    child
}

/// The Merkle node's template under a parameter: its tweak's fields are written at each level.
fn merkle_template(pp: &PublicParam) -> Template<8> {
    let [t0, t1] = tweak(TWEAK_MERKLE, 0, 0);
    Template::new([t0, t1, pp[0], pp[1], 0, 0, 0, 0])
}

/// The tweak index at each Merkle level for a leaf index: the parent's index, `leaf_index >> (level + 1)`.
#[inline(always)]
fn parent_indices(leaf_index: LeafIndex) -> [u64; LOG_LIFETIME] {
    core::array::from_fn(|level| u64::from(leaf_index) >> (level + 1))
}

/// Bytes 12..16 of a tweak: its index.
const TWEAK_INDEX: usize = 12;

/// The parent of `child` at level `LEVEL`, the leaves being level 0, and its `sibling`, `bits` the leaf index, `first`
/// the tweak's first word at this level and `parents` the tweak index at each level.
///
/// Bit `LEVEL` of the leaf index is the child's side: the child and the sibling go to the slots it picks, with no
/// branch. The side is kept in bytes, a multiple of a word, so turning it into an address takes no shift: from level 5
/// up it is bit 4 of a lower level's parent index.
#[inline(always)]
fn merkle_node<const LEVEL: usize>(
    node: &mut Template<8>,
    bits: u64,
    first: u64,
    parents: &[u64; LOG_LIFETIME],
    child: Digest,
    sibling: &Digest,
) -> Digest {
    let side = if LEVEL >= 5 {
        parents[LEVEL.saturating_sub(5)] & 16
    } else {
        bits << 4 >> LEVEL & 16
    } as usize;
    // The parent is at the next level up, at half the index.
    node.write(0, first);
    node.write(TWEAK_INDEX, parents[LEVEL] as u32);
    node.write(8 * PAYLOAD + side, child);
    node.write(8 * PAYLOAD + 16 - side, *sibling);
    digest(node.digest())
}
