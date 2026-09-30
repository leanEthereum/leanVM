//! leanSPHINCS: stateless SPHINCS+ over BLAKE2s, with WOTS+C and FORS+C.
//!
//! A variant of the SPHINCS+ framework, not SLH-DSA (FIPS 205):
//!
//! - WOTS+C replaces the Winternitz checksum by a target sum, which the signer grinds a counter for.
//! - FORS+C drops the last tree, whose index the signer grinds to zero.
//! - Digests are 16 bytes, with 16-byte tweaks of this variant's own layout.
//!
//! A hypertree of `d = 3` Merkle layers over one-time keys signs few-time keys.
//!
//! A key answers `2^26` indices, so it signs up to `2^24` messages with no state.
//!
//! `Th(P, tw, M)` is standard BLAKE2s of `tw | P | M`, cut to `n = 128` bits.
//!
//! Values are little-endian 64-bit words, whose bytes are the specification's.
//!
//! The machine loads a word in one instruction, and a byte-aligned value in eight.
//!
//! Byte for byte the scheme of the leanSPHINCS specification, whose letters the code keeps.
#![no_std]

mod fts;
mod ots;
mod sign;

pub use sign::{SecretKey, SignError, key_gen};

use leanvm_guest::Blake2s;

/// `n`: a hash value, 128 bits.
pub type Digest = [u64; 2];
/// `P`: the per-key public parameter.
pub type PublicParam = [u64; 2];
/// The per-signature randomizer the message digest is taken under.
pub type Randomizer = [u64; 2];
/// The message to sign: a 256-bit message hash.
pub type Message = [u64; 4];

/// `w`: bits per chunk of a one-time codeword.
pub const W: usize = 3;
/// `2^w`: values on one hash chain.
pub const CHAIN_LEN: usize = 1 << W;
/// `v`: chunks, one hash chain each.
pub const V: usize = 42;
/// `T`: what every codeword sums to.
///
/// Above the mean 147, so a verifier walks fewer steps than a signer.
pub const TARGET_SUM: usize = 191;
/// `d`: hypertree layers, numbered from the top.
pub const D: usize = 3;
/// `h_lay`: each layer's tree height.
pub const HEIGHTS: [usize; D] = [12, 7, 7];
/// `h`: the total height, so a key has `2^h` few-time keys.
pub const H: usize = 26;
/// `a`: log2 of the leaves of one few-time tree.
pub const A: usize = 10;
/// `k`: indices the message digest picks, one per few-time tree.
pub const K: usize = 15;
/// Trees in a few-time forest: the last index is ground to zero, so its tree is dropped.
pub const FTS_TREES: usize = K - 1;

/// Serialized public key: `root | public_param`.
pub const PUB_KEY_SIZE: usize = size_of::<PublicKey>();
/// Serialized signature: the in-memory layout with each counter in 4 bytes, not a word.
pub const SIG_SIZE: usize = size_of::<Signature>() - D * 4;
/// Hash calls in one verification: the digest, the forest, `d` one-time leaves, `h` nodes.
pub const VERIFY_HASHES: usize = 1 + (FTS_TREES * (1 + A) + 1) + D * (V * (CHAIN_LEN - 1) - TARGET_SUM + 2) + H;

const _: () = assert!(H == HEIGHTS[0] + HEIGHTS[1] + HEIGHTS[2]);
// Each 64-bit half of an encoding digest holds `v/2` chunks and one pinned bit.
const _: () = assert!(W * V / 2 + 1 == 64);
const _: () = assert!(PUB_KEY_SIZE == 32 && SIG_SIZE == 4924 && VERIFY_HASHES == 497);

/// Byte 0 of every tweak: 1 for leanSPHINCS, so none of its hashes is a leanXMSS one.
const PROTOCOL_DOMAIN_SEP: u8 = 1;

// Tweak types, byte 1 of a tweak.
const TWEAK_PRF: u8 = 0;
const TWEAK_CHAIN: u8 = 1;
const TWEAK_LEAF: u8 = 2;
const TWEAK_NODE: u8 = 3;
const TWEAK_ENC: u8 = 4;
const TWEAK_PARAMETER: u8 = 5;
const TWEAK_RANDOMIZER: u8 = 7;
const TWEAK_FTS_PRF: u8 = 8;
const TWEAK_FTS_LEAF: u8 = 9;
const TWEAK_FTS_NODE: u8 = 10;
const TWEAK_FTS_ROOTS: u8 = 11;
const TWEAK_MSG: u8 = 12;

/// A public key.
///
/// Its fields are words, so it has no padding and any 32 bytes are one.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(C)]
pub struct PublicKey {
    /// The root of the top layer's tree.
    pub root: Digest,
    /// `P`, which every hash of the key is taken under.
    pub public_param: PublicParam,
}

/// One few-time tree's part of a signature: the opened secret and its path.
#[derive(Clone, Debug, PartialEq, Eq)]
#[repr(C)]
pub struct FtsOpening {
    /// The secret of the leaf the digest picks.
    pub secret: Digest,
    /// The sibling at each level, leaf first.
    pub path: [Digest; A],
}

/// One hypertree layer's part of a signature, for a tree of a given height.
#[derive(Clone, Debug, PartialEq, Eq)]
#[repr(C)]
pub struct LayerSignature<const HEIGHT: usize> {
    /// The encoding counter, a 32-bit value in a word of its own.
    pub counter: u64,
    /// The one-time signature: chain `i` opened at chunk `i`.
    pub ots: [Digest; V],
    /// The sibling at each level of the layer's tree, leaf first.
    pub path: [Digest; HEIGHT],
}

/// A signature, in the specification's order.
///
/// Its fields are words, so it has no padding and any words are one.
#[derive(Clone, Debug, PartialEq, Eq)]
#[repr(C)]
pub struct Signature {
    /// What the message digest is taken under, ground by the signer.
    pub randomizer: Randomizer,
    /// The few-time signature, one opening per tree.
    pub fts: [FtsOpening; FTS_TREES],
    /// The top layer, of height 12.
    pub layer0: LayerSignature<{ HEIGHTS[0] }>,
    /// The middle layer, of height 7.
    pub layer1: LayerSignature<{ HEIGHTS[1] }>,
    /// The bottom layer, of height 7, which signs the few-time key.
    pub layer2: LayerSignature<{ HEIGHTS[2] }>,
}

impl Signature {
    /// A layer's counter, one-time signature and path.
    fn layer(&self, lay: usize) -> (u64, &[Digest; V], &[Digest]) {
        // The layers have different heights, hence different types.
        match lay {
            0 => self.layer0.parts(),
            1 => self.layer1.parts(),
            _ => self.layer2.parts(),
        }
    }

    /// The specification's serialization, each counter in 4 bytes.
    pub fn to_bytes(&self) -> [u8; SIG_SIZE] {
        // Fields in order, each word as its 8 little-endian bytes.
        let mut out = [0; SIG_SIZE];
        let mut at = 0;
        let mut put = |bytes: &[u8]| {
            out[at..at + bytes.len()].copy_from_slice(bytes);
            at += bytes.len();
        };
        let words = |words: &[u64], put: &mut dyn FnMut(&[u8])| words.iter().for_each(|w| put(&w.to_le_bytes()));
        words(&self.randomizer, &mut put);
        for opening in &self.fts {
            words(&opening.secret, &mut put);
            words(opening.path.as_flattened(), &mut put);
        }
        for lay in 0..D {
            let (counter, ots, path) = self.layer(lay);
            // A counter of a valid signature fits its 4 bytes.
            put(&(counter as u32).to_le_bytes());
            words(ots.as_flattened(), &mut put);
            words(path.as_flattened(), &mut put);
        }
        out
    }
}

impl<const HEIGHT: usize> LayerSignature<HEIGHT> {
    fn parts(&self) -> (u64, &[Digest; V], &[Digest]) {
        (self.counter, &self.ots, &self.path)
    }
}

/// Why a signature is rejected.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum VerifyError {
    /// The message digest's last index is not zero.
    InadmissibleDigest,
    /// A layer's counter gives the message it signs no codeword.
    InadmissibleEncoding,
    /// The hypertree walk does not reach the key's root.
    RootMismatch,
}

/// One one-time key's place: the layer, the tree within it, the leaf within that tree.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct Pos {
    /// `lay`: the layer, 0 at the top.
    lay: usize,
    /// `tau`: the tree within the layer.
    tau: u32,
    /// `e`: the leaf within the tree.
    e: u32,
}

/// The height of everything below each layer's top: `[26, 14, 7, 0]`.
const SUFFIX: [usize; D + 1] = [H, H - HEIGHTS[0], HEIGHTS[2], 0];

impl Pos {
    /// The one-time key an index uses on a layer.
    ///
    /// ```text
    ///   idx = [ tau_0 = 0 | e_0 : 12 bits | e_1 : 7 bits | e_2 : 7 bits ]
    /// ```
    fn of(idx: u64, lay: usize) -> Self {
        // The tree is what sits above the layer, the leaf the layer's own bits.
        Self {
            lay,
            tau: (idx >> SUFFIX[lay]) as u32,
            e: ((idx >> SUFFIX[lay + 1]) & ((1 << HEIGHTS[lay]) - 1)) as u32,
        }
    }
}

/// `Ver`: 497 hash calls.
pub fn verify(pk: &PublicKey, message: &Message, signature: &Signature) -> Result<(), VerifyError> {
    let pp = &pk.public_param;
    // The digest picks the few-time key and the leaf it opens in each tree.
    let (idx, u) = message_digest(pp, &pk.root, &signature.randomizer, message);
    // The last tree is dropped, so its index must be zero (FORS+C).
    if u[K - 1] != 0 {
        return Err(VerifyError::InadmissibleDigest);
    }
    // The few-time key is the message the bottom layer signs, and each root the next one up.
    let mut message = fts::recover(pp, idx, &u, &signature.fts);
    for lay in (0..D).rev() {
        let pos = Pos::of(idx, lay);
        let (counter, ots, path) = signature.layer(lay);
        // A counter is 32 bits: a word holding more is no counter.
        let counter = u32::try_from(counter).map_err(|_| VerifyError::InadmissibleEncoding)?;
        let leaf = ots::leaf(pp, pos, &message, counter, ots).ok_or(VerifyError::InadmissibleEncoding)?;
        message = tree_fold(pp, pos, leaf, path);
    }
    if message == pk.root {
        Ok(())
    } else {
        Err(VerifyError::RootMismatch)
    }
}

/// A tweak as two words.
///
/// ```text
///   bytes  0      1     2    3     4..8  8..12  12..16
///          domain type  lay  zero  p     tau    j
/// ```
///
/// `lay` is a hypertree layer or a few-time tree.
fn tweak(t: u8, lay: usize, tau: u32, p: u32, j: u32) -> [u64; 2] {
    [
        u64::from(PROTOCOL_DOMAIN_SEP) | u64::from(t) << 8 | (lay as u64) << 16 | u64::from(p) << 32,
        u64::from(tau) | u64::from(j) << 32,
    ]
}

/// `Th(P, tw, M)`, on a message of whole words.
///
/// Inlined with its length known, a call folds to the words it hashes and the compressions.
#[inline(always)]
fn th<const N: usize>(pp: &PublicParam, tw: &[u64; 2], message: &[u64; N]) -> Digest {
    let mut hasher = Blake2s::new();
    hasher.update_words(tw).update_words(pp).update_words(message);
    // A digest is the first 16 bytes of the 32.
    let digest = hasher.finalize_words();
    [digest[0], digest[1]]
}

/// The message digest, read as the index and the `k` few-time leaf indices.
///
/// `h + ka = 176` bits: the index in the low 26, then 10 bits per leaf index.
fn message_digest(pp: &PublicParam, root: &Digest, randomizer: &Randomizer, message: &Message) -> (u64, [u32; K]) {
    // `tw | P | randomizer | root | message`: 96 bytes, two compressions.
    let mut hasher = Blake2s::new();
    hasher.update_words(&tweak(TWEAK_MSG, 0, 0, 0, 0)).update_words(pp);
    hasher.update_words(randomizer).update_words(root).update_words(message);
    let digest = hasher.finalize_words();
    // Bits `offset..offset + len`, little-endian, which may straddle two words.
    let bits = |offset: usize, len: usize| {
        let (word, shift) = (offset / 64, offset % 64);
        let mut x = digest[word] >> shift;
        if shift + len > 64 {
            x |= digest[word + 1] << (64 - shift);
        }
        x & ((1 << len) - 1)
    };
    (bits(0, H), core::array::from_fn(|kappa| bits(H + kappa * A, A) as u32))
}

/// A hypertree node: a level and an index within a layer's tree.
fn node(pp: &PublicParam, lay: usize, tau: u32, level: usize, j: u64, left: &Digest, right: &Digest) -> Digest {
    th(
        pp,
        &tweak(TWEAK_NODE, lay, tau, level as u32, j as u32),
        &concat(left, right),
    )
}

/// Two digests as one message.
fn concat(left: &Digest, right: &Digest) -> [u64; 4] {
    [left[0], left[1], right[0], right[1]]
}

/// `Tree.fold`: a leaf folded up its path to its tree's root.
fn tree_fold(pp: &PublicParam, pos: Pos, leaf: Digest, path: &[Digest]) -> Digest {
    path.iter().enumerate().fold(leaf, |current, (level, sibling)| {
        // The leaf's bit at this level says which child the current node is.
        let (left, right) = if (pos.e >> level) & 1 == 0 {
            (&current, sibling)
        } else {
            (sibling, &current)
        };
        node(
            pp,
            pos.lay,
            pos.tau,
            level + 1,
            u64::from(pos.e >> (level + 1)),
            left,
            right,
        )
    })
}
