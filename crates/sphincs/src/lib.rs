//! leanSPHINCS over BLAKE2s: the stateless scheme specified in
//! `doc/sphincs/main.tex`. One Merkle tree of height `h = 26` over WOTS+C keys,
//! each signing the key of a few-time signature built from small WOTS keys, the
//! two-level WOTS forest. A public key is 32 bytes, a signature 4276, and a
//! verification 307 BLAKE2s compressions.
//!
//! `Th(P, A, M) = BLAKE2s(P | A | M)` truncated to `n = 16` bytes, the 16-byte
//! address `A` naming one hash call in the whole structure (the `hash` module).
//!
//! One 32-byte seed derives the public parameter and every secret. A key may be
//! pruned: it keeps one subtree of height `b` and replaces the `h - b` siblings
//! above it by pseudorandom nodes, which trades lifetime for key generation.

#![cfg_attr(not(test), warn(unused_crate_dependencies))]

mod hash;
pub use hash::*;
mod wots;
pub use wots::*;
mod forest;
pub use forest::*;
mod sphincs;
pub use sphincs::*;

/// `n`: hash value and Merkle node length, in bytes.
pub const N: usize = 16;
pub type Digest = [u8; N];

/// The public parameter derived from the seed.
pub const PUBLIC_PARAM_LEN: usize = 16;
pub type PublicParam = [u8; PUBLIC_PARAM_LEN];

/// The seed every secret is derived from.
pub const MASTER_SECRET_LEN: usize = 32;
pub type MasterSecret = [u8; MASTER_SECRET_LEN];

/// The per-signature randomizer the message digest is computed under.
pub const RANDOMIZER_LEN: usize = 16;
pub type Randomizer = [u8; RANDOMIZER_LEN];

/// The message to sign (a 256-bit message hash).
pub const MESSAGE_LEN: usize = 32;
pub type Message = [u8; MESSAGE_LEN];

/// The serialized width of an encoding counter.
pub const COUNTER_LEN: usize = 4;

// The one-time signature (WOTS+C).
/// `w`: chunk size in bits.
pub const W: usize = 2;
/// `2^w`: one more than the steps of a hash chain.
pub const CHAIN_LEN: usize = 1 << W;
/// `v`: code length, one hash chain per chunk.
pub const V: usize = 64;
/// `T`: the sum every codeword has. Above the mean `v(2^w-1)/2 = 96`, so
/// verification walks fewer chain steps and the signer grinds a counter for it.
pub const TARGET_SUM: usize = 120;

/// `h`: the tree's height, so `2^h` few-time keys.
pub const H: usize = 26;

// The few-time signature (the two-level WOTS forest).
/// Trees in a forest.
pub const FOREST_TREES: usize = 8;
/// Height of a tree, whose leaves each hash two subtrees.
pub const TREE_HEIGHT: usize = 4;
/// Subtrees under one tree leaf.
pub const SUBTREES: usize = 2;
/// Height of a subtree, whose leaves are small WOTS keys.
pub const SUBTREE_HEIGHT: usize = 3;
/// Chains of a small WOTS key.
pub const FOREST_CHAINS: usize = 6;
/// The top position of a forest chain: positions `0..=4`, four steps.
pub const FOREST_CHAIN_TOP: usize = 4;
/// The digit sum of a forest codeword, hence the chain steps one small WOTS key
/// costs a verifier.
pub const CODEWORD_SUM: usize = 5;
/// Digest bits naming a codeword.
pub const CODEWORD_BITS: usize = 8;

/// `A_max`: randomizers tried per signature.
pub const MAX_DIGEST_ATTEMPTS: u64 = 1 << 32;
/// `C_max`: encoding counters tried per signature.
pub const MAX_ENCODING_ATTEMPTS: u64 = 1 << 32;

/// The message digest's first bytes: one codeword per subtree, a byte each.
pub const DIGEST_WORD_BYTES: usize = FOREST_TREES * SUBTREES;
/// Digest bits one tree consumes: its leaf, and per subtree a WOTS key and a
/// codeword.
pub const TREE_BITS: usize = TREE_HEIGHT + SUBTREES * (SUBTREE_HEIGHT + CODEWORD_BITS);
/// The message digest's width: the codewords, the index, the trees' leaves, the
/// subtrees' WOTS keys.
pub const DIGEST_BITS: usize = H + FOREST_TREES * TREE_BITS;

/// Values a signature carries per tree: per subtree the chain values and the
/// path, then the tree's path.
pub const TREE_VALUES: usize = SUBTREES * (FOREST_CHAINS + SUBTREE_HEIGHT) + TREE_HEIGHT;

pub const PUB_KEY_SIZE: usize = N + PUBLIC_PARAM_LEN;
pub const SIG_SIZE: usize = RANDOMIZER_LEN + FOREST_TREES * TREE_VALUES * N + COUNTER_LEN + V * N + H * N;

/// BLAKE2s compressions of one verification: the digest, the forest, the
/// encoding, the chains, the one-time leaf and the path.
pub const VERIFY_COMPRESSIONS: usize = blocks(MESSAGE_LEN + RANDOMIZER_LEN)
    + FOREST_TREES
        * (SUBTREES * (CODEWORD_SUM + blocks(FOREST_CHAINS * N) + SUBTREE_HEIGHT - 1)
            + blocks(2 * SUBTREES * N)
            + TREE_HEIGHT
            - 1)
    + blocks(2 * FOREST_TREES * N)
    + blocks(N + COUNTER_LEN)
    + (V * (CHAIN_LEN - 1) - TARGET_SUM)
    + blocks(V * N)
    + H * blocks(2 * N);

const _: () = assert!(W * V == 8 * N);
const _: () = assert!(TARGET_SUM < V * (CHAIN_LEN - 1));
const _: () = assert!(CODEWORD_BITS == 8 && DIGEST_BITS == 234);
const _: () = assert!(PUB_KEY_SIZE == 32);
const _: () = assert!(SIG_SIZE == 4276);
const _: () = assert!(VERIFY_COMPRESSIONS == 307);
