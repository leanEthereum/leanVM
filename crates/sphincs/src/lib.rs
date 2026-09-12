//! SPHINCS+ over BLAKE2s: the stateless scheme specified in
//! `doc/sphincs/main.tex`, with WOTS+C and FORS+C, at `2^24` signatures per key
//! pair. A public key is 32 bytes, a signature 4924, and a verification 497 hash
//! calls.
//!
//! That specification is the reference and every symbol here carries its name:
//! `n`, `w`, `v`, `T`, `d`, `h_lay`, `a`, `k`. `Th` is standard BLAKE2s of
//! the exact byte string `tweak | P | payload` truncated to `n = 128` bits (the
//! `hash` module), and the tweak names one hash call in the whole structure.
//!
//! One 32-byte master seed derives the public parameter and all signing secrets.
//! The signer caches public nodes of the top tree.

#![cfg_attr(not(test), warn(unused_crate_dependencies))]

mod hash;
pub use hash::*;
mod ots;
pub use ots::*;
mod fts;
pub use fts::*;
mod sphincs;
pub use sphincs::*;

/// `n`: hash value and Merkle node length, in bytes.
pub const N: usize = 16;
pub type Digest = [u8; N];

/// The public parameter derived from the master seed.
pub const PUBLIC_PARAM_LEN: usize = 16;
pub type PublicParam = [u8; PUBLIC_PARAM_LEN];

/// The master secret used to derive all WOTS and FORS secrets.
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

// The one-time signature.
/// `w`: chunk size in bits.
pub const W: usize = 3;
/// `2^w`: one more than the steps of a hash chain.
pub const CHAIN_LEN: usize = 1 << W;
/// `v`: code length, one hash chain per chunk.
pub const V: usize = 42;
/// `T`: the sum every codeword has. Above the mean `v(2^w-1)/2 = 147`, so
/// verification walks fewer chain steps and the signer grinds a counter for it.
pub const TARGET_SUM: usize = 191;

// The hypertree.
/// `d`: hypertree layers, numbered from the top.
pub const D: usize = 3;
/// `h_lay`: the Merkle tree height of each layer.
pub const HEIGHTS: [usize; D] = [12, 7, 7];
/// `h`: total height, so `2^h` few-time keys.
pub const H: usize = 26;

// The few-time signature.
/// `a`: log2 of the leaves in one few-time tree.
pub const A: usize = 10;
/// `k`: digest index groups.
pub const K: usize = 15;
/// The forest holds `k-1` trees: the tree of the last digest index carries no
/// information, that index being ground to zero (FORS$^+$C).
pub const NUM_FTS_TREES: usize = K - 1;

/// `A_max`: digest attempts per signature.
pub const MAX_DIGEST_ATTEMPTS: u64 = 1 << 32;
/// `C_max`: encoding attempts per layer.
pub const MAX_ENCODING_ATTEMPTS: u64 = 1 << 32;

/// `h + ka`: the message digest's width, all of it consumed by the index and the
/// `k` leaf indices.
pub const DIGEST_BITS: usize = H + K * A;
pub const DIGEST_BYTES: usize = DIGEST_BITS / 8;

pub const PUB_KEY_SIZE: usize = N + PUBLIC_PARAM_LEN;
/// A secret key is its public parameter and its master secret; the rest is derived.
pub const SECRET_KEY_SIZE: usize = PUBLIC_PARAM_LEN + MASTER_SECRET_LEN;
pub const SIG_SIZE: usize = RANDOMIZER_LEN + NUM_FTS_TREES * (1 + A) * N + D * (COUNTER_LEN + V * N) + H * N;

/// Calls to the hash function one verification makes: the digest, `Fts.recover`,
/// `d` times `Ots.leaf`, and `Tree.fold`.
pub const VERIFY_HASHES: usize = 1 + (NUM_FTS_TREES * (1 + A) + 1) + D * (V * (CHAIN_LEN - 1) - TARGET_SUM + 2) + H;

const _: () = assert!(H == HEIGHTS[0] + HEIGHTS[1] + HEIGHTS[2]);
// Each half of an encoding digest holds `v/2` chunks and one pinned bit.
const _: () = assert!(W * V / 2 + 1 == 64);
const _: () = assert!(DIGEST_BITS == DIGEST_BYTES * 8);
const _: () = assert!(TARGET_SUM < V * (CHAIN_LEN - 1));
const _: () = assert!(PUB_KEY_SIZE == 32);
const _: () = assert!(SIG_SIZE == 4924);
const _: () = assert!(VERIFY_HASHES == 497);
