//! leanXMSS over Keccak-256: two layers of XMSS of height 16 over WOTS+C keys, as
//! specified in the [leanXMSS specification]. Each leaf of the top tree signs the
//! root of one bottom tree, whose `2^16` leaves sign messages, so a key signs at
//! `2^32` leaf indices. A public key is 32 bytes, a signature 2404, and a
//! verification 186 permutations.
//!
//! `Th(P, A, M) = H(P | A | M)` truncated to 16 bytes, `H` the leanVM hash, with
//! a 16-byte address `A` (the `hash` module).
//!
//! [leanXMSS specification]: https://github.com/leanEthereum/leanVM/releases/download/doc-latest/leanXMSS.pdf

#![cfg_attr(not(test), warn(unused_crate_dependencies))]

mod hash;
pub use hash::*;
mod wots;
pub use wots::*;
mod tree;
use tree::*;
mod scheme;
pub use scheme::*;

/// The key's seed, the whole secret key.
pub const SEED_LEN: usize = 32;
pub type Seed = [u8; SEED_LEN];

/// Hashed before the seed, so no other scheme derives from the same bytes.
pub(crate) const SEED_TAG: &[u8] = b"leanXMSS";

/// The randomizer a layer's message digest is computed under.
pub const RANDOMIZER_LEN: usize = 16;
pub(crate) type Randomizer = [u8; RANDOMIZER_LEN];

/// The message to sign (a 256-bit message hash).
pub const MESSAGE_LEN: usize = 32;
pub type Message = [u8; MESSAGE_LEN];

/// The leaf, and so the bottom one-time key, a signature uses: its top 16 bits name
/// the bottom tree, its low 16 bits the leaf in it. Each leaf index may sign only
/// one message.
pub type LeafIndex = u32;

// WOTS+C
/// `w`: digit size in bits.
pub const W: usize = 2;
/// `2^w`: one more than the steps of a hash chain.
pub const CHAIN_LEN: usize = 1 << W;
/// The digest's digits: 128 bits of base `2^w`.
pub const DIGITS: usize = 8 * N / W;
/// The last digits, which the signer grinds to zero, so they have no chain.
pub(crate) const ZERO_DIGITS: usize = 6;
/// `v`: the chains of a one-time key.
pub const V: usize = DIGITS - ZERO_DIGITS;
/// `T`: the sum of every codeword's `v` digits. Above the mean, so verification
/// walks fewer chain steps.
pub const TARGET_SUM: usize = 106;
/// Chain steps one verification walks per layer.
pub(crate) const CHAIN_HASHES: usize = V * (CHAIN_LEN - 1) - TARGET_SUM;
/// Randomizers tried per layer signature.
pub(crate) const MAX_RANDOMIZER_TRIALS: u64 = 1 << 32;

// The trees
/// Height of each layer's tree.
pub const LAYER_HEIGHT: usize = 16;
pub const LOG_LIFETIME: usize = 2 * LAYER_HEIGHT;

pub const PUB_KEY_SIZE: usize = N + PUBLIC_PARAM_LEN;
pub(crate) const LEAF_INDEX_SIZE: usize = size_of::<LeafIndex>();
/// One layer's signature: the randomizer, the chain values and the path.
pub(crate) const LAYER_SIG_SIZE: usize = RANDOMIZER_LEN + V * N + LAYER_HEIGHT * N;
/// The leaf index, then the bottom layer's signature, then the top one's.
pub const SIG_SIZE: usize = LEAF_INDEX_SIZE + 2 * LAYER_SIG_SIZE;

/// Permutations of one verification: per layer the message digest, the chains,
/// the one-time leaf and the path.
pub(crate) const VERIFY_PERMUTATIONS: usize = blocks(RANDOMIZER_LEN + MESSAGE_LEN)
    + blocks(RANDOMIZER_LEN + N)
    + 2 * (CHAIN_HASHES * blocks(2 * N) + blocks(V * N) + LAYER_HEIGHT * blocks(2 * N));

const _: () = assert!(V == 58 && TARGET_SUM < V * (CHAIN_LEN - 1));
const _: () = assert!(PUB_KEY_SIZE == 32 && LAYER_SIG_SIZE == 1200 && SIG_SIZE == 2404);
const _: () = assert!(VERIFY_PERMUTATIONS == 186);
// A leaf index is the two layers' indices side by side.
const _: () = assert!(LOG_LIFETIME == 8 * LEAF_INDEX_SIZE);

use primitives::hash::Hasher;

/// The tweakable hash is `Truncate_16(H(prefix | address | payload))`,
/// the prefix being the public parameter and the address each scheme's own: a
/// hasher that has absorbed `prefix | address`.
fn prefixed_hasher(prefix: &[u8; N], address: &[u8]) -> Hasher {
    let mut hasher = Hasher::new();
    hasher.update(prefix).update(address);
    hasher
}

/// The root that `leaf`, at index `e`, and its authentication `path` reach, showing `visit` the two
/// children of every node on the way up, `node(z, j, children)` hashing node `j` at height `z`.
fn path_fold(
    leaf: [u8; N],
    e: usize,
    path: &[[u8; N]],
    mut visit: impl FnMut(&[[u8; N]; 2]),
    node: impl Fn(usize, usize, &[[u8; N]; 2]) -> [u8; N],
) -> [u8; N] {
    path.iter().enumerate().fold(leaf, |current, (z, &sibling)| {
        // Bit `z` of `e` says whether the node is the right child.
        let children = if (e >> z) & 1 == 0 {
            [current, sibling]
        } else {
            [sibling, current]
        };
        visit(&children);
        node(z + 1, e >> (z + 1), &children)
    })
}

/// `Truncate_16`: a hash value from a Keccak-256 output.
fn truncate(output: [u8; 32]) -> [u8; N] {
    output[..N].try_into().unwrap()
}
