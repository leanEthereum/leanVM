//! leanSPHINCS over Keccak-256: the stateless scheme specified in
//! `doc/lean_sphincs/main.tex`, the layered key of `2^30` signatures with FORS.
//! A message digest picks a bottom leaf `idx`, and so one FORS instance, and one
//! leaf in each of its 24 trees. The FORS openings sign the message, and a
//! hypertree of three layers of WOTS+C keys, of heights 8, 8 and 10 from the
//! bottom, signs the FORS key up to the public key. A public key is 32 bytes, a
//! signature 7740, and a verification 492 permutations.
//!
//! `Th(P, A, M) = H(P | A | M)` truncated to `n = 16` bytes, `H` the leanVM hash,
//! the 16-byte address `A` naming one hash call in the whole structure (the
//! `hash` module).
//!
//! The secret key is one 32-byte seed. Its hash with the scheme's tag derives
//! the public parameter and every secret. Key generation builds the top tree,
//! and signing the FORS instance and the three trees on the way up.

mod hash;
pub use hash::*;
mod wots;
pub use wots::*;
mod fors;
pub use fors::*;
mod scheme;
pub use scheme::*;

/// The key's seed, the whole secret key.
pub const SEED_LEN: usize = 32;
pub type Seed = [u8; SEED_LEN];

/// Hashed before the seed, so no other scheme derives from the same bytes.
pub(crate) const SEED_TAG: &[u8] = b"leanSPHINCS";

/// The per-message randomizer the message digest is computed under.
pub const RANDOMIZER_LEN: usize = 16;
pub(crate) type Randomizer = [u8; RANDOMIZER_LEN];

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
pub const TARGET_SUM: usize = 128;
/// `C_max`: encoding counters tried per one-time signature.
pub(crate) const MAX_ENCODING_ATTEMPTS: u64 = 1 << 32;

// The hypertree.
/// `d`: the layers.
pub const LAYERS: usize = 3;
/// The height of each layer's trees, bottom first.
pub const LAYER_HEIGHTS: [usize; LAYERS] = [8, 8, 10];
/// `h`: the bits of an index, which names a bottom leaf and its FORS instance.
pub const H: usize = LAYER_HEIGHTS[0] + LAYER_HEIGHTS[1] + LAYER_HEIGHTS[2];

// The few-time signature (FORS).
/// `k`: the trees of a FORS instance.
pub const FORS_TREES: usize = 24;
/// `a`: the height of a FORS tree.
pub const FORS_HEIGHT: usize = 10;

/// The message digest bits a signature reads: the index, then one leaf per FORS
/// tree.
pub const DIGEST_BITS: usize = H + FORS_TREES * FORS_HEIGHT;
/// The Keccak-256 calls that give them.
pub const DIGEST_CALLS: usize = DIGEST_BITS.div_ceil(256);

pub const PUB_KEY_SIZE: usize = N + PUBLIC_PARAM_LEN;
/// One FORS tree's opening: the secret, then the path.
pub const FORS_OPENING_SIZE: usize = N + FORS_HEIGHT * N;

/// One layer's signature on trees of height `height`: the counter, the chain
/// values and the path.
pub const fn layer_sig_size(height: usize) -> usize {
    COUNTER_LEN + V * N + height * N
}

pub const SIG_SIZE: usize = RANDOMIZER_LEN
    + FORS_TREES * FORS_OPENING_SIZE
    + layer_sig_size(LAYER_HEIGHTS[0])
    + layer_sig_size(LAYER_HEIGHTS[1])
    + layer_sig_size(LAYER_HEIGHTS[2]);

/// Permutations of one verification: the digest, the FORS leaves and nodes, the
/// encodings (the bottom one absorbs the FORS key), the chains, the one-time
/// leaves and the paths.
pub(crate) const VERIFY_PERMUTATIONS: usize = DIGEST_CALLS * blocks(MESSAGE_LEN + RANDOMIZER_LEN)
    + FORS_TREES * (blocks(N) + (FORS_HEIGHT - 1) * blocks(2 * N))
    + blocks(2 * FORS_TREES * N + COUNTER_LEN)
    + (LAYERS - 1) * blocks(N + COUNTER_LEN)
    + LAYERS * (V * (CHAIN_LEN - 1) - TARGET_SUM + blocks(V * N))
    + H * blocks(2 * N);

const _: () = assert!(W * V == 8 * N);
const _: () = assert!(TARGET_SUM < V * (CHAIN_LEN - 1));
const _: () = assert!(H == 26 && DIGEST_BITS == 266 && DIGEST_CALLS == 2);
const _: () = assert!(PUB_KEY_SIZE == 32);
const _: () = assert!(SIG_SIZE == 7740);
const _: () = assert!(VERIFY_PERMUTATIONS == 492);
