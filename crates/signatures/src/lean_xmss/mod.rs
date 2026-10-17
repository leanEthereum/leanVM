//! leanXMSS over BLAKE2s: two layers of XMSS of height 16 over WOTS+C keys, as
//! specified in the [leanXMSS specification]. Each leaf of the top tree signs the
//! root of one bottom tree, whose `2^16` leaves sign messages, so a key signs at
//! `2^32` leaf indices. A public key is 32 bytes, a signature 2404, and a
//! verification 201 BLAKE2s compressions.
//!
//! `Th(P, A, M) = BLAKE2s(P | A | M)` truncated to 16 bytes, with the 16-byte
//! address `A` of leanSPHINCS (the `hash` module).
//!
//! [leanXMSS specification]: https://github.com/leanEthereum/leanVM/releases/download/doc-latest/leanXMSS.pdf

mod hash;
pub use hash::*;
mod wots;
pub use wots::*;
mod tree;
use tree::*;
mod scheme;
pub use scheme::*;
mod ssz_serialization;
pub use ssz_serialization::*;
#[cfg(feature = "mock")]
pub mod mock;

/// The seed every secret is derived from.
pub const SEED_LEN: usize = 32;
pub type Seed = [u8; SEED_LEN];

/// Hashed before the seed, so no other scheme derives from the same bytes.
pub const SEED_TAG: &[u8] = b"leanXMSS";

/// The randomizer a layer's message digest is computed under.
pub const RANDOMIZER_LEN: usize = 16;
pub type Randomizer = [u8; RANDOMIZER_LEN];

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
pub const ZERO_DIGITS: usize = 6;
/// `v`: the chains of a one-time key.
pub const V: usize = DIGITS - ZERO_DIGITS;
/// `T`: the sum of every codeword's `v` digits. Above the mean, so verification
/// walks fewer chain steps.
pub const TARGET_SUM: usize = 106;
/// Chain steps one verification walks per layer.
pub const CHAIN_HASHES: usize = V * (CHAIN_LEN - 1) - TARGET_SUM;
/// Randomizers tried per layer signature.
pub const MAX_RANDOMIZER_TRIALS: u64 = 1 << 32;

// The trees
/// Height of each layer's tree.
pub const LAYER_HEIGHT: usize = 16;
pub const LOG_LIFETIME: usize = 2 * LAYER_HEIGHT;

pub const PUB_KEY_SIZE: usize = N + PUBLIC_PARAM_LEN;
pub const LEAF_INDEX_SIZE: usize = size_of::<LeafIndex>();
/// One layer's signature: the randomizer, the chain values and the path.
pub const LAYER_SIG_SIZE: usize = RANDOMIZER_LEN + V * N + LAYER_HEIGHT * N;
/// The leaf index, then the bottom layer's signature, then the top one's.
pub const SIG_SIZE: usize = LEAF_INDEX_SIZE + 2 * LAYER_SIG_SIZE;

/// BLAKE2s compressions of one verification: per layer the message digest, the
/// chains, the one-time leaf and the path.
pub const VERIFY_COMPRESSIONS: usize = blocks(RANDOMIZER_LEN + MESSAGE_LEN)
    + blocks(RANDOMIZER_LEN + N)
    + 2 * (CHAIN_HASHES * blocks(2 * N) + blocks(V * N) + LAYER_HEIGHT * blocks(2 * N));

const _: () = assert!(V == 58 && TARGET_SUM < V * (CHAIN_LEN - 1));
const _: () = assert!(PUB_KEY_SIZE == 32 && LAYER_SIG_SIZE == 1200 && SIG_SIZE == 2404);
const _: () = assert!(VERIFY_COMPRESSIONS == 201);
// A leaf index is the two layers' indices side by side.
const _: () = assert!(LOG_LIFETIME == 8 * LEAF_INDEX_SIZE);

/// Serde for `[T; N]` with N > 32 (serde only derives arrays up to 32):
/// serialized as a fixed-length tuple, exactly like the native array impls.
pub mod array_serialization {
    use serde::de::{Error, SeqAccess, Visitor};
    use serde::ser::SerializeTuple;
    use serde::{Deserialize, Deserializer, Serialize, Serializer};
    use std::marker::PhantomData;

    pub fn serialize<S: Serializer, T: Serialize, const N: usize>(data: &[T; N], ser: S) -> Result<S::Ok, S::Error> {
        let mut tup = ser.serialize_tuple(N)?;
        for elem in data {
            tup.serialize_element(elem)?;
        }
        tup.end()
    }

    struct ArrayVisitor<T, const N: usize>(PhantomData<T>);

    impl<'de, T: Deserialize<'de> + Copy + Default, const N: usize> Visitor<'de> for ArrayVisitor<T, N> {
        type Value = [T; N];

        fn expecting(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
            write!(f, "an array of length {N}")
        }

        fn visit_seq<A: SeqAccess<'de>>(self, mut seq: A) -> Result<[T; N], A::Error> {
            let mut out = [T::default(); N];
            for (i, slot) in out.iter_mut().enumerate() {
                *slot = seq.next_element()?.ok_or_else(|| Error::invalid_length(i, &self))?;
            }
            Ok(out)
        }
    }

    pub fn deserialize<'de, D, T, const N: usize>(de: D) -> Result<[T; N], D::Error>
    where
        D: Deserializer<'de>,
        T: Deserialize<'de> + Copy + Default,
    {
        de.deserialize_tuple(N, ArrayVisitor::<T, N>(PhantomData))
    }
}
