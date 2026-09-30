//! Key generation and signing, for a key of one leaf index.
//!
//! The specification's key builds all `2^32` leaves, which no benchmark can afford.
//!
//! A key of the range `[e, e]` has one real leaf, at index `e`.
//!
//! Every other node its path needs is a filler: a hash of the seed, not a subtree.
//!
//! Its signatures are the specification's, and verify as any other.

use crate::*;

/// Bound on the randomness a signer tries before giving up.
const MAX_RANDOMIZER_TRIALS: u64 = 1 << 32;

/// A secret key: its seed is the whole secret, everything else is derived.
#[derive(Clone, Debug)]
pub struct SecretKey {
    /// The secret every chain start and filler is derived from.
    seed: [u64; 4],
    /// The one leaf index the key signs at.
    leaf_index: LeafIndex,
    /// The public key, kept so it is not recomputed.
    public_key: PublicKey,
}

/// Why signing failed.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SignError {
    /// No randomness within the trial bound gave a valid encoding.
    NoValidEncoding,
}

/// The key pair that signs at one leaf index only, from its secret seed.
pub fn key_gen(seed: [u8; 32], leaf_index: LeafIndex) -> (SecretKey, PublicKey) {
    let seed = core::array::from_fn(|i| u64::from_le_bytes(seed[8 * i..8 * i + 8].try_into().unwrap()));
    // The public parameter is hashed under an all-zero one.
    let public_param = tweak_hash(&[0; 2], TWEAK_PARAMETER, 0, 0, &seed);
    let pp = &public_param;
    // The one real leaf: every chain walked from its start to its end.
    let ends =
        core::array::from_fn(|i| chain(pp, leaf_index, i, 0, CHAIN_LENGTH - 1, secret(&seed, pp, leaf_index, i)));
    let leaf = wots_leaf(pp, leaf_index, &ends);
    // Its path is all fillers, which the root is the fold of.
    let merkle_root = merkle_root(pp, leaf_index, leaf, &filler_path(&seed, pp, leaf_index));
    let public_key = PublicKey {
        merkle_root,
        public_param,
    };
    (
        SecretKey {
            seed,
            leaf_index,
            public_key,
        },
        public_key,
    )
}

impl SecretKey {
    pub fn public_key(&self) -> PublicKey {
        self.public_key
    }

    /// Sign a message at the key's leaf index, deterministically.
    ///
    /// The signer tries randomness until the encoding is valid: about `2^15` tries.
    pub fn sign(&self, message: &Message) -> Result<Signature, SignError> {
        let (seed, leaf_index, pp) = (&self.seed, self.leaf_index, &self.public_key.public_param);
        let (randomness, digits) = (0..MAX_RANDOMIZER_TRIALS)
            .find_map(|trial| {
                // Trial `j`'s randomness: the first 24 bytes of a hash of the seed and the message.
                let mut hasher = Blake2s::new();
                hasher.update_words(&tweak(TWEAK_RANDOMIZER, trial as u32, leaf_index));
                hasher.update_words(pp).update_words(seed).update_words(message);
                let [r0, r1, r2, _] = hasher.finalize_words();
                let randomness = [r0, r1, r2];
                encode(pp, leaf_index, message, &randomness).map(|digits| (randomness, digits))
            })
            .ok_or(SignError::NoValidEncoding)?;
        // Chain `i` opened at value `digit_i`, and the path of fillers.
        Ok(Signature {
            chain_tips: core::array::from_fn(|i| {
                chain(
                    pp,
                    leaf_index,
                    i,
                    0,
                    digits[i] as usize,
                    secret(seed, pp, leaf_index, i),
                )
            }),
            randomness,
            merkle_proof: filler_path(seed, pp, leaf_index),
        })
    }
}

/// The start of chain `i` of the one-time key at a leaf index.
fn secret(seed: &[u64; 4], pp: &PublicParam, leaf_index: LeafIndex, i: usize) -> Digest {
    tweak_hash(pp, TWEAK_PRF, i as u32, leaf_index, seed)
}

/// The leaf's authentication path: at each level its sibling, a filler.
fn filler_path(seed: &[u64; 4], pp: &PublicParam, leaf_index: LeafIndex) -> [Digest; LOG_LIFETIME] {
    core::array::from_fn(|level| {
        // The sibling's index flips the low bit of the node's.
        let sibling = (u64::from(leaf_index) >> level) ^ 1;
        tweak_hash(pp, TWEAK_FILLER, level as u32, sibling as u32, seed)
    })
}
