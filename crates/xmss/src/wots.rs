//! WOTS (Winternitz one-time signature) with target-sum encoding.

use rand::{CryptoRng, Rng};
use serde::{Deserialize, Serialize};

use crate::*;

#[derive(Debug)]
pub struct WotsSecretKey {
    pre_images: [Digest; V],
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct WotsPublicKey(pub [Digest; V]);

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq, Hash)]
pub struct WotsSignature {
    #[serde(with = "crate::array_serialization")]
    pub chain_tips: [Digest; V],
    pub randomness: Randomness,
}

impl WotsSecretKey {
    pub const fn new(pre_images: [Digest; V]) -> Self {
        Self { pre_images }
    }

    /// Walk every chain to its tip. Only key generation needs this; signing
    /// stops each chain at its encoding digit.
    pub fn public_key(&self, public_param: &PublicParam, epoch: Epoch) -> WotsPublicKey {
        WotsPublicKey(std::array::from_fn(|i| {
            iterate_hash(&self.pre_images[i], CHAIN_LENGTH - 1, public_param, epoch, i, 0)
        }))
    }

    /// `encoding` and `randomness` come as a pair from
    /// [`find_randomness_for_wots_encoding`], which only returns a randomness
    /// whose encoding is valid.
    pub fn sign(
        &self,
        encoding: &[u8; V],
        randomness: Randomness,
        epoch: Epoch,
        public_param: &PublicParam,
    ) -> WotsSignature {
        WotsSignature {
            chain_tips: std::array::from_fn(|i| {
                iterate_hash(&self.pre_images[i], encoding[i] as usize, public_param, epoch, i, 0)
            }),
            randomness,
        }
    }
}

impl WotsSignature {
    pub fn recover_public_key(
        &self,
        message: &Message,
        epoch: Epoch,
        public_param: &PublicParam,
    ) -> Option<WotsPublicKey> {
        let encoding = wots_encode(message, epoch, public_param, &self.randomness)?;
        Some(WotsPublicKey(std::array::from_fn(|i| {
            iterate_hash(
                &self.chain_tips[i],
                CHAIN_LENGTH - 1 - encoding[i] as usize,
                public_param,
                epoch,
                i,
                encoding[i] as usize,
            )
        })))
    }
}

impl WotsPublicKey {
    /// The Merkle leaf: standard BLAKE2s over the tweak, public parameter, and
    /// 42 concatenated chain tips (704 bytes, 11 compressions).
    pub fn hash(&self, public_param: &PublicParam, epoch: Epoch) -> Digest {
        tweak_hash(public_param, TWEAK_TYPE_WOTS_PK, 0, epoch, self.0.as_flattened())
    }
}

/// One chain step (1 compression). The position `chain_index * CHAIN_LENGTH +
/// step` identifies the edge from chain value `step` to `step + 1`.
fn chain_step(public_param: &PublicParam, epoch: Epoch, chain_index: usize, step: usize, value: &Digest) -> Digest {
    let position = (chain_index * CHAIN_LENGTH + step) as u32;
    tweak_hash(public_param, TWEAK_TYPE_CHAIN, position, epoch, value)
}

/// Walk chain `chain_index` for `n` steps starting at chain value `start_step`.
fn iterate_hash(
    start: &Digest,
    steps: usize,
    public_param: &PublicParam,
    epoch: Epoch,
    chain_index: usize,
    start_step: usize,
) -> Digest {
    (0..steps).fold(*start, |value, offset| {
        chain_step(public_param, epoch, chain_index, start_step + offset, &value)
    })
}

pub fn find_randomness_for_wots_encoding(
    message: &Message,
    epoch: Epoch,
    public_param: &PublicParam,
    rng: &mut impl CryptoRng,
) -> (Randomness, [u8; V], usize) {
    let mut num_iters = 0;
    loop {
        num_iters += 1;
        let randomness: Randomness = rng.random();
        if let Some(encoding) = wots_encode(message, epoch, public_param, &randomness) {
            return (randomness, encoding, num_iters);
        }
    }
}

/// The target-sum encoding. `D = MD(msg | randomness | zeros)` under the
/// encoding tweak, truncated to 16 bytes: 2 standard BLAKE2s compressions over
/// the 96-byte exact input. `D`'s two little-endian 64-bit words each hold 21
/// chunks of 3 bits (the VM's word width budgets the monomial encoding at 64
/// bits per word: `g^k = x^k` only for `k < 64`): digit `i < 21` sits at bits
/// `3i` of word 0, digit `i >= 21` at bits `3(i-21)` of word 1. The encoding is
/// valid iff the leftover top bit of EACH word (bits 63 and 127) is zero AND
/// the chunks sum to [`TARGET_SUM`]. Grinding the top bits to zero makes each
/// digest word exactly `sum(e_i * 2^{3i})` of its 21 digits, so both words
/// decompose into the chunks with no slack term. In-circuit this is checked
/// over GF(2^64) per word by accumulating the dispatched digit literals against
/// `8^i` monomial weights (see `verify_sig` in `rec_aggregation`'s `guests/lean_ethereum.py`).
pub fn wots_encode(
    message: &Message,
    epoch: Epoch,
    public_param: &PublicParam,
    randomness: &Randomness,
) -> Option<[u8; V]> {
    let mut data = [0u8; 2 * STATE_LEN];
    data[..MESSAGE_LEN].copy_from_slice(message);
    data[MESSAGE_LEN..][..RANDOMNESS_LEN].copy_from_slice(randomness);
    let digest = tweak_hash(public_param, TWEAK_TYPE_ENCODING, 0, epoch, &data);

    let mut encoding = [0u8; V];
    let mut sum = 0;
    for (half, bytes) in digest.as_chunks::<8>().0.iter().enumerate() {
        let word = u64::from_le_bytes(*bytes);
        if word >> (W * V / 2) != 0 {
            return None;
        }
        for i in 0..V / 2 {
            let digit = ((word >> (W * i)) & (CHAIN_LENGTH as u64 - 1)) as u8;
            encoding[half * (V / 2) + i] = digit;
            sum += digit as usize;
        }
    }
    (sum == TARGET_SUM).then_some(encoding)
}
