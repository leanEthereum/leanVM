use backend::*;
use rand::{CryptoRng, RngExt};
use serde::{Deserialize, Serialize};

use crate::*;

/// No Debug: `pre_images` are the one-time secret keys.
pub struct WotsSecretKey {
    pre_images: [Digest; V],
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct WotsPublicKey(pub [Digest; V]);

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct WotsSignature {
    #[serde(
        with = "backend::array_serialization",
        bound(serialize = "F: Serialize", deserialize = "F: Deserialize<'de>")
    )]
    pub chain_tips: [Digest; V],
    pub randomness: Randomness,
}

impl WotsSecretKey {
    pub fn random(rng: &mut impl CryptoRng) -> Self {
        Self::new(rng.random())
    }

    pub const fn new(pre_images: [Digest; V]) -> Self {
        Self { pre_images }
    }

    /// Walks all `V` chains to their ends. Only key generation needs this (it hashes the WOTS
    /// public key into a Merkle leaf); signing walks each chain part-way instead, so it must not
    /// pay for the full walk.
    pub fn public_key(&self, public_param: PublicParam, slot: u32) -> WotsPublicKey {
        WotsPublicKey(std::array::from_fn(|i| {
            iterate_hash(&self.pre_images[i], CHAIN_LENGTH - 1, public_param, slot, i, 0)
        }))
    }

    pub(crate) fn sign_with_encoding(
        &self,
        randomness: Randomness,
        encoding: &[u8; V],
        public_param: PublicParam,
        slot: u32,
    ) -> WotsSignature {
        WotsSignature {
            chain_tips: std::array::from_fn(|i| {
                iterate_hash(&self.pre_images[i], encoding[i] as usize, public_param, slot, i, 0)
            }),
            randomness,
        }
    }
}

impl WotsSignature {
    pub fn recover_public_key(
        &self,
        message: &[F; MESSAGE_LEN_FE],
        slot: u32,
        xmss_pub_key: &XmssPublicKey,
    ) -> Option<WotsPublicKey> {
        let encoding = wots_encode(message, slot, xmss_pub_key, &self.randomness)?;
        Some(WotsPublicKey(std::array::from_fn(|i| {
            iterate_hash(
                &self.chain_tips[i],
                CHAIN_LENGTH - 1 - encoding[i] as usize,
                xmss_pub_key.public_param,
                slot,
                i,
                encoding[i] as usize,
            )
        })))
    }
}

impl WotsPublicKey {
    // Overwrite-sponge
    pub fn hash(&self, public_param: PublicParam, slot: u32) -> Digest {
        // state[0..8] = IV [tweak(2) | 00 | pp(4)]; state[8..16] = 0.
        let mut state = [F::ZERO; WIDTH];
        state[..TWEAK_LEN].copy_from_slice(&make_tweak(TWEAK_TYPE_WOTS_PK, 0, slot));
        state[4..4 + PUBLIC_PARAM_LEN_FE].copy_from_slice(&public_param);
        state = poseidon16_permute(state);
        for i in (0..V).step_by(2) {
            state[8..][..XMSS_DIGEST_LEN].copy_from_slice(&self.0[i]);
            state[8 + XMSS_DIGEST_LEN..].copy_from_slice(&self.0[i + 1]);
            state = poseidon16_permute(state);
        }
        state[CAPACITY..][..XMSS_DIGEST_LEN].try_into().unwrap()
    }
}

pub fn iterate_hash(
    a: &Digest,
    n: usize,
    public_param: PublicParam,
    slot: u32,
    chain_index: usize,
    start_step: usize,
) -> Digest {
    // Chain hash layout: left = [tweak (2) | zeros (2) | data (4)], right = [public_param(4) | zeros(4)].
    let right = build_right_chain_input(&public_param);
    (0..n).fold(*a, |acc, j| {
        let tweak = make_tweak(TWEAK_TYPE_CHAIN, chain_index * CHAIN_LENGTH + start_step + j, slot);
        let left = build_left_chain_input(tweak, &acc);
        poseidon16_compress_pair(&left, &right)[..XMSS_DIGEST_LEN]
            .try_into()
            .unwrap()
    })
}

pub fn wots_encode(
    message: &[F; MESSAGE_LEN_FE],
    slot: u32,
    xmss_pub_key: &XmssPublicKey,
    randomness: &Randomness,
) -> Option<[u8; V]> {
    let first_input_left = message;
    let mut first_input_right = [F::default(); DIGEST_LEN_FE];
    first_input_right[..RANDOMNESS_LEN_FE].copy_from_slice(randomness);
    first_input_right[RANDOMNESS_LEN_FE..][..TWEAK_LEN].copy_from_slice(&make_tweak(TWEAK_TYPE_ENCODING, 0, slot));
    let pre_compressed = poseidon16_compress_pair(first_input_left, &first_input_right);

    let mut second_input_right = [F::default(); DIGEST_LEN_FE];
    second_input_right[..PUBLIC_PARAM_LEN_FE].copy_from_slice(&xmss_pub_key.public_param);
    let compressed = poseidon16_compress_pair(&pre_compressed, &second_input_right);

    if compressed[..NUM_ENCODING_FE].iter().any(|&kb| kb == -F::ONE) {
        // ensures uniformity of encoding
        return None;
    }
    // Signing grinds this function until the encoding hits `TARGET_SUM`, so it runs on the
    // order of a thousand times per signature: keep it allocation-free.
    let mut words = [0usize; NUM_ENCODING_FE];
    for (word, &kb) in words.iter_mut().zip(&compressed[..NUM_ENCODING_FE]) {
        *word = kb.to_usize();
    }
    let mut encoding = [0u8; V];
    let mut sum = 0usize;
    for (i, out) in encoding.iter_mut().enumerate() {
        // Chunk i lives in word i / CHUNKS_PER_FE, at bit offset W * (i % CHUNKS_PER_FE).
        let chunk = ((words[i / CHUNKS_PER_FE] >> (W * (i % CHUNKS_PER_FE))) & (CHAIN_LENGTH - 1)) as u8;
        *out = chunk;
        sum += usize::from(chunk);
    }
    // Masking to W bits already guarantees every entry is below CHAIN_LENGTH, so the target sum
    // is the only remaining validity condition.
    (sum == TARGET_SUM).then_some(encoding)
}

#[cfg(test)]
mod tests {
    use rand::{RngExt, SeedableRng, rngs::StdRng};

    use super::*;

    /// Measures the average number of randomness attempts before a valid encoding.
    #[test]
    #[ignore]
    fn encoding_grinding_bits() {
        let n = 100;
        let xmss_pub_key = XmssPublicKey {
            merkle_root: Default::default(),
            public_param: Default::default(),
        };
        let total_iters = parallel::map_reduce(
            n,
            || 0usize,
            |i| {
                let message: [F; MESSAGE_LEN_FE] = Default::default();
                let slot = i as u32;
                let mut rng = StdRng::seed_from_u64(i as u64);
                let mut num_iters = 0;
                loop {
                    num_iters += 1;
                    let randomness: Randomness = rng.random();
                    if wots_encode(&message, slot, &xmss_pub_key, &randomness).is_some() {
                        break num_iters;
                    }
                }
            },
            |a, b| a + b,
        );
        let grinding = ((total_iters as f64) / (n as f64)).log2();
        println!("Average grinding bits: {:.1}", grinding);
    }
}
