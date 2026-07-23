#![cfg_attr(not(test), warn(unused_crate_dependencies))]
use backend::{DIGEST_LEN_FE, KoalaBear, POSEIDON1_WIDTH, PrimeCharacteristicRing, PrimeField32, poseidon16_compress};

#[cfg(any(test, feature = "test-utils"))]
pub mod signers_cache;
mod ssz_serialization;
pub use ssz_serialization::{PUB_KEY_SSZ_LEN, SIGNATURE_SSZ_LEN};
mod wots;
// The rest of the WOTS layer (one-time secret keys, chain walking, encoding) is a private
// building block of xmss_sign / xmss_verify; only the signature type is part of the API.
pub use wots::WotsSignature;
mod xmss;
pub use xmss::*;

pub const XMSS_DIGEST_LEN: usize = 4;
pub(crate) const TWEAK_LEN: usize = 2;

/// The base field of the scheme.
pub type F = KoalaBear;
/// A truncated Poseidon digest: hash-chain values and Merkle tree nodes.
pub type Digest = [F; XMSS_DIGEST_LEN];
/// The per-key public parameter of the tweakable hash.
pub type PublicParam = [F; PUBLIC_PARAM_LEN_FE];
/// The encoding randomness carried in every signature.
pub type Randomness = [F; RANDOMNESS_LEN_FE];

// WOTS
pub const V: usize = 42;
pub const W: usize = 3;
pub const CHAIN_LENGTH: usize = 1 << W;
pub const NUM_CHAIN_HASHES: usize = 110;
pub const TARGET_SUM: usize = V * (CHAIN_LENGTH - 1) - NUM_CHAIN_HASHES;
pub const NUM_ENCODING_FE: usize = V.div_ceil(24 / W);
pub const RANDOMNESS_LEN_FE: usize = 6;
/// Byte length of the messages being signed.
pub const MESSAGE_LEN_BYTES: usize = 32;
/// Field elements of the injective base-p embedding of a message (p > 2^30, 9 * 30 >= 8 * 32).
pub(crate) const MESSAGE_EMBEDDING_LEN_FE: usize = 9;
/// Field elements of the hashed message, the form consumed by WOTS encoding (and the snark).
pub(crate) const MESSAGE_LEN_FE: usize = 8;
pub const PUBLIC_PARAM_LEN_FE: usize = 4;
pub const PUB_KEY_FLAT_SIZE: usize = XMSS_DIGEST_LEN + PUBLIC_PARAM_LEN_FE;
pub const WOTS_SIG_SIZE_FE: usize = RANDOMNESS_LEN_FE + V * XMSS_DIGEST_LEN;

// XMSS
pub const LOG_LIFETIME: usize = 32;

// Tweak: domain separation within each hash.
pub const TWEAK_TYPE_CHAIN: usize = 0;
pub const TWEAK_TYPE_WOTS_PK: usize = 1;
pub const TWEAK_TYPE_MERKLE: usize = 2;
pub const TWEAK_TYPE_ENCODING: usize = 3;

const _: () = assert!(V.is_multiple_of(2)); // For efficiency of the snark (we can batch chains in pairs)
const _: () = assert!(MESSAGE_EMBEDDING_LEN_FE * 30 >= MESSAGE_LEN_BYTES * 8); // Injective embedding
const _: () = assert!(MESSAGE_LEN_FE == DIGEST_LEN_FE); // hash_message output is one Poseidon digest
const _: () = assert!(MESSAGE_EMBEDDING_LEN_FE < POSEIDON1_WIDTH); // Domain sep + embedding fit

// Domain separators, placed in the first lane of a poseidon16_compress input. The window
// [336, 1024) is collision-free with every tweak first lane: chain tweaks with index_hi = 0
// stay below 336 (sub_position <= V * CHAIN_LENGTH - 1), any other tweak is >= 1024.
pub(crate) const PRF_DOMAINSEP_WOTS_SECRET_KEY: u32 = 1000;
pub(crate) const PRF_DOMAINSEP_PUBLIC_PARAM: u32 = 1001;
pub(crate) const PRF_DOMAINSEP_RANDOM_NODE: u32 = 1002;
pub(crate) const PRF_DOMAINSEP_SIGNATURE_RANDOMNESS: u32 = 1003;
pub(crate) const DOMAINSEP_MESSAGE_HASH: u32 = 1004;

/// Signing grinds the encoding randomness until the encoding is valid (expected: a few hundred
/// attempts); this bound only exists so a broken configuration fails instead of looping forever.
pub const MAX_SIGNING_ATTEMPTS: usize = 100_000;

/// Injective embedding of a message into `MESSAGE_EMBEDDING_LEN_FE` field elements:
/// little-endian base-p decomposition of the message read as a little-endian integer
/// (the same convention as leanSig's `encode_message`).
pub(crate) fn encode_message(message: &[u8; MESSAGE_LEN_BYTES]) -> [F; MESSAGE_EMBEDDING_LEN_FE] {
    let p = u64::from(F::ORDER_U32);
    let mut words: [u32; MESSAGE_LEN_BYTES / 4] =
        std::array::from_fn(|i| u32::from_le_bytes(message[4 * i..4 * (i + 1)].try_into().unwrap()));
    std::array::from_fn(|_| {
        // Long division of the little-endian `words` integer by p; the remainder is the limb.
        let mut rem: u64 = 0;
        for word in words.iter_mut().rev() {
            let cur = (rem << 32) | u64::from(*word);
            *word = (cur / p) as u32;
            rem = cur % p;
        }
        F::from_u64(rem)
    })
}

/// Off-circuit message hash: what gets signed (and what the snark consumes as "message") is
/// this domain-separated Poseidon digest of the 32-byte message.
#[doc(hidden)]
pub fn hash_message(message: &[u8; MESSAGE_LEN_BYTES]) -> [F; DIGEST_LEN_FE] {
    let mut input = [F::ZERO; POSEIDON1_WIDTH];
    input[0] = F::from_u32(DOMAINSEP_MESSAGE_HASH);
    input[1..1 + MESSAGE_EMBEDDING_LEN_FE].copy_from_slice(&encode_message(message));
    poseidon16_compress(input)
}

pub(crate) fn poseidon_prf(domain: u32, seed: &[u8; 32], indices: [usize; 2]) -> [F; DIGEST_LEN_FE] {
    let mut input = [F::ZERO; 16];
    input[0] = F::from_u32(domain);
    let mask: usize = (1 << 30) - 1;
    let mut high_bits = 0usize;
    for (i, word) in seed.as_chunks::<4>().0.iter().enumerate() {
        let w = u32::from_le_bytes(*word) as usize;
        input[1 + i] = F::from_usize(w & mask);
        high_bits |= (w >> 30) << (2 * i);
    }
    input[9] = F::from_usize(high_bits);

    for (i, &idx) in indices.iter().enumerate() {
        assert!(idx < 1 << 60);
        input[10 + 2 * i] = F::from_usize(idx & mask);
        input[11 + 2 * i] = F::from_usize(idx >> 30);
    }

    poseidon16_compress(input)
}

/// index = slot or node_index in Merkle tree
pub fn make_tweak(tweak_type: usize, sub_position: usize, index: u32) -> [F; TWEAK_LEN] {
    assert!(tweak_type < 4);
    assert!(sub_position < 1 << 10);
    let index_lo = (index & 0xFFFF) as usize;
    let index_hi = (index >> 16) as usize;
    [
        F::from_usize((tweak_type << 26) + (index_hi << 10) + sub_position),
        F::from_usize(index_lo),
    ]
}

/// [tweak(2) | zeros(2) | public_param(4) | left_child(4) | right_child(4)]
pub(crate) fn build_merkle_data(
    tweak: [F; TWEAK_LEN],
    public_param: &PublicParam,
    left_child: &Digest,
    right_child: &Digest,
) -> [F; POSEIDON1_WIDTH] {
    let mut data = [F::default(); POSEIDON1_WIDTH];
    data[..TWEAK_LEN].copy_from_slice(&tweak);
    // data[2..4] = zeros (default)
    data[DIGEST_LEN_FE - PUBLIC_PARAM_LEN_FE..][..PUBLIC_PARAM_LEN_FE].copy_from_slice(public_param);
    data[DIGEST_LEN_FE..][..XMSS_DIGEST_LEN].copy_from_slice(left_child);
    data[DIGEST_LEN_FE + XMSS_DIGEST_LEN..].copy_from_slice(right_child);
    data
}

/// [tweak(2) | zeros(2) | data(4)]
pub(crate) fn build_left_chain_input(tweak: [F; TWEAK_LEN], data: &Digest) -> [F; DIGEST_LEN_FE] {
    let mut left = [F::default(); DIGEST_LEN_FE];
    left[..TWEAK_LEN].copy_from_slice(&tweak);
    left[DIGEST_LEN_FE - XMSS_DIGEST_LEN..].copy_from_slice(data);
    left
}

/// [public_param(4) | zeros(4)]
pub(crate) fn build_right_chain_input(public_param: &PublicParam) -> [F; DIGEST_LEN_FE] {
    let mut right = [F::default(); DIGEST_LEN_FE];
    right[..PUBLIC_PARAM_LEN_FE].copy_from_slice(public_param);
    right
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Expected limbs computed independently (big-integer base-p decomposition, little-endian).
    #[test]
    fn encode_message_reference_vectors() {
        let cases: [([u8; 32], [u32; MESSAGE_EMBEDDING_LEN_FE]); 3] = [
            (
                std::array::from_fn(|i| i as u8),
                [
                    158200685, 22817125, 768861932, 1220633732, 741473605, 1829125427, 227592113, 282695284, 33,
                ],
            ),
            (
                [0xFF; 32],
                [
                    1539525976, 1261153412, 1969546126, 1544481308, 1871195519, 936857536, 333911385, 1230415057, 272,
                ],
            ),
            (
                std::array::from_fn(|i| if i % 2 == 0 { 0x00 } else { 0xFF }),
                [
                    1914907182, 1596164347, 55024625, 1538471654, 1366473412, 361154807, 606204774, 1101267152, 271,
                ],
            ),
        ];
        for (message, expected) in cases {
            assert_eq!(encode_message(&message).map(|l| l.as_canonical_u32()), expected);
        }
        assert_eq!(encode_message(&[0; 32]), [F::ZERO; MESSAGE_EMBEDDING_LEN_FE]);
    }
}
