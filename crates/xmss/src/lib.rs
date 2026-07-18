#![cfg_attr(not(test), warn(unused_crate_dependencies))]
use backend::{DIGEST_LEN_FE, KoalaBear, POSEIDON1_WIDTH, PrimeCharacteristicRing, poseidon16_compress};

pub mod signers_cache;
mod wots;
pub use wots::*;
mod xmss;
pub use xmss::*;

pub const XMSS_DIGEST_LEN: usize = 4;
pub(crate) const TWEAK_LEN: usize = 2;

type F = KoalaBear;
type Digest = [F; XMSS_DIGEST_LEN];
type PublicParam = [F; PUBLIC_PARAM_LEN_FE];
type Randomness = [F; RANDOMNESS_LEN_FE];

// WOTS
pub const V: usize = 42;
pub const W: usize = 3;
pub const CHAIN_LENGTH: usize = 1 << W;
pub const NUM_CHAIN_HASHES: usize = 110;
pub const TARGET_SUM: usize = V * (CHAIN_LENGTH - 1) - NUM_CHAIN_HASHES;
pub const NUM_ENCODING_FE: usize = V.div_ceil(24 / W);
pub const RANDOMNESS_LEN_FE: usize = 6;
pub const MESSAGE_LEN_FE: usize = 8;
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

pub(crate) const PRF_DOMAINSEP_WOTS_SECRET_KEY: u32 = 1000;
pub(crate) const PRF_DOMAINSEP_PUBLIC_PARAM: u32 = 1001;
pub(crate) const PRF_DOMAINSEP_RANDOM_NODE: u32 = 1002;

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
