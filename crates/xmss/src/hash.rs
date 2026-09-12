//! The XMSS hash layer: [`tweak_hash`] is standard BLAKE2s of the exact byte
//! string `tweak | pp | payload`, for chain steps, Merkle nodes, WOTS public
//! keys, and message encodings alike.
//!
//! The 16-byte tweak makes every call site a distinct hash function
//! (multi-target separation, as in leanVM) and the public parameter separates
//! users. Standard BLAKE2s binds the exact payload length.
//!
//! Compression counts per call: chain step 1, Merkle node 1, message encoding
//! 2, WOTS public key 11. A full XMSS verification is a constant 144
//! compressions: 2 (encoding) + 99 (chains, fixed by the target sum) + 11
//! (tips) + 32 (Merkle path).

use crate::*;

pub const PROTOCOL_DOMAIN_SEP: u8 = 0;

// Tweak types (byte 1).
pub const TWEAK_TYPE_CHAIN: u8 = 1;
pub const TWEAK_TYPE_WOTS_PK: u8 = 2;
pub const TWEAK_TYPE_MERKLE: u8 = 3;
pub const TWEAK_TYPE_ENCODING: u8 = 4;

pub const TWEAK_LEN: usize = 16;
pub type Tweak = [u8; TWEAK_LEN];

/// A full 32-byte BLAKE2s chaining value/output.
pub const STATE_LEN: usize = 32;

/// `[protocol_domain_sep:1 | type:1 | layer:1 | zero:1 | p:4 | tree:4 | index:4]`, little endian.
/// XMSS sets `layer` and `tree` to zero.
/// `index` is the epoch (chain / wots_pk / encoding) or the Merkle node index;
/// `sub_position` is the chain position or the Merkle level.
pub fn make_tweak(tweak_type: u8, sub_position: u32, index: u32) -> Tweak {
    let mut tweak = [0u8; TWEAK_LEN];
    tweak[0] = PROTOCOL_DOMAIN_SEP;
    tweak[1] = tweak_type;
    tweak[4..8].copy_from_slice(&sub_position.to_le_bytes());
    tweak[12..16].copy_from_slice(&index.to_le_bytes());
    tweak
}

/// Standard BLAKE2s of the exact-length `tweak | pp | payload` byte string. One
/// compression for chain steps (48 bytes total) and Merkle nodes (64 bytes
/// total), more for the multi-block WOTS public-key and encoding inputs.
pub fn tweak_hash(pp: &PublicParam, tweak_type: u8, sub_position: u32, index: u32, payload: &[u8]) -> Digest {
    let mut hasher = primitives::hash::Hasher::new();
    hasher.update(&make_tweak(tweak_type, sub_position, index));
    hasher.update(pp);
    hasher.update(payload);
    hasher.finalize()[..DIGEST_LEN].try_into().unwrap()
}
