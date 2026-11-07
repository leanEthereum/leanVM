//! The hash-based signature schemes leanVM aggregates: leanXMSS, stateful, and
//! leanSPHINCS, stateless. Both sign with WOTS+C, so the recursion guest verifies
//! both with one walk; leanXMSS hashes with its own tweakable hash, and leanSPHINCS
//! with FIPS 205's.

#![cfg_attr(not(test), warn(unused_crate_dependencies))]

pub mod lean_sphincs;
pub mod lean_xmss;

use primitives::hash::Hasher;

/// The length both schemes cut a hash value to.
const N: usize = 16;

/// Both schemes' tweakable hash is `Truncate_16(H(prefix | address | payload))`,
/// the prefix being the public parameter and the address each scheme's own: a
/// hasher that has absorbed `prefix | address`.
fn hasher(prefix: &[u8; N], address: &[u8]) -> Hasher {
    let mut hasher = Hasher::new();
    hasher.update(prefix).update(address);
    hasher
}

/// `Truncate_16`: a hash value from a Keccak-256 output.
fn truncate(output: [u8; 32]) -> [u8; N] {
    output[..N].try_into().unwrap()
}
