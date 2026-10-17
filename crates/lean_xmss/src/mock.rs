//! Keys real only over a short range of leaf indices, every node over no leaf in it
//! a pseudorandom filler. In that range they sign like a full key, and verify with
//! [`crate::verify`], for a fraction of its key generation. For tests and
//! benchmarks: signing outside the range panics.
//!
//! A seed must back ONE key: never a mock key and the full key, nor two mock keys
//! over different ranges. They share every one-time key but not their bottom roots,
//! so the same top one-time key would sign two roots, and its signatures would
//! forge others.

use crate::*;

pub fn key_gen_from_seed(seed: Seed, first: LeafIndex, last: LeafIndex) -> (LeanXmssSecretKey, LeanXmssPublicKey) {
    assert!(first <= last, "an empty range");
    generate(seed, first, last)
}
