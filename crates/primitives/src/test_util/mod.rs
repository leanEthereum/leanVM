//! Shared deterministic generators and BLAKE2s vectors for tests and benchmarks.
//!
//! The test-support feature lets other crates use these fixtures through development dependencies.

use rand::{RngCore, SeedableRng, rngs::StdRng};

use crate::field::F192;
use crate::hash::OUT_LEN;

/// A seeded [`StdRng`] plus the draws this repo's tests actually need.
pub struct Rng(StdRng);

impl Rng {
    pub fn new(seed: u64) -> Self {
        Self(StdRng::seed_from_u64(seed))
    }

    pub fn next_u32(&mut self) -> u32 {
        self.0.next_u32()
    }

    pub fn next_u64(&mut self) -> u64 {
        self.0.next_u64()
    }

    pub fn next_u8(&mut self) -> u8 {
        self.next_u32() as u8
    }

    pub fn bit(&mut self) -> bool {
        self.next_u64() & 1 != 0
    }

    pub fn bits(&mut self, n: usize) -> Vec<bool> {
        (0..n).map(|_| self.bit()).collect()
    }

    pub fn ext(&mut self) -> F192 {
        F192::new(self.next_u64(), self.next_u64(), self.next_u64())
    }

    pub fn ext_vec(&mut self, n: usize) -> Vec<F192> {
        (0..n).map(|_| self.ext()).collect()
    }
}

/// The official unkeyed BLAKE2s-256 test vectors, as `(input, digest)` pairs.
///
/// Input `n` is the `n` bytes `00 01 .. n-1`, for `n` in `0..256`: every length through four blocks.
///
/// `test_vectors.txt` is extracted from `testvectors/blake2-kat.json` of <https://github.com/BLAKE2/BLAKE2>:
///
/// ```text
/// jq -r '.[] | select(.hash == "blake2s" and .key == "") | .out' blake2-kat.json
/// ```
pub fn test_vectors() -> impl Iterator<Item = (Vec<u8>, [u8; OUT_LEN])> {
    let lines: Vec<&str> = include_str!("../hash/test_vectors.txt").lines().collect();
    assert_eq!(lines.len(), 256, "the vector file is truncated");
    lines.into_iter().enumerate().map(|(n, line)| {
        let input = (0..n).map(|i| i as u8).collect();
        let digest = std::array::from_fn(|i| u8::from_str_radix(&line[2 * i..2 * i + 2], 16).unwrap());
        (input, digest)
    })
}
