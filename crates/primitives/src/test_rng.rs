//! One deterministic generator for the whole workspace's tests, so a SIMD
//! kernel and its scalar oracle see the same stream on every host.
//!
//! Exported normally rather than under `#[cfg(test)]`: integration tests in
//! `pcs`, `flock` and `primitives` are separate crates and cannot reach a
//! test-only module.

use rand::{RngCore, SeedableRng, rngs::StdRng};

use crate::field::F192;

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
