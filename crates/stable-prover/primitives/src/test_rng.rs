//! One deterministic generator for the stable tree's tests, so a test sees the same stream on every host. It sits
//! behind the `test-util` feature rather than `#[cfg(test)]`, so the other crates' tests can reach it.

use rand::{RngCore, SeedableRng, rngs::StdRng};

use crate::field::F128;

/// A seeded [`StdRng`] plus the draws this repo's tests actually need.
pub struct Rng(StdRng);

impl Rng {
    pub fn new(seed: u64) -> Self {
        Self(StdRng::seed_from_u64(seed))
    }

    pub fn next_u64(&mut self) -> u64 {
        self.0.next_u64()
    }

    pub fn bits(&mut self, n: usize) -> Vec<bool> {
        (0..n).map(|_| self.next_u64() & 1 != 0).collect()
    }

    pub fn ext(&mut self) -> F128 {
        F128::new(self.next_u64(), self.next_u64())
    }

    pub fn ext_vec(&mut self, n: usize) -> Vec<F128> {
        (0..n).map(|_| self.ext()).collect()
    }
}
