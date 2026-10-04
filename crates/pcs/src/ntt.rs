// CREDIT: https://github.com/succinctlabs/flock (flock-core), MIT OR Apache-2.0.
//! Additive NTTs (Lin-Chung-Han novel polynomial basis).
//!
//! Two transforms live here: [`AdditiveNttF64`] for WHIR commitments, and
//! [`AdditiveNttGf8`] (this file) plus [`inv_table`] for a small GF(2^8) NTT
//! used by flock's univariate-skip zerocheck round.

use primitives::field::F8;

pub mod additive_ntt_f64;
pub mod inv_table;
pub use additive_ntt_f64::{AdditiveNttF64, RowSink, transpose_lane_major};
pub use inv_table::InvNttTableByteSingleGf8;

/// Twiddle recurrence used to build the next subspace layer's evaluation points:
/// `next_s(s, root) = s² + root · s = s · (s + root)`.
#[inline]
fn next_s(s: F8, s_at_root: F8) -> F8 {
    s * (s + s_at_root)
}

/// Build the size-(2^k − 1) twiddle table for the additive NTT.
///
/// Layout: level-L twiddles live at offset (2^L − 1).
/// Level 0 has 2^{k-1} twiddles, level 1 has 2^{k-2}, …, level k−1 has 1.
fn compute_twiddles(k: usize, beta: F8) -> Vec<F8> {
    if k == 0 {
        return Vec::new();
    }
    let n = 1usize << k;
    let mut twiddles = vec![F8::ZERO; n - 1];

    // Layer 0: 2^{k-1} points beta + {0, 2, 4, ..., 2(write_at-1)}.
    let mut write_at = 1usize << (k - 1);
    let mut layer: Vec<F8> = (0..write_at).map(|i| beta + F8((2 * i) as u8)).collect();
    let mut s_at_root = F8::ONE;

    // Write layer 0 directly (s_at_root = 1 ⇒ no scaling needed).
    twiddles[write_at - 1..2 * write_at - 1].copy_from_slice(&layer[..write_at]);

    // Subsequent layers: halve the size, advance the recurrence, scale by s⁻¹.
    for _ in 1..k {
        write_at >>= 1;
        let next_s_root = next_s(layer[1] + layer[0], s_at_root);
        for i in 0..write_at {
            layer[i] = next_s(layer[2 * i], s_at_root);
        }
        s_at_root = next_s_root;

        let s_inv = s_at_root.inv();
        for j in 0..write_at {
            twiddles[write_at - 1 + j] = s_inv * layer[j];
        }
    }

    twiddles
}

#[inline]
fn fft_butterfly(v: &mut [F8], lambda: F8) {
    let n = v.len();
    let half = n >> 1;
    for i in 0..half {
        let w = v[half + i];
        v[i] += lambda * w;
        v[half + i] = w + v[i];
    }
}

fn fft_rec(v: &mut [F8], tw: &[F8], idx: usize) {
    let n = v.len();
    if n == 1 {
        return;
    }
    fft_butterfly(v, tw[idx - 1]);
    let half = n >> 1;
    let (lo, hi) = v.split_at_mut(half);
    fft_rec(lo, tw, 2 * idx);
    fft_rec(hi, tw, 2 * idx + 1);
}

#[inline]
fn ifft_butterfly(v: &mut [F8], lambda: F8) {
    let n = v.len();
    let half = n >> 1;
    for i in 0..half {
        v[half + i] += v[i];
        v[i] += lambda * v[half + i];
    }
}

fn ifft_rec(v: &mut [F8], tw: &[F8], idx: usize) {
    let n = v.len();
    if n == 1 {
        return;
    }
    let half = n >> 1;
    let (lo, hi) = v.split_at_mut(half);
    ifft_rec(lo, tw, 2 * idx);
    ifft_rec(hi, tw, 2 * idx + 1);
    ifft_butterfly(v, tw[idx - 1]);
}

/// Additive NTT over GF(2^8) with domain of size 2^k.
///
/// Evaluation domain `W = β + span{1, 2, …, 2^{k-1}}` (additive coset of an
/// F_2 subspace of F_{2^8}). Maximum useful `k` is 7 (|W| = 128); k = 8 would
/// exhaust all 256 elements of F_{2^8}.
///
/// Internal LCH basis: the forward transform maps coefficients in the
/// Lin-Chung-Han basis to evaluations at the 2^k points of the domain.
/// `inverse` is the exact reverse.
#[derive(Clone, Debug)]
pub struct AdditiveNttGf8 {
    k: usize,
    twiddles: Vec<F8>,
}

impl AdditiveNttGf8 {
    /// Build an NTT for a 2^k-point domain with offset β.
    pub fn new(k: usize, beta: F8) -> Self {
        Self {
            k,
            twiddles: compute_twiddles(k, beta),
        }
    }

    pub const fn k(&self) -> usize {
        self.k
    }
    const fn domain_size(&self) -> usize {
        1usize << self.k
    }

    pub fn forward(&self, v: &mut [F8]) {
        assert_eq!(v.len(), self.domain_size(), "forward: input length must be 2^k");
        if v.len() <= 1 {
            return;
        }
        fft_rec(v, &self.twiddles, 1);
    }

    pub fn inverse(&self, v: &mut [F8]) {
        assert_eq!(v.len(), self.domain_size(), "inverse: input length must be 2^k");
        if v.len() <= 1 {
            return;
        }
        ifft_rec(v, &self.twiddles, 1);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use primitives::test_util::Rng;

    fn rand_vec(rng: &mut Rng, n: usize) -> Vec<F8> {
        (0..n).map(|_| F8((rng.next_u64() & 0xff) as u8)).collect()
    }

    #[test]
    fn forward_inverse_roundtrip() {
        let mut rng = Rng::new(42);
        for k in 1..=7 {
            let ntt = AdditiveNttGf8::new(k, F8::ZERO);
            for _ in 0..8 {
                let original = rand_vec(&mut rng, 1 << k);
                let mut v = original.clone();
                ntt.forward(&mut v);
                ntt.inverse(&mut v);
                assert_eq!(v, original, "roundtrip failed at k={k}");
            }
        }
    }

    #[test]
    fn nonzero_beta_roundtrip() {
        let mut rng = Rng::new(45);
        for beta_v in [0x01u8, 0x42, 0xCA, 0xFF] {
            let beta = F8(beta_v);
            for k in 1..=6 {
                let ntt = AdditiveNttGf8::new(k, beta);
                let original = rand_vec(&mut rng, 1 << k);
                let mut v = original.clone();
                ntt.forward(&mut v);
                ntt.inverse(&mut v);
                assert_eq!(v, original, "beta={beta_v:#x}, k={k}");
            }
        }
    }
}
