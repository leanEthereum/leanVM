// CREDIT: https://github.com/succinctlabs/flock (flock-core), MIT OR Apache-2.0.
// CREDIT: https://github.com/binius-zk/binius64, Apache-2.0.
// Copyright 2025 The Binius Developers
// Copyright 2025 Irreducible, Inc.
// Modifications copyright 2026 Succinct Labs, Benedikt Bunz, William Wang
// SPDX-License-Identifier: Apache-2.0 OR MIT
//
// Port of binius64's `crates/math/src/tensor_algebra.rs` for the 64-bit
// transition: K = F_{2^64} packing, E = GF(2^192) tower opening field.

//! Tensor algebra for the rectangular `K ⊗ E` transpose: the column view of ring switching, which its tests check the map's coordinate weights against.

use primitives::PrimeCharacteristicRing;

use primitives::{F64, F192};

/// Rectangular tensor-algebra transpose: `s_hat_v` (64 E-elements, the row
/// view of a `K (x)_F2 E` element) to `s_hat_u` (192 K-elements, the column
/// view).
///
/// ```text
///     bit i of s_hat_u[w]  ==  bit w of s_hat_v[i],   i in 0..64, w in 0..192
/// ```
///
/// `s_hat_u[w] = t_w` in the ring-switching construction.
pub(crate) fn transpose_s_hat(s_hat_v: &[F192]) -> Vec<F64> {
    assert_eq!(
        s_hat_v.len(),
        64,
        "transpose_s_hat: s_hat_v must have one entry per packing bit (64)"
    );
    let mut s_hat_u = vec![F64::ZERO; 3 * 64];
    for (i, elem) in s_hat_v.iter().enumerate() {
        // Deposit bit w of elem into bit i of s_hat_u[w]; scan set bits only.
        let mut c0 = elem.coefficients()[0].to_bits();
        while c0 != 0 {
            let w = c0.trailing_zeros() as usize;
            s_hat_u[w] += F64::new(1u64 << i);
            c0 &= c0 - 1;
        }
        let mut c1 = elem.coefficients()[1].to_bits();
        while c1 != 0 {
            let w = c1.trailing_zeros() as usize;
            s_hat_u[64 | w] += F64::new(1u64 << i);
            c1 &= c1 - 1;
        }
        let mut c2 = elem.coefficients()[2].to_bits();
        while c2 != 0 {
            let w = c2.trailing_zeros() as usize;
            s_hat_u[128 | w] += F64::new(1u64 << i);
            c2 &= c2 - 1;
        }
    }
    s_hat_u
}

#[cfg(test)]
mod tests {
    use super::*;
    use primitives::test_util::Rng;

    /// Bit w of an E element in the tower basis (w in 0..192).
    const fn ext_bit(e: F192, w: usize) -> u64 {
        if w < 64 {
            (e.coefficients()[0].to_bits() >> w) & 1
        } else if w < 128 {
            (e.coefficients()[1].to_bits() >> (w - 64)) & 1
        } else {
            (e.coefficients()[2].to_bits() >> (w - 128)) & 1
        }
    }

    #[test]
    fn rect_transpose_bit_relation() {
        let mut rng = Rng::new(1);
        let s_hat_v = rng.ext_vec(64);
        let s_hat_u = transpose_s_hat(&s_hat_v);
        assert_eq!(s_hat_u.len(), 192);
        for (i, &v) in s_hat_v.iter().enumerate() {
            for (w, &u) in s_hat_u.iter().enumerate() {
                assert_eq!((u.to_bits() >> i) & 1, ext_bit(v, w), "bit ({i}, {w}) not transposed");
            }
        }
    }
}
