// CREDIT: https://github.com/succinctlabs/flock (flock-core), MIT OR Apache-2.0.
// CREDIT: https://github.com/binius-zk/binius64, Apache-2.0.
// Copyright 2025 The Binius Developers
// Copyright 2025 Irreducible, Inc.
// Modifications copyright 2026 Succinct Labs, Benedikt Bunz, William Wang
// SPDX-License-Identifier: Apache-2.0 OR MIT
//
// Port of binius64's `crates/math/src/tensor_algebra.rs` for the 64-bit
// transition: K = F_{2^64} packing, E = GF(2^192) tower opening field.

//! Tensor algebra for the rectangular `K ⊗ E` transpose used by ring switching.

use primitives::field::{F64, F192};

use crate::pack::PACKING_WIDTH;

/// The degree of E = GF(2^192) over F_2 (the opening degree e).
pub const DEGREE_E: usize = 192;

/// Rectangular tensor-algebra transpose: `s_hat_v` (64 E-elements, the row
/// view of a `K (x)_F2 E` element) to `s_hat_u` (192 K-elements, the column
/// view).
///
/// ```text
///     bit i of s_hat_u[w]  ==  bit w of s_hat_v[i],   i in 0..64, w in 0..192
/// ```
///
/// `s_hat_u[w] = t_w` in the ring-switching construction.
pub fn transpose_s_hat(s_hat_v: &[F192]) -> Vec<F64> {
    assert_eq!(
        s_hat_v.len(),
        PACKING_WIDTH,
        "transpose_s_hat: s_hat_v must have one entry per packing bit (64)"
    );
    let mut s_hat_u = vec![F64::ZERO; DEGREE_E];
    for (i, elem) in s_hat_v.iter().enumerate() {
        // Deposit bit w of elem into bit i of s_hat_u[w]; scan set bits only.
        let mut c0 = elem.c0;
        while c0 != 0 {
            let w = c0.trailing_zeros() as usize;
            s_hat_u[w].0 |= 1u64 << i;
            c0 &= c0 - 1;
        }
        let mut c1 = elem.c1;
        while c1 != 0 {
            let w = c1.trailing_zeros() as usize;
            s_hat_u[64 | w].0 |= 1u64 << i;
            c1 &= c1 - 1;
        }
        let mut c2 = elem.c2;
        while c2 != 0 {
            let w = c2.trailing_zeros() as usize;
            s_hat_u[128 | w].0 |= 1u64 << i;
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
            (e.c0 >> w) & 1
        } else if w < 128 {
            (e.c1 >> (w - 64)) & 1
        } else {
            (e.c2 >> (w - 128)) & 1
        }
    }

    #[test]
    fn rect_transpose_bit_relation() {
        let mut rng = Rng::new(1);
        let s_hat_v = rng.ext_vec(PACKING_WIDTH);
        let s_hat_u = transpose_s_hat(&s_hat_v);
        assert_eq!(s_hat_u.len(), DEGREE_E);
        for (i, &v) in s_hat_v.iter().enumerate() {
            for (w, &u) in s_hat_u.iter().enumerate() {
                assert_eq!((u.0 >> i) & 1, ext_bit(v, w), "bit ({i}, {w}) not transposed");
            }
        }
    }
}
