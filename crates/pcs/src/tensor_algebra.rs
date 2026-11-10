// CREDIT: https://github.com/succinctlabs/flock (flock-core), MIT OR Apache-2.0.
// CREDIT: https://github.com/binius-zk/binius64, Apache-2.0.
// Copyright 2025 The Binius Developers
// Copyright 2025 Irreducible, Inc.
// Modifications copyright 2026 Succinct Labs, Benedikt Bunz, William Wang
// SPDX-License-Identifier: Apache-2.0 OR MIT
//
// Port of binius64's `crates/math/src/tensor_algebra.rs` for the 64-bit
// transition: K = F_{2^64} packing, E = GF(2^128) = K[y]/(y^2 + x*y + 1) opening field.

//! The rectangular `K ⊗ E` tensor-algebra transpose used by ring switching.

use primitives::field::{F64, F128};

use crate::pack::PACKING_WIDTH;

/// The degree of E = GF(2^128) over F_2 (the opening degree e).
pub const DEGREE_E: usize = 128;

/// Rectangular tensor-algebra transpose: `s_hat_v` (64 E-elements, the row
/// view of a `K (x)_F2 E` element) to `s_hat_u` (128 K-elements, the column
/// view).
///
/// ```text
///     bit i of s_hat_u[w]  ==  bit w of s_hat_v[i],   i in 0..64, w in 0..128
/// ```
///
/// `s_hat_u[w] = t_w` in the ring-switching construction.
pub fn transpose_s_hat(s_hat_v: &[F128; PACKING_WIDTH]) -> [F64; DEGREE_E] {
    let mut s_hat_u = [F64::ZERO; DEGREE_E];
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
    }
    s_hat_u
}

#[cfg(test)]
mod tests {
    use super::*;
    use primitives::test_rng::Rng;

    /// Bit w of an E element in the basis `x^i y^j`, `w = 64 j + i` (w in 0..128).
    fn ext_bit(e: F128, w: usize) -> u64 {
        e.to_limbs()[w / 64] >> (w % 64) & 1
    }

    #[test]
    fn rect_transpose_bit_relation() {
        let mut rng = Rng::new(1);
        let s_hat_v = std::array::from_fn(|_| rng.ext());
        let s_hat_u = transpose_s_hat(&s_hat_v);
        for i in 0..PACKING_WIDTH {
            for w in 0..DEGREE_E {
                assert_eq!(
                    (s_hat_u[w].0 >> i) & 1,
                    ext_bit(s_hat_v[i], w),
                    "bit ({i}, {w}) not transposed"
                );
            }
        }
    }
}
