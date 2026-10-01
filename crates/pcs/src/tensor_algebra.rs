// CREDIT: https://github.com/succinctlabs/flock (flock-core), MIT OR Apache-2.0.
// CREDIT: https://github.com/binius-zk/binius64, Apache-2.0.
// Copyright 2025 The Binius Developers
// Copyright 2025 Irreducible, Inc.
// Modifications copyright 2026 Succinct Labs, Benedikt Bunz, William Wang
// SPDX-License-Identifier: Apache-2.0 OR MIT
//
// Port of binius64's `crates/math/src/tensor_algebra.rs` for the 64-bit
// transition: K = F_{2^64} packing, E = GF(2^192) tower opening field.

//! Tensor algebra for the rectangular `K ⊗ E` transpose and square `E ⊗ E` operations used by ring switching.

use core::ops::AddAssign;
use primitives::field::{F64, F192};

use crate::pack::PACKING_WIDTH;

/// The degree of E = GF(2^192) over F_2 (the opening degree e).
pub const DEGREE_E: usize = 192;

/// Bit w of an E element in the tower basis (w in 0..192).
#[inline(always)]
const fn ext_bit(e: F192, w: usize) -> u64 {
    if w < 64 {
        (e.c0 >> w) & 1
    } else if w < 128 {
        (e.c1 >> (w - 64)) & 1
    } else {
        (e.c2 >> (w - 128)) & 1
    }
}

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

/// An element of `E (x)_F2 E` (E = the tower GF(2^192)), stored as 192
/// `F192` elements: `elems[i]` is the second-factor component attached to
/// the i-th F_2-basis element of the first factor, i.e.
/// `bit_j(elems[i])` = the coefficient of `b_i (x) b_j`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TensorAlgebraE {
    /// Length-192 vector; see the struct docs for the indexing convention.
    pub elems: Vec<F192>,
}

impl TensorAlgebraE {
    /// Embed `x` into the vertical subring: returns `1 (x) x`.
    pub fn from_vertical(x: F192) -> Self {
        let mut elems = vec![F192::ZERO; DEGREE_E];
        elems[0] = x;
        Self { elems }
    }

    /// Multiply by an element of the vertical subring (`1 (x) scalar`): each
    /// `elems[i]` is scaled by `scalar` in E.
    pub fn scale_vertical(mut self, scalar: F192) -> Self {
        for e in self.elems.iter_mut() {
            *e *= scalar;
        }
        self
    }

    /// Multiply by an element of the horizontal subring (`scalar (x) 1`).
    /// Implemented as `transpose . scale_vertical . transpose`.
    pub fn scale_horizontal(self, scalar: F192) -> Self {
        self.transpose().scale_vertical(scalar).transpose()
    }

    /// Transpose: swap the two tensor factors. Concretely, after transpose,
    /// `bit_j(elems'[i]) = bit_i(elems[j])` for all `i, j in [0, 192)`.
    pub fn transpose(mut self) -> Self {
        square_transpose_ext(&mut self.elems);
        self
    }

    /// Fold to a single E element: transpose, then scale row `w` by
    /// `coeffs[w]` and sum.
    ///
    /// Computes `sum_w coeffs[w] * transpose(self).elems[w]`. With `self =
    /// sum_y eq(query, y) (x) eq(z, y)` and `coeffs = eq(r'')` this is the
    /// MLE of `rs_eq_ind` at `query` (see `ring_switch::eval_rs_eq`).
    pub fn fold_vertical(self, coeffs: &[F192]) -> F192 {
        assert_eq!(coeffs.len(), DEGREE_E, "fold_vertical: coeffs.len() must be 192");
        let transposed = self.transpose();
        let mut acc = F192::ZERO;
        for (e, c) in transposed.elems.iter().zip(coeffs.iter()) {
            acc += *e * *c;
        }
        acc
    }
}

impl AddAssign<&Self> for TensorAlgebraE {
    fn add_assign(&mut self, rhs: &Self) {
        for (a, b) in self.elems.iter_mut().zip(rhs.elems.iter()) {
            *a = *a + *b;
        }
    }
}

/// In-place 192x192 F_2 matrix transpose of the F192 coefficient table.
///
/// On input: `elems[i]` viewed as a 192-bit row; bit `j` (tower basis) is the
/// F_2 coefficient at position `(i, j)`. On output: bit `j` of `elems[i]`
/// becomes the old bit `i` of `elems[j]`.
fn square_transpose_ext(elems: &mut [F192]) {
    assert_eq!(elems.len(), DEGREE_E, "square_transpose_ext: input must be length 192");

    let mut out = [F192::ZERO; DEGREE_E];
    for (j, o) in out.iter_mut().enumerate() {
        let mut c0: u64 = 0;
        let mut c1: u64 = 0;
        let mut c2: u64 = 0;
        for (i, &elem) in elems[0..64].iter().enumerate() {
            c0 |= ext_bit(elem, j) << i;
        }
        for (i, &elem) in elems[64..128].iter().enumerate() {
            c1 |= ext_bit(elem, j) << i;
        }
        for (i, &elem) in elems[128..192].iter().enumerate() {
            c2 |= ext_bit(elem, j) << i;
        }
        *o = F192::new(c0, c1, c2);
    }
    elems.copy_from_slice(&out);
}

#[cfg(test)]
mod tests {
    use super::*;
    use primitives::test_rng::Rng;

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

    #[test]
    fn square_transpose_is_involution() {
        let mut rng = Rng::new(2);
        let orig = rng.ext_vec(DEGREE_E);
        let t = TensorAlgebraE { elems: orig.clone() };
        let tt = t.transpose();
        // Bit relation on a spot-check diagonal band plus full involution.
        for i in 0..DEGREE_E {
            for w in [0usize, 1, 63, 64, 65, 127] {
                assert_eq!(ext_bit(tt.elems[i], w), ext_bit(orig[w], i));
            }
        }
        assert_eq!(tt.transpose().elems, orig, "transpose twice must be id");
    }

    /// `fold_vertical(from_vertical(x), coeffs)` is exactly the F_2-linear
    /// map Phi sending the w-th E-basis bit to coeffs[w], applied to x. This
    /// is the map the ring switch uses to define `rs_eq_ind`.
    #[test]
    fn fold_vertical_is_phi() {
        let mut rng = Rng::new(3);
        let coeffs = rng.ext_vec(DEGREE_E);
        let x = rng.ext();
        let folded = TensorAlgebraE::from_vertical(x).fold_vertical(&coeffs);
        let mut expected = F192::ZERO;
        for (w, &c) in coeffs.iter().enumerate() {
            if ext_bit(x, w) == 1 {
                expected += c;
            }
        }
        assert_eq!(folded, expected);
    }
}
