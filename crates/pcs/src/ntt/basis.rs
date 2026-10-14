//! The novel polynomial basis of Lin, Chung and Han, over the standard basis `v_k = x^k` of `K`.
//!
//! ```text
//!     s_0(x)      = x
//!     s_{k+1}(x)  = s_k(x) (s_k(x) + s_k(v_k))           the subspace polynomials
//!     s'_k(x)     = s_k(x) / s_k(v_k)                     normalized: one at v_k
//!     X_j(x)      = prod_{k : bit k of j set} s'_k(x)      the basis polynomials
//! ```
//!
//! - `s_k` vanishes on the span of `v_0, ..., v_{k-1}`.
//! - `s_k` is GF(2)-linear.
//! - So `s'_k` at the point whose bits are `p` is a subset sum of its values at `v_k, v_{k+1}, ...`.
//!
//! Every value here lies in `K`.

use fiat_shamir::arith::Arith;
use primitives::field::{F64, F192};

/// The subspace polynomials of a domain of `2^log_n` points, and their normalizers.
#[derive(Clone, Debug)]
pub(crate) struct NovelBasis {
    /// Row `k`: `s'_k(v_j)` for `j = k..=log_n`, so its first entry is one.
    rows: Vec<Vec<F64>>,
    /// `s_k(v_k)` for `k = 0..=log_n`.
    normalizers: Vec<F64>,
    /// `1 / s_k(v_k)` for `k = 0..=log_n`.
    inverses: Vec<F64>,
}

impl NovelBasis {
    /// The basis on the domain spanned by `v_0, ..., v_{log_n - 1}`, with the normalizers up to `s_{log_n}`.
    ///
    /// Each normalizer is nonzero: `v_k` lies outside the span of `v_0, ..., v_{k-1}`, where `s_k` vanishes.
    ///
    /// Computed by the portable products, since the native verifier builds it too.
    ///
    /// # Panics
    ///
    /// Panics if `log_n > 63`, past the degree of `K`.
    pub(crate) fn new(log_n: usize) -> Self {
        assert!(log_n < F64::DEGREE, "a basis vector of K per variable");
        // Row 0 of the unnormalized table: s_0(v_j) = v_j.
        let mut row: Vec<F64> = (0..=log_n).map(|j| F64(1 << j)).collect();
        let mut rows = Vec::with_capacity(log_n + 1);
        loop {
            // The recurrence on every later basis vector: s_{k+1}(v_j) = s_k(v_j) (s_k(v_j) + s_k(v_k)).
            let next: Vec<F64> = row[1..].iter().map(|&s| s.mul_portable(s + row[0])).collect();
            rows.push(row);
            if next.is_empty() {
                break;
            }
            row = next;
        }
        // Row k's first entry is s_k(v_k): dividing by it normalizes the row.
        let normalizers: Vec<F64> = rows.iter().map(|row| row[0]).collect();
        let inverses: Vec<F64> = normalizers.iter().map(|s| s.inv_portable()).collect();
        for (row, &inverse) in rows.iter_mut().zip(&inverses) {
            row.iter_mut().for_each(|s| *s = s.mul_portable(inverse));
        }
        Self {
            rows,
            normalizers,
            inverses,
        }
    }

    /// The log of the domain's size.
    pub(crate) const fn log_n(&self) -> usize {
        self.rows.len() - 1
    }

    /// `s'_k(v_j)` for `j = k..=log_n`.
    pub(crate) fn row(&self, k: usize) -> &[F64] {
        &self.rows[k]
    }

    /// `1 / s_k(v_k)` for `k = 0..=log_n`.
    pub(crate) fn inverses(&self) -> &[F64] {
        &self.inverses
    }

    /// `s'_k` at the point of the domain whose bits are `point`.
    ///
    /// The bits below `k` add nothing, since `s'_k` vanishes on `v_0, ..., v_{k-1}`.
    pub(crate) fn at_point(&self, k: usize, point: usize) -> F64 {
        subset_sum(&self.rows[k], point >> k)
    }

    /// `s'_k(x)` for every `k < out.len()`, by the recurrence from `s_0(x) = x`.
    pub(crate) fn normalized_at(&self, x: F64, out: &mut [F64]) {
        let mut s = x;
        for (k, o) in out.iter_mut().enumerate() {
            if k > 0 {
                s *= s + self.normalizers[k - 1];
            }
            *o = s * self.inverses[k];
        }
    }

    /// `s'_k(x)` alone, by the recurrence on the portable products, as the native verifier computes it.
    pub(crate) fn normalized_portable(&self, x: F64, k: usize) -> F64 {
        let s = (0..k).fold(x, |s, j| s.mul_portable(s + self.normalizers[j]));
        s.mul_portable(self.inverses[k])
    }

    /// `s_{k+1}(x)` from `s = s_k(x)`, as `s^2 + s_k(v_k) s`.
    ///
    /// The prover, the native verifier and the recursion machine's rows all step through it.
    pub(crate) fn next<A: Arith>(&self, a: &mut A, s: A::E, k: usize) -> A::E {
        let scaled = a.mul_const(s, F192::from(self.normalizers[k]));
        a.mul_add(s, s, scaled)
    }
}

/// The basis polynomials `X_j` at a point, for `j < 2^n`, from the normalized `s'_k` there, `k < n`.
///
/// Each value doubles the table: `X_{j + 2^k} = X_j s'_k` for `j < 2^k`.
pub(crate) fn basis_values(normalized: &[F64]) -> Vec<F64> {
    let mut table = vec![F64::ONE; 1 << normalized.len()];
    for (k, &s_k) in normalized.iter().enumerate() {
        let (lo, hi) = table.split_at_mut(1 << k);
        for (h, &l) in hi[..1 << k].iter_mut().zip(lo.iter()) {
            *h = l * s_k;
        }
    }
    table
}

/// The subset sum `sum_j bit_j(index) * entries[j]`.
#[inline]
pub(super) fn subset_sum(entries: &[F64], index: usize) -> F64 {
    let mut acc = F64::ZERO;
    for (j, &b) in entries.iter().enumerate() {
        if (index >> j) & 1 == 1 {
            acc += b;
        }
    }
    acc
}

#[cfg(test)]
mod tests {
    use super::*;
    use fiat_shamir::arith::Native;

    #[test]
    fn the_table_and_the_recurrence_agree() {
        // Invariant: every way of reaching `s'_k` gives the same value.
        //
        //     table:       subset sums of the values at the basis vectors
        //     recurrence:  s_{k+1} = s_k (s_k + s_k(v_k)), natively, portably and through the arithmetic
        //
        // Fixture state: a 12-variable domain, at points spread over it.
        let basis = NovelBasis::new(12);
        for point in (0..1usize << 12).step_by(97).chain([(1 << 12) - 1]) {
            let mut normalized = [F64::ZERO; 12];
            basis.normalized_at(F64(point as u64), &mut normalized);
            let mut s = F192::from(F64(point as u64));
            for (k, &want) in normalized.iter().enumerate() {
                assert_eq!(basis.at_point(k, point), want, "point {point}, k {k}");
                assert_eq!(
                    basis.normalized_portable(F64(point as u64), k),
                    want,
                    "point {point}, k {k}"
                );
                assert_eq!(
                    s.mul_base(basis.inverses()[k]),
                    F192::from(want),
                    "point {point}, k {k}"
                );
                s = basis.next(&mut Native, s, k);
            }
        }
    }
}
