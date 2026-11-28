//! The forms a table's links and identities are written in, and the claims on its columns.

use primitives::field::F128;

/// An evaluation claim on a committed column, settled against the witness.
/// Reconstructed identically by both sides (its value rides the stream).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ColumnClaim {
    pub col: usize,
    pub point: Vec<F128>,
    pub value: F128,
}

/// A degree-2 form over one table's committed columns, `Σ_c coeffs[c]·col_c(z) + Σ (a,b,c) c·col_a(z)·col_b(z) +
/// constant`: a link's payload folded by its challenges, or a table's identities.
#[derive(Clone, Debug)]
pub struct Form {
    pub coeffs: Vec<F128>,
    /// `(col_a, col_b, coeff)` in LOCAL column indices.
    pub(crate) prods: Vec<(usize, usize, F128)>,
    pub constant: F128,
}

impl Form {
    /// The zero form over `n_cols` columns.
    pub(crate) fn new(n_cols: usize) -> Self {
        Self {
            coeffs: vec![F128::ZERO; n_cols],
            prods: Vec::new(),
            constant: F128::ZERO,
        }
    }

    /// The verifier's form over a table of `n_cols` columns: the same polynomial.
    pub(crate) fn from_verifier(form: &verifier::layout::Form, n_cols: usize) -> Self {
        let mut out = Self::new(n_cols);
        for (monomial, c) in form.terms() {
            let c = F128::new(c.c0, c.c1);
            match *monomial {
                [] => out.constant += c,
                [a] => out.coeffs[a] += c,
                [a, b] => out.prods.push((a.min(b), a.max(b), c)),
                _ => unreachable!("a form has degree at most two"),
            }
        }
        out
    }

    /// `self += w·other`, over the same columns.
    pub(crate) fn add_scaled(&mut self, other: &Form, w: F128) {
        assert_eq!(self.coeffs.len(), other.coeffs.len(), "forms over the same columns");
        for (slot, &c) in self.coeffs.iter_mut().zip(&other.coeffs) {
            *slot += w * c;
        }
        self.prods.extend(other.prods.iter().map(|&(a, b, q)| (a, b, w * q)));
        self.constant += w * other.constant;
    }

    /// The same form scaled by `w`, once per table rather than once per row.
    pub fn scaled(&self, w: F128) -> Self {
        Self {
            coeffs: self.coeffs.iter().map(|&c| c * w).collect(),
            prods: self.prods.iter().map(|&(a, b, c)| (a, b, c * w)).collect(),
            constant: self.constant * w,
        }
    }

    /// The form at one point, `evals` the columns' values there; only its degree-two terms when `quadratic`.
    #[cfg(test)]
    pub(crate) fn eval(&self, evals: &[F128], quadratic: bool) -> F128 {
        let linear = if quadratic { F128::ZERO } else { self.linear(evals) };
        self.prods
            .iter()
            .fold(linear, |acc, &(a, b, c)| acc + evals[a] * evals[b] * c)
    }

    /// `constant + Σ coeffs[i]·evals[i]`.
    #[cfg(test)]
    fn linear(&self, evals: &[F128]) -> F128 {
        self.coeffs
            .iter()
            .zip(evals)
            .fold(self.constant, |acc, (&w, &v)| acc + w * v)
    }
}
