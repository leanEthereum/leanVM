//! Polynomials of degree at most two over one table's columns, the shape every link and identity is written in.

use primitives::field::{F64, F128};

/// `constant + Σ_c coeffs[c]·col_c + Σ q·col_a·col_b` over `prods`, in the table's local column indices.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Form {
    pub coeffs: Vec<F128>,
    /// `(a, b, q)` with `a ≤ b`.
    pub prods: Vec<(usize, usize, F128)>,
    pub constant: F128,
}

impl Form {
    /// The zero form over `n_cols` columns.
    pub fn new(n_cols: usize) -> Self {
        Self {
            coeffs: vec![F128::ZERO; n_cols],
            prods: Vec::new(),
            constant: F128::ZERO,
        }
    }

    /// The verifier's form over a table of `n_cols` columns: the same polynomial.
    pub fn from_verifier(form: &verifier::layout::Form, n_cols: usize) -> Self {
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

    /// The form scaled by `w`.
    pub fn scaled(&self, w: F128) -> Self {
        Self {
            coeffs: self.coeffs.iter().map(|&c| c * w).collect(),
            prods: self.prods.iter().map(|&(a, b, q)| (a, b, q * w)).collect(),
            constant: self.constant * w,
        }
    }

    /// `self += w·other`, over the same columns.
    pub fn add_scaled(&mut self, other: &Form, w: F128) {
        assert_eq!(self.coeffs.len(), other.coeffs.len(), "forms over the same columns");
        for (slot, &c) in self.coeffs.iter_mut().zip(&other.coeffs) {
            *slot += w * c;
        }
        self.prods.extend(other.prods.iter().map(|&(a, b, q)| (a, b, w * q)));
        self.constant += w * other.constant;
    }

    /// Whether the form has no product.
    pub fn is_affine(&self) -> bool {
        self.prods.iter().all(|&(_, _, q)| q.is_zero())
    }

    /// The form at one row, `row[c]` column `c`'s value there.
    pub fn evaluate(&self, row: &[F128]) -> F128 {
        let linear = (self.coeffs.iter().zip(row)).fold(self.constant, |acc, (&w, &v)| acc + w * v);
        (self.prods.iter()).fold(linear, |acc, &(a, b, q)| acc + q * row[a] * row[b])
    }

    /// The form at one row of `K` columns, `row(c)` column `c`'s value there.
    pub fn evaluate_k(&self, row: impl Fn(usize) -> F64) -> F128 {
        let linear = (self.coeffs.iter().enumerate())
            .filter(|(_, w)| !w.is_zero())
            .fold(self.constant, |acc, (c, w)| acc + w.mul_base(row(c)));
        (self.prods.iter()).fold(linear, |acc, &(a, b, q)| acc + q.mul_base(row(a) * row(b)))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use primitives::test_rng::Rng;

    /// Every table's link forms, converted, are the verifier's polynomials.
    #[test]
    fn converted_forms_evaluate_as_the_verifiers() {
        let mut rng = Rng::new(0xf0);
        for table in verifier::layout::tables() {
            let n = table.width();
            let row: Vec<F128> = rng.ext_vec(n);
            let row_e: Vec<verifier::E> = row.iter().map(|v| verifier::E::new(v.c0, v.c1)).collect();
            let links = &table.links;
            let state = links.state();
            let mut forms: Vec<&verifier::layout::Form> = state.next.iter().collect();
            forms.extend(links.bytecode_link().operands.iter().map(|(_, f)| f));
            for access in &links.memory {
                forms.extend([&access.address, &access.value]);
            }
            for form in forms {
                let ours = Form::from_verifier(form, n);
                let theirs = form.evaluate(&row_e);
                assert_eq!(ours.evaluate(&row), F128::new(theirs.c0, theirs.c1));
                let k: Vec<F64> = row.iter().map(|v| F64(v.c0)).collect();
                let k_e: Vec<verifier::E> = k.iter().map(|v| verifier::E::new(v.0, 0)).collect();
                let theirs = form.evaluate(&k_e);
                assert_eq!(ours.evaluate_k(|c| k[c]), F128::new(theirs.c0, theirs.c1));
            }
        }
    }
}
