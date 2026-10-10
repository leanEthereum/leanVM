//! A sparse rank-one constraint system over `E`.

use primitives::field::F192;

/// How many witness columns the two dummy constraints take (see [`R1cs::push_dummies`]).
pub(crate) const N_DUMMIES: usize = 6;

/// One sparse row of a matrix: `(column, coefficient)` pairs.
pub(crate) type Row = Vec<(u32, F192)>;

/// Rows `(A_x·z)(B_x·z) = (C_x·z)` over `z = (1, w)`: column 0 is the constant one.
///
/// The three matrices have one row per constraint.
#[derive(Clone, Debug, Default)]
pub(crate) struct R1cs {
    pub(crate) n_cols: usize,
    pub(crate) a: Vec<Row>,
    pub(crate) b: Vec<Row>,
    pub(crate) c: Vec<Row>,
}

impl R1cs {
    pub(crate) const fn n_rows(&self) -> usize {
        self.a.len()
    }

    /// The variables of the row cube: at least one, the rows past [`Self::n_rows`] being zero rows.
    pub(crate) const fn log_rows(&self) -> usize {
        let log = self.n_rows().next_power_of_two().trailing_zeros() as usize;
        if log == 0 { 1 } else { log }
    }

    /// `Az`, `Bz`, `Cz`, each zero-padded to `2^log_rows`.
    pub(crate) fn products(&self, z: &[F192]) -> [Vec<F192>; 3] {
        assert_eq!(z.len(), self.n_cols, "a value per column");
        assert!(
            self.b.len() == self.n_rows() && self.c.len() == self.n_rows(),
            "three matrices of one height"
        );
        let len = 1 << self.log_rows();
        [&self.a, &self.b, &self.c].map(|m| {
            let mut out: Vec<F192> = m
                .iter()
                .map(|row| {
                    row.iter()
                        .fold(F192::ZERO, |acc, &(y, coef)| acc + coef * z[y as usize])
                })
                .collect();
            out.resize(len, F192::ZERO);
            out
        })
    }

    #[cfg(test)]
    pub(crate) fn is_satisfied(&self, z: &[F192]) -> bool {
        z.first() == Some(&F192::ONE) && {
            let [az, bz, cz] = self.products(z);
            (az.iter().zip(&bz).zip(&cz)).all(|((&a, &b), &c)| a * b == c)
        }
    }

    /// Append the two dummy constraints `z[first]·z[first+1] = z[first+2]` and `z[first+3]·z[first+4] = z[first+5]`.
    ///
    /// Their operands are fresh and uniform ([`dummy_values`]), which is what hides the final `(a, b, c)` of the outer Spartan: each sits at a row of its own, so it adds a uniform term to each of the three evaluations.
    pub(crate) fn push_dummies(&mut self, first: usize) {
        assert!(
            first > 0 && first + N_DUMMIES <= self.n_cols,
            "the dummies are witness columns"
        );
        for k in [first, first + 3] {
            let unit = |y: usize| vec![(u32::try_from(y).expect("a column fits a u32"), F192::ONE)];
            self.a.push(unit(k));
            self.b.push(unit(k + 1));
            self.c.push(unit(k + 2));
        }
    }
}

/// The dummy constraints' columns: two uniform operand pairs and their products.
pub(crate) fn dummy_values(mut rand: impl FnMut() -> F192) -> [F192; N_DUMMIES] {
    let [a0, b0, a1, b1] = [rand(), rand(), rand(), rand()];
    [a0, b0, a0 * b0, a1, b1, a1 * b1]
}
