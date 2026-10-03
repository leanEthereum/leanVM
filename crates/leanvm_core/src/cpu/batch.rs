//! The table sumcheck's batch (§constraints): one summand per table, then one per lookup producer.
//!
//! Prover and verifier both build it here, so their column order and summands agree by construction.

use super::layout::Layout;
use crate::colval::ColVal;
use crate::constraints::{self, Air};
use crate::leaf::BusForm;
use crate::tables;
use primitives::field::F192;

/// The two bus sides' weights in the batch, `1` and `xi`, shared by every table.
///
/// The sharing is what ties the batch to the bus.
///
/// With one power per side, the batch's target is `sum_s xi^s * R_s`, for the sides' table shares `R_s`.
///
/// The verifier derives the `R_s` from the leaf claims, so a wrong share surfaces as a constraint error.
///
/// With powers per table, the target would not factor through the `R_s`, and nothing would pin the tables' share.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) struct FormPowers([F192; 2]);

impl FormPowers {
    /// The powers of the challenge `xi`.
    pub(super) const fn new(xi: F192) -> Self {
        Self([F192::ONE, xi])
    }

    /// The weighted sum of one value per side.
    pub(super) fn combine(self, sides: [F192; 2]) -> F192 {
        self.0[0] * sides[0] + self.0[1] * sides[1]
    }

    /// Each table's claimed sum: its two bus forms, weighted.
    ///
    /// The prover needs them to build each round; the verifier only their total, which it derives.
    pub(super) fn table_sums(self, bus: &[Vec<F192>; 2]) -> Vec<F192> {
        (0..tables::tables().len())
            .map(|t| self.combine([bus[0][t], bus[1][t]]))
            .collect()
    }

    /// The weight of the push side, which the producers' summands sit on.
    pub(super) const fn push(self) -> F192 {
        self.0[0]
    }
}

/// The table sumcheck's batch: one air per table in schema order, then one per lookup producer.
pub(super) struct Batch(Vec<Air<Term>>);

impl Batch {
    /// The batch settling what the bus reduction left.
    ///
    /// # Arguments
    ///
    /// - `layout`: the tables' heights and the producers.
    /// - `forms`: each side's bus form per table.
    /// - `coefficients`: per producer, per bit, its block's selector on the push side.
    /// - `powers`: the bus sides' weights.
    pub(super) fn new(
        layout: &Layout,
        forms: &[Vec<BusForm>; 2],
        coefficients: &[Vec<F192>],
        powers: FormPowers,
    ) -> Self {
        // A table's term is one form, not two: the batch adds the sides' evaluations anyway.
        let tables = tables::tables()
            .iter()
            .zip(&layout.taus)
            .enumerate()
            .map(|(t, (table, &tau))| Air {
                tau,
                n_cols: table.n_committed_columns(),
                summand: Term::Table(BusForm::sum((0..2).map(|s| forms[s][t].scaled(powers.0[s])))),
            });

        // A producer's term: its bits, then its columns `P'_i`.
        let producers = layout.producers.iter().zip(coefficients).map(|(p, coefficients)| Air {
            tau: p.kappa,
            n_cols: 2 * p.bits,
            summand: Term::Producer(coefficients.iter().map(|&c| c * powers.push()).collect()),
        });
        Self(tables.chain(producers).collect())
    }

    /// The batch's airs, as the table sumcheck takes them.
    pub(super) fn airs(&self) -> &[Air<Term>] {
        &self.0
    }
}

/// One term of the batch: a table's, or a lookup producer's.
pub(super) enum Term {
    /// A table's two bus forms, already summed with their side weights.
    Table(BusForm),
    /// A producer's share of the push side (§sec:lookup), as each bit's block's selector, the push side's weight folded in.
    ///
    /// Bit `i`'s block owes the push side `sum_x eq(zeta, x) * (1 + b_i(x) * P'_i(x))`, at the block's selector.
    ///
    /// Its columns are its bits `b_i`, then `P'_i`, both sent; the program's claims bind the second half.
    ///
    /// The producer has no identity of its own.
    Producer(Vec<F192>),
}

impl constraints::Summand for Term {
    #[inline(always)]
    fn eval<T: ColVal>(&self, cols: &[T], quadratic: bool) -> F192 {
        match self {
            Self::Table(bus) => T::reduce(bus.eval_unreduced(cols, quadratic)),
            // `sum_i c_i * (1 + b_i * P'_i)`, whose quadratic part is the products.
            Self::Producer(coefficients) => {
                let n = coefficients.len();
                let products = (0..n).fold(T::lift(F192::ZERO), |acc, i| {
                    acc ^ (cols[i] * cols[n + i]).mul_e_unreduced(coefficients[i])
                });
                let constant = if quadratic {
                    F192::ZERO
                } else {
                    coefficients.iter().fold(F192::ZERO, |a, &b| a + b)
                };
                T::reduce(products) + constant
            }
        }
    }
}
