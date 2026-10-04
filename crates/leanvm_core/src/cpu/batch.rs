//! The table sumcheck's batch (§constraints): one summand per table, then one per lookup producer.
//!
//! Prover and verifier both build it here, so their column order and summands agree by construction.

use super::layout::Layout;
use crate::arith::{Arith, Native};
use crate::colval::ColVal;
use crate::constraints::{self, Air, Residual};
use crate::leaf::{self, BusForm, BusVerify, Producer};
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
pub(crate) struct FormPowers<E = F192>([E; 2]);

impl<E: Copy> FormPowers<E> {
    /// The powers of the challenge `xi`.
    pub(crate) fn new<A: Arith<E = E>>(a: &mut A, xi: E) -> Self {
        Self([a.one(), xi])
    }

    /// The weighted sum of one value per side.
    pub(crate) fn combine<A: Arith<E = E>>(self, a: &mut A, sides: [E; 2]) -> E {
        let push = a.mul(self.0[0], sides[0]);
        a.mul_add(self.0[1], sides[1], push)
    }

    /// The weight of side `s`: the push side, which the producers' summands sit on, is side 0.
    pub(crate) const fn side(self, s: usize) -> E {
        self.0[s]
    }

    /// The weight of the push side, which the producers' summands sit on.
    pub(crate) const fn push(self) -> E {
        self.side(0)
    }
}

impl FormPowers {
    /// Each table's claimed sum: its two bus forms, weighted.
    ///
    /// The prover needs them to build each round; the verifier only their total, which it derives.
    pub(super) fn table_sums(self, bus: &[Vec<F192>; 2]) -> Vec<F192> {
        (0..tables::ClassTable::all().len())
            .map(|t| self.combine(&mut Native, [bus[0][t], bus[1][t]]))
            .collect()
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
    /// - `weights`, `beta`: the bus fingerprint, which the producers' public columns are made of.
    /// - `powers`: the bus sides' weights.
    pub(super) fn new(
        layout: &Layout,
        forms: &[Vec<BusForm>; 2],
        coefficients: &[Vec<F192>],
        weights: &[F192],
        beta: F192,
        powers: FormPowers,
    ) -> Self {
        // A table's term is one form, not two: the batch adds the sides' evaluations anyway.
        let tables = tables::ClassTable::all()
            .iter()
            .zip(&layout.taus)
            .enumerate()
            .map(|(t, (table, &tau))| Air {
                tau,
                n_cols: table.n_committed_columns(),
                n_public: 0,
                summand: Term::Table(BusForm::sum((0..2).map(|s| forms[s][t].scaled(powers.0[s])))),
            });

        // A producer's term: its bits, then its public columns.
        let producers = layout.producers.iter().zip(coefficients).map(|(p, coefficients)| Air {
            tau: p.kappa,
            n_cols: 2 * p.bits,
            n_public: p.bits,
            summand: Term::Producer(ProducerTerm {
                coefficients: coefficients.iter().map(|&c| c * powers.push()).collect(),
                producer: p.clone(),
                weights: weights.to_vec(),
                beta,
            }),
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
    /// A producer's share of the push side.
    Producer(ProducerTerm),
}

/// A producer's term (§sec:lookup).
///
/// Bit `i`'s block owes the push side `sum_x eq(zeta, x) * (1 + b_i(x) * P'_i(x))`, at the block's selector.
///
/// Its columns are its bits `b_i`, which are sent, then its public `P'_i`, which the verifier computes.
///
/// The producer has no identity of its own.
pub(super) struct ProducerTerm {
    /// Per bit, its block's selector, the push side's weight folded in.
    coefficients: Vec<F192>,
    /// The producer the term is for.
    producer: Producer,
    /// The fingerprint's weights `eq(alpha, .)`, which its public columns are made of.
    weights: Vec<F192>,
    /// The fingerprint's offset.
    beta: F192,
}

impl constraints::Summand for Term {
    #[inline(always)]
    fn eval<T: ColVal>(&self, cols: &[T], quadratic: bool) -> F192 {
        match self {
            Self::Table(bus) => T::reduce(bus.eval_unreduced(cols, quadratic)),
            // `sum_i c_i * (1 + b_i * P'_i)`, whose quadratic part is the products.
            Self::Producer(s) => {
                let n = s.coefficients.len();
                let products = (0..n).fold(T::lift(F192::ZERO), |acc, i| {
                    acc ^ (cols[i] * cols[n + i]).mul_e_unreduced(s.coefficients[i])
                });
                let constant = if quadratic {
                    F192::ZERO
                } else {
                    s.coefficients.iter().fold(F192::ZERO, |a, &b| a + b)
                };
                T::reduce(products) + constant
            }
        }
    }

    fn public(&self, chi: &[F192]) -> Vec<F192> {
        match self {
            Self::Table(_) => Vec::new(),
            // Short of the program's columns, which the program claim settles.
            Self::Producer(s) => leaf::producer_affine_evals(&mut Native, &s.producer, &s.weights, s.beta, chi),
        }
    }
}

/// One term of the batch as the verifiers evaluate it at the sumcheck's point, over their arithmetic.
///
/// The prover's terms fold the sides' weights into one form; these weigh each side's form once, which costs fewer rows.
pub(crate) enum OwedTerm<'a, E> {
    /// A table's bus form on each side, and the sides' weights.
    Table {
        /// The push side's form, then the pull side's.
        forms: [&'a BusForm<E>; 2],
        /// The sides' weights.
        powers: FormPowers<E>,
    },
    /// A producer's share of the push side.
    Producer {
        /// Per bit, its block's selector, the push side's weight folded in.
        coefficients: Vec<E>,
        /// The producer the term is for.
        producer: &'a Producer,
        /// The fingerprint's weights.
        weights: &'a [E],
        /// The fingerprint's offset.
        beta: E,
    },
}

/// The batch the verifiers check: one air per table in schema order, then one per lookup producer.
///
/// It is the prover's batch, its terms kept as the bus left them.
pub(crate) struct VerifierBatch<'a, E>(Vec<Air<OwedTerm<'a, E>>>);

impl<'a, E: Copy> VerifierBatch<'a, E> {
    /// The batch settling what the bus left, its sides weighed by `powers`.
    pub(crate) fn new<A: Arith<E = E>>(
        a: &mut A,
        layout: &'a Layout,
        bus: &'a BusVerify<E>,
        powers: FormPowers<E>,
    ) -> Self {
        let tables = (tables::ClassTable::all().iter().zip(&layout.taus).enumerate()).map(|(t, (table, &tau))| Air {
            tau,
            n_cols: table.n_committed_columns(),
            n_public: 0,
            summand: OwedTerm::Table {
                forms: [&bus.forms[0][t], &bus.forms[1][t]],
                powers,
            },
        });
        let mut airs: Vec<_> = tables.collect();
        for (p, coefficients) in layout.producers.iter().zip(&bus.producers) {
            airs.push(Air {
                tau: p.kappa,
                n_cols: 2 * p.bits,
                n_public: p.bits,
                summand: OwedTerm::Producer {
                    coefficients: coefficients.iter().map(|&c| a.mul(c, powers.push())).collect(),
                    producer: p,
                    weights: &bus.weights,
                    beta: bus.beta,
                },
            });
        }
        Self(airs)
    }

    /// The batch's airs, as the table sumcheck takes them.
    pub(crate) fn airs(&self) -> &[Air<OwedTerm<'a, E>>] {
        &self.0
    }
}

impl<A: Arith> Residual<A> for OwedTerm<'_, A::E> {
    fn value_at(&self, a: &mut A, cols: &[A::E]) -> A::E {
        match self {
            Self::Table { forms, powers } => {
                let push = forms[0].at(a, cols);
                let pull = forms[1].at(a, cols);
                powers.combine(a, [push, pull])
            }
            // `sum_i c_i * (1 + b_i * P'_i)`.
            Self::Producer { coefficients, .. } => {
                let n = coefficients.len();
                let zero = a.zero();
                (0..n).fold(zero, |acc, i| {
                    let one = a.one();
                    let leaf = a.mul_add(cols[i], cols[n + i], one);
                    a.mul_add(coefficients[i], leaf, acc)
                })
            }
        }
    }

    fn public_at(&self, a: &mut A, chi: &[A::E]) -> Vec<A::E> {
        match self {
            Self::Table { .. } => Vec::new(),
            Self::Producer {
                producer,
                weights,
                beta,
                ..
            } => leaf::producer_affine_evals(a, producer, weights, *beta, chi),
        }
    }
}
