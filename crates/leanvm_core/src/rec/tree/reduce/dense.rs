//! The dense reduction: claims on the dense polynomials to one evaluation of each, at prefixes of one point.
//!
//! The claims' terms are batched by the powers of one challenge `theta`, then one degree-two sumcheck runs over
//!
//! ```text
//! sum_j sum_x Xi_j(x) P_j(x),    Xi_j = sum_{t on P_j} theta^t scale_t eq(p_t, .)
//! ```
//!
//! lowest variable first.
//! A polynomial of fewer variables is bound early, and its share then waits on the rest: each later round multiplies it by its challenge.

use super::{DenseTables, FoldTable, PAR_LEN, ReduceError, products_par, table_of};
use crate::arith::{Arith, Verifier};
use crate::rec::tree::claims::{DenseClaim, DensePoly, DenseTerm};
use fiat_shamir::transcript::{Challenger, ProverState, Transmitter};
use primitives::field::{F64, F192};
use primitives::multilinear::eq_table;
use std::collections::BTreeMap;

/// Each dense polynomial's variables: the bytecode table's, the image's, the fixed polynomial's.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct DenseVars(pub(crate) [usize; DensePoly::COUNT]);

/// What the dense reduction leaves: one point, and each reduced polynomial's value at its prefix.
///
/// A polynomial no claim weighs is not reduced and has no value.
pub(crate) struct DenseReduced<E> {
    /// The point, one coordinate per round.
    pub(crate) point: Vec<E>,
    /// Each polynomial's value at its prefix of the point, if reduced.
    pub(crate) values: [Option<E>; DensePoly::COUNT],
}

/// The dense reduction's prover: each reduced polynomial and its weight table, both folded as the challenges come.
pub(crate) struct DenseProver<'a> {
    /// The reduced polynomials, in order.
    parts: Vec<Part<'a>>,
}

/// One reduced polynomial in the prover: its variables, its table, and its weight table `Xi_j`.
struct Part<'a> {
    /// The polynomial's variables.
    n_vars: usize,
    /// Its values, folded.
    table: Table<'a>,
    /// Its weight table, folded.
    weights: FoldTable,
}

/// A polynomial's table: its values in `K` until the first round binds a variable.
enum Table<'a> {
    /// The polynomial as given.
    Base(&'a [F64]),
    /// The polynomial folded by at least one round.
    Ext(FoldTable),
}

/// One term of a weight table: `c eq(p, .)` on one aligned block of the table.
struct Placed {
    /// The term's coefficient.
    coef: F192,
    /// The point's coordinates before its trailing Boolean ones.
    point: Vec<F192>,
    /// The block's offset in the table, which the trailing Boolean coordinates name.
    offset: usize,
}

impl DenseVars {
    /// The polynomials some claim weighs, which the reduction reduces.
    fn reduced<E>(claims: &[DenseClaim<E>]) -> [bool; DensePoly::COUNT] {
        DensePoly::ALL.map(|p| claims.iter().any(|c| c.poly == p))
    }

    /// The rounds: the most variables a reduced polynomial has.
    fn rounds(&self, reduced: [bool; DensePoly::COUNT]) -> usize {
        (self.0.iter().zip(reduced))
            .filter_map(|(&n, r)| r.then_some(n))
            .max()
            .unwrap_or(0)
    }

    /// Verify the reduction of the claims.
    ///
    /// # Errors
    ///
    /// Returns a malformed stream, or the final identity's failure.
    pub(crate) fn verify<V: Verifier>(
        &self,
        v: &mut V,
        claims: &[DenseClaim<V::E>],
    ) -> Result<DenseReduced<V::E>, ReduceError> {
        let reduced = Self::reduced(claims);
        let theta = v.sample();
        let n_terms = claims.iter().map(|c| c.terms.len()).sum();
        let powers = v.powers(theta, n_terms);
        let zero = v.zero();
        let terms = claims.iter().flat_map(|c| &c.terms);
        let mut claim = (terms.zip(&powers)).fold(zero, |acc, (t, &power)| {
            let value = t.scale.map_or(t.value, |s| v.mul(s, t.value));
            v.mul_add(power, value, acc)
        });

        let rounds = self.rounds(reduced);
        let mut point = Vec::with_capacity(rounds);
        for _ in 0..rounds {
            let h = v.next_round_poly(3, claim, None)?;
            let r = v.sample();
            claim = v.poly_eval(&h, r);
            point.push(r);
        }
        let mut values = [None; DensePoly::COUNT];
        for (value, reduced) in values.iter_mut().zip(reduced) {
            if reduced {
                *value = Some(v.next_scalar()?);
            }
        }
        let weights = self.final_weights(v, claims, &powers, &point);
        let total = (values.iter().zip(weights)).fold(zero, |acc, (value, weight)| match (value, weight) {
            (Some(value), Some(weight)) => v.mul_add(*value, weight, acc),
            _ => acc,
        });
        v.ensure_eq(claim, total, || ReduceError::Dense)?;
        Ok(DenseReduced { point, values })
    }

    /// Each reduced polynomial's weight in the final identity: `Xi_j` at its prefix of `point`, times the later challenges.
    pub(crate) fn final_weights<A: Arith>(
        &self,
        a: &mut A,
        claims: &[DenseClaim<A::E>],
        powers: &[A::E],
        point: &[A::E],
    ) -> [Option<A::E>; DensePoly::COUNT] {
        let mut weights = [None; DensePoly::COUNT];
        let mut powers = powers.iter().copied();
        for claim in claims {
            let n = self.0[claim.poly as usize];
            let xi = claim.weight_at(a, &mut powers, &point[..n]);
            let slot = &mut weights[claim.poly as usize];
            *slot = Some(slot.map_or(xi, |w| a.add(w, xi)));
        }
        for (weight, &n) in weights.iter_mut().zip(&self.0) {
            if let Some(w) = weight {
                *w = point[n.min(point.len())..].iter().fold(*w, |acc, &x| a.mul(acc, x));
            }
        }
        weights
    }
}

impl<E: Copy> DenseClaim<E> {
    /// `sum_t power_t scale_t eq(p_t, r)`, the powers taken in order, the terms sharing their low point's prefix.
    fn weight_at<A: Arith<E = E>>(&self, a: &mut A, powers: &mut impl Iterator<Item = E>, r: &[E]) -> E {
        let longest = self.terms.iter().map(|t| t.n_low).max().unwrap_or(0);
        let one = a.one();
        let mut prefix = Vec::with_capacity(longest + 1);
        prefix.push(one);
        for (j, (&p, &x)) in self.low.iter().zip(r).take(longest).enumerate() {
            let s = a.add(p, x);
            let next = a.times_one_plus(prefix[j], s);
            prefix.push(next);
        }
        let zero = a.zero();
        self.terms.iter().fold(zero, |acc, t| {
            let DenseTerm {
                n_low,
                bits,
                top,
                scale,
                ..
            } = *t;
            let at_bits = n_low + bits.len;
            assert_eq!(
                at_bits + usize::from(top.is_some()),
                r.len(),
                "a term's point has its polynomial's variables"
            );
            let bits_eq = a.eq_bits(bits.value, &r[n_low..at_bits]);
            let mut eq = a.mul(prefix[n_low], bits_eq);
            if let Some(top) = top {
                let s = a.add(top, r[at_bits]);
                eq = a.times_one_plus(eq, s);
            }
            let power = powers.next().expect("a power per term");
            let weight = scale.map_or(power, |s| a.mul(power, s));
            a.mul_add(weight, eq, acc)
        })
    }
}

impl DenseTerm<F192> {
    /// The term at its coefficient, placed in its polynomial's table: its point's trailing Boolean coordinates name a block.
    fn placed(&self, low: &[F192], coef: F192) -> Placed {
        let mut point = low[..self.n_low].to_vec();
        point.extend((0..self.bits.len).map(|i| F192::new((self.bits.value >> i & 1) as u64, 0, 0)));
        point.extend(self.top);
        let boolean = |x: &F192| *x == F192::ZERO || *x == F192::ONE;
        let k = point.len() - point.iter().rev().take_while(|x| boolean(x)).count();
        let offset = (point[k..].iter().enumerate())
            .map(|(i, &x)| usize::from(x == F192::ONE) << (k + i))
            .sum();
        point.truncate(k);
        Placed { coef, point, offset }
    }
}

impl<'a> DenseProver<'a> {
    /// Prove the reduction of the claims, which must be true of the tables.
    pub(crate) fn prove(ps: &mut ProverState, vars: &DenseVars, tables: &'a DenseTables, claims: &[DenseClaim<F192>]) {
        let theta = ps.sample();
        let mut prover = Self::new(vars, tables, claims, theta);
        for i in 0..prover.rounds() {
            ps.add_scalars(&prover.round(i));
            let r = ps.sample();
            prover.bind(i, r);
        }
        ps.add_scalars(&prover.finals());
    }

    /// The prover of the claims under the batching challenge `theta`.
    pub(crate) fn new(vars: &DenseVars, tables: &'a DenseTables, claims: &[DenseClaim<F192>], theta: F192) -> Self {
        let reduced = DenseVars::reduced(claims);
        let mut placed: Vec<Vec<Placed>> = DensePoly::ALL.map(|_| Vec::new()).into();
        let mut power = F192::ONE;
        for claim in claims {
            for term in &claim.terms {
                let coef = term.scale.map_or(power, |s| power * s);
                if !coef.is_zero() {
                    placed[claim.poly as usize].push(term.placed(&claim.low, coef));
                }
                power *= theta;
            }
        }
        let parts = (DensePoly::ALL.into_iter().zip(placed))
            .filter(|&(p, _)| reduced[p as usize])
            .map(|(p, terms)| {
                let n_vars = vars.0[p as usize];
                let table = &tables.0[p as usize];
                assert_eq!(table.len(), 1 << n_vars, "a dense table has its variables");
                Part {
                    n_vars,
                    table: Table::Base(table),
                    weights: FoldTable::new(weight_table(n_vars, &terms)),
                }
            })
            .collect();
        Self { parts }
    }

    /// The number of rounds.
    pub(crate) fn rounds(&self) -> usize {
        self.parts.iter().map(|p| p.n_vars).max().unwrap_or(0)
    }

    /// Round `i`'s message: `h(0)` and the leading coefficient, the claim fixing the linear one.
    ///
    /// A polynomial bound already contributes a linear term only, which the claim accounts for.
    pub(crate) fn round(&self, i: usize) -> [F192; 2] {
        (self.parts.iter().filter(|p| p.n_vars > i)).fold([F192::ZERO; 2], |[c0, c2], p| {
            let w = &p.weights.values;
            let [a, b] = match &p.table {
                Table::Base(t) => products_par(w, t, F192::mul_base),
                Table::Ext(t) => products_par(w, &t.values, |x, y| x * y),
            };
            [c0 + a, c2 + b]
        })
    }

    /// Bind round `i`'s variable to `r`.
    pub(crate) fn bind(&mut self, i: usize, r: F192) {
        for p in self.parts.iter_mut().filter(|p| p.n_vars > i) {
            p.weights.fold(r, true);
            match &mut p.table {
                Table::Base(t) => {
                    let t = *t;
                    let folded = table_of(t.len() / 2, |k| {
                        r.mul_base(t[2 * k] + t[2 * k + 1]) + F192::from(t[2 * k])
                    });
                    p.table = Table::Ext(FoldTable::new(folded));
                }
                Table::Ext(t) => t.fold(r, true),
            }
        }
    }

    /// Each reduced polynomial's value at its prefix of the point.
    pub(crate) fn finals(&self) -> Vec<F192> {
        (self.parts.iter())
            .map(|p| match &p.table {
                Table::Base(t) => F192::from(t[0]),
                Table::Ext(t) => t.values[0],
            })
            .collect()
    }
}

/// `Xi(x) = sum_t coef_t eq(p_t, x)` over `2^n` entries, each block's terms added in one pass.
fn weight_table(n: usize, terms: &[Placed]) -> Vec<F192> {
    let mut table = table_of(1 << n, |_| F192::ZERO);
    let mut blocks: BTreeMap<(usize, usize), Vec<&Placed>> = BTreeMap::new();
    for t in terms {
        blocks.entry((t.offset, t.point.len())).or_default().push(t);
    }
    for block in blocks.values() {
        add_eqs(&mut table, block);
    }
    table
}

/// The variables of the low eq tables a weight table's pass keeps in L1.
const LOW_VARS: usize = 10;

/// `table[offset + x] += sum_t coef_t eq(p_t, x)` for terms of one block.
///
/// Each term's eq table is the tensor of a low one and a high one, the coefficient in the high one.
fn add_eqs(table: &mut [F192], terms: &[&Placed]) {
    let k = terms[0].point.len();
    let l = k.min(LOW_VARS);
    let lows: Vec<Vec<F192>> = terms.iter().map(|t| eq_table(&t.point[..l])).collect();
    let highs: Vec<Vec<F192>> = (terms.iter())
        .map(|t| eq_table(&t.point[l..]).into_iter().map(|e| e * t.coef).collect())
        .collect();
    let row = |h: usize, dst: &mut [F192]| {
        for (low, high) in lows.iter().zip(&highs) {
            for (slot, &e) in dst.iter_mut().zip(low) {
                *slot += high[h] * e;
            }
        }
    };
    let offset = terms[0].offset;
    let dst = &mut table[offset..offset + (1 << k)];
    if dst.len() < PAR_LEN {
        dst.chunks_mut(1 << l).enumerate().for_each(|(h, d)| row(h, d));
    } else {
        parallel::chunks_mut(dst, 1 << l, row);
    }
}
