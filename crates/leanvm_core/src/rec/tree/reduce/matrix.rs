//! The matrix reduction: claims `u^T (a A + b B) w = v` on the flock circuits' matrices to `A` and `B` at one row and one column point.
//!
//! The claims are batched by the powers of one challenge `theta`, every circuit sharing every challenge.
//!
//! - The row phase is a sumcheck over `sum_x sum_c theta^c u_c(x) g_c(x)`, with `g_c = (a_c A + b_c B) w_c`, to a row point `r`.
//! - The column phase is a sumcheck over `sum_y A(r, y) Theta_A(y) + B(r, y) Theta_B(y)`, with `Theta_A = sum_c theta^c u_c(r) a_c w_c`, to a column point `s`.
//!
//! A circuit of fewer variables waits on the rest in each phase, as the dense reduction's smaller polynomials do.

use super::{FoldTable, ReduceError, products};
use crate::class_flock::{FlockId, N_FLOCKS};
use crate::rec::tree::claims::{Coefficient, ColWeight, MatrixClaim, RowWeight};
use crate::rec::verifier::SkipDomain;
use fiat_shamir::arith::{Arith, Verifier};
use fiat_shamir::transcript::{Challenger, ProverState, Transmitter};
use flock::lincheck::{LincheckCircuit, build_quirky_eq_table};
use flock::zerocheck::K_SKIP;
use primitives::field::F192;
use primitives::multilinear::eq_table;

/// What the matrix reduction leaves: the row and column points, and each circuit's `A` and `B` at its prefixes of them.
pub(crate) struct MatrixReduced<E> {
    /// The row point.
    pub(crate) rows: Vec<E>,
    /// The column point.
    pub(crate) cols: Vec<E>,
    /// Each circuit's `A` and `B` at its prefixes of the points.
    pub(crate) values: Vec<[E; 2]>,
}

/// The matrix reduction's prover, in its row phase: per claim, its row weight and `g_c`.
pub(crate) struct MatrixProver {
    /// Each claim's tables.
    claims: Vec<RowTables>,
}

/// The matrix reduction's prover, in its column phase: per circuit, `A(r, .)`, `Theta_A`, `B(r, .)` and `Theta_B`.
pub(crate) struct ColumnPhase {
    /// Each circuit's four tables.
    circuits: Vec<[FoldTable; 4]>,
}

/// One claim's tables in the row phase.
struct RowTables {
    /// Its circuit's variables.
    k: usize,
    /// Its row weight, scaled by its power of `theta`.
    u: FoldTable,
    /// `g_c = (a A + b B) w`.
    g: FoldTable,
}

/// `prod_{i >= k} x_i`: what a circuit of `k` variables waits on.
fn waiting<A: Arith>(a: &mut A, x: &[A::E], k: usize) -> A::E {
    let one = a.one();
    x[k..].iter().fold(one, |acc, &x| a.mul(acc, x))
}

/// The value cached under `key`, or `value()` cached under it.
///
/// Claims at one point share their weights' factors: natively their elements are equal, in rows they are the same wires.
fn shared<K: PartialEq, E: Copy>(cache: &mut Vec<(K, E)>, key: K, value: impl FnOnce() -> E) -> E {
    if let Some(&(_, v)) = cache.iter().find(|(k, _)| *k == key) {
        return v;
    }
    let v = value();
    cache.push((key, v));
    v
}

impl<E: Copy + PartialEq> MatrixReduced<E> {
    /// Verify the reduction of the claims.
    ///
    /// # Errors
    ///
    /// Returns a malformed stream, or the final identity's failure.
    pub(crate) fn verify<V: Verifier<E = E>>(v: &mut V, claims: &[MatrixClaim<E>]) -> Result<Self, ReduceError> {
        let theta = v.sample();
        let powers = v.powers(theta, claims.len());
        let zero = v.zero();
        let mut claim = (claims.iter().zip(&powers)).fold(zero, |acc, (c, &p)| v.mul_add(p, c.value, acc));
        let phase = |v: &mut V, claim: &mut E| -> Result<Vec<E>, ReduceError> {
            (0..FlockId::MAX_K_LOG)
                .map(|_| {
                    let h = v.next_round_poly(3, *claim, None)?;
                    let x = v.sample();
                    *claim = v.poly_eval(&h, x);
                    Ok(x)
                })
                .collect()
        };
        let rows = phase(v, &mut claim)?;
        let cols = phase(v, &mut claim)?;
        let values = (0..N_FLOCKS)
            .map(|_| Ok([v.next_scalar()?, v.next_scalar()?]))
            .collect::<Result<Vec<_>, ReduceError>>()?;
        let weights = Self::final_weights(v, claims, &powers, &rows, &cols);
        let total = (values.iter().zip(&weights)).fold(zero, |acc, ([a, b], [wa, wb])| {
            let acc = v.mul_add(*a, *wa, acc);
            v.mul_add(*b, *wb, acc)
        });
        v.ensure_eq(claim, total, || ReduceError::Matrix)?;
        Ok(Self { rows, cols, values })
    }

    /// Each circuit's weights on `A` and `B` in the final identity: `sum_c theta^c u_c(r) w_c(s) (a_c, b_c)`, times what it waits on.
    ///
    /// A row weight is evaluated once for all its claims, as are its skip factor and a column weight's eq factor.
    pub(crate) fn final_weights<A: Arith<E = E>>(
        a: &mut A,
        claims: &[MatrixClaim<E>],
        powers: &[E],
        rows: &[E],
        cols: &[E],
    ) -> Vec<[E; 2]> {
        let skip_r = a.eq_table(&rows[..K_SKIP]);
        let skip_s = a.eq_table(&cols[..K_SKIP]);
        let zero = a.zero();
        let mut weights = vec![[zero; 2]; N_FLOCKS];
        let (mut row_values, mut skips, mut col_eqs) = (Vec::new(), Vec::new(), Vec::new());
        for (c, &power) in claims.iter().zip(powers) {
            let k = c.circuit.k_log();
            let u = shared(&mut row_values, &c.row, || c.row.at(a, &rows[..k], &skip_r, &mut skips));
            let w = c.col.at(a, &cols[..k], &skip_s, &mut col_eqs);
            let uw = a.mul(u, w);
            let g = a.mul(power, uw);
            let [wa, wb] = &mut weights[c.circuit.index()];
            *wa = c.coefficients[0].times(a, g, *wa);
            *wb = c.coefficients[1].times(a, g, *wb);
        }
        let mut lifts = Vec::new();
        for (f, pair) in FlockId::ALL.into_iter().zip(&mut weights) {
            let k = f.k_log();
            let lift = shared(&mut lifts, k, || {
                let lift_r = waiting(a, rows, k);
                let lift_s = waiting(a, cols, k);
                a.mul(lift_r, lift_s)
            });
            *pair = pair.map(|w| a.mul(w, lift));
        }
        weights
    }
}

impl<E: Copy + PartialEq> RowWeight<E> {
    /// The weight's multilinear extension at `r`, given the eq table of its skip variables and the skip factors so far.
    fn at<A: Arith<E = E>>(&self, a: &mut A, r: &[E], skip: &[E], skips: &mut Vec<(E, E)>) -> E {
        match self {
            Self::Skip { z, rest } => {
                let low = shared(skips, *z, || {
                    let vanishing = SkipDomain::vanishing(a, *z);
                    SkipDomain::lagrange_at(a, *z, vanishing, skip)
                });
                let high = a.eq_eval(rest, &r[K_SKIP..]);
                a.mul(low, high)
            }
            Self::Point(p) => a.eq_eval(p, r),
        }
    }
}

impl<E: Copy + PartialEq> ColWeight<E> {
    /// The weight's multilinear extension at `s`, given the eq table of its skip variables and the eq factors so far.
    ///
    /// An eq factor is keyed by its point and by whether it starts past the skip variables.
    fn at<'c, A: Arith<E = E>>(&'c self, a: &mut A, s: &[E], skip: &[E], eqs: &mut Vec<((bool, &'c [E]), E)>) -> E {
        match self {
            Self::Slices { slices, rest } => {
                let zero = a.zero();
                let low = (slices.iter().zip(skip)).fold(zero, |acc, (&x, &e)| a.mul_add(x, e, acc));
                let high = shared(eqs, (true, rest.as_slice()), || a.eq_eval(rest, &s[K_SKIP..]));
                a.mul(low, high)
            }
            Self::Point(p) => shared(eqs, (false, p.as_slice()), || a.eq_eval(p, s)),
        }
    }
}

impl<E: Copy> Coefficient<E> {
    /// `acc + coefficient x`.
    fn times<A: Arith<E = E>>(self, a: &mut A, x: E, acc: E) -> E {
        match self {
            Self::Zero => acc,
            Self::One => a.add(x, acc),
            Self::Of(c) => a.mul_add(c, x, acc),
        }
    }
}

impl Coefficient<F192> {
    const fn value(self) -> F192 {
        match self {
            Self::Zero => F192::ZERO,
            Self::One => F192::ONE,
            Self::Of(c) => c,
        }
    }
}

impl RowWeight<F192> {
    fn table(&self) -> Vec<F192> {
        match self {
            Self::Skip { z, rest } => build_quirky_eq_table(*z, rest, K_SKIP),
            Self::Point(p) => eq_table(p),
        }
    }
}

impl ColWeight<F192> {
    /// The weight's table: the slices vary fastest.
    fn table(&self) -> Vec<F192> {
        match self {
            Self::Slices { slices, rest } => (eq_table(rest).into_iter())
                .flat_map(|h| slices.iter().map(move |&x| x * h))
                .collect(),
            Self::Point(p) => eq_table(p),
        }
    }
}

impl MatrixProver {
    /// Prove the reduction of the claims, which must be true of the circuits' matrices.
    pub(crate) fn prove(ps: &mut ProverState, claims: &[MatrixClaim<F192>]) {
        let theta = ps.sample();
        let mut rows = Self::new(claims, theta);
        let r: Vec<F192> = (0..FlockId::MAX_K_LOG)
            .map(|i| {
                ps.add_scalars(&rows.round(i));
                let x = ps.sample();
                rows.bind(i, x);
                x
            })
            .collect();
        let mut cols = rows.columns(claims, &r);
        for i in 0..FlockId::MAX_K_LOG {
            ps.add_scalars(&cols.round(i));
            let x = ps.sample();
            cols.bind(i, x);
        }
        ps.add_scalars(&cols.finals());
    }

    /// The row phase of the claims under the batching challenge `theta`: each claim's tables, one walk of its circuit each.
    pub(crate) fn new(claims: &[MatrixClaim<F192>], theta: F192) -> Self {
        let powers: Vec<F192> = std::iter::successors(Some(F192::ONE), |&p| Some(p * theta))
            .take(claims.len())
            .collect();
        let claims = parallel::map_collect(claims.len(), |i| {
            let c = &claims[i];
            let u: Vec<F192> = c.row.table().into_iter().map(|x| powers[i] * x).collect();
            let (ra, rb) = c.circuit.circuit().row_values(&c.col.table());
            let [a, b] = c.coefficients.map(Coefficient::value);
            let g = ra.iter().zip(&rb).map(|(&x, &y)| a * x + b * y).collect();
            RowTables {
                k: c.circuit.k_log(),
                u: FoldTable::new(u),
                g: FoldTable::new(g),
            }
        });
        Self { claims }
    }

    /// Row round `i`'s message: `h(0)` and the leading coefficient.
    pub(crate) fn round(&self, i: usize) -> [F192; 2] {
        let add = |[a, b]: [F192; 2], [c, d]: [F192; 2]| [a + c, b + d];
        parallel::map_reduce(
            self.claims.len(),
            || [F192::ZERO; 2],
            |c| {
                let t = &self.claims[c];
                if t.k > i {
                    products(&t.u.values, &t.g.values)
                } else {
                    [F192::ZERO; 2]
                }
            },
            add,
        )
    }

    /// Bind row round `i`'s variable to `x`.
    pub(crate) fn bind(&mut self, i: usize, x: F192) {
        parallel::for_each_mut(&mut self.claims, |_, t| {
            if t.k > i {
                t.u.fold(x, false);
                t.g.fold(x, false);
            }
        });
    }

    /// The column phase at the row point `r`: per circuit, two backward walks for `A(r, .)` and `B(r, .)`, and the claims' column weights.
    pub(crate) fn columns(&self, claims: &[MatrixClaim<F192>], r: &[F192]) -> ColumnPhase {
        let circuits = parallel::map_collect(N_FLOCKS, |f| {
            let f = FlockId::ALL[f];
            let k = f.k_log();
            let circuit = f.circuit();
            let eq = eq_table(&r[..k]);
            let at = circuit.fold_alpha_batched(F192::ZERO, &eq);
            let both = circuit.fold_alpha_batched(F192::ONE, &eq);
            let bt: Vec<F192> = at.iter().zip(&both).map(|(&x, &y)| x + y).collect();
            let lambda = r[k..].iter().fold(F192::ONE, |acc, &x| acc * x);
            let (mut wa, mut wb) = (vec![F192::ZERO; 1 << k], vec![F192::ZERO; 1 << k]);
            for (c, t) in claims.iter().zip(&self.claims).filter(|(c, _)| c.circuit == f) {
                let [a, b] = c.coefficients.map(Coefficient::value);
                let scale = lambda * t.u.values[0];
                let (sa, sb) = (scale * a, scale * b);
                for ((x, y), w) in wa.iter_mut().zip(wb.iter_mut()).zip(c.col.table()) {
                    *x += sa * w;
                    *y += sb * w;
                }
            }
            [at, wa, bt, wb].map(FoldTable::new)
        });
        ColumnPhase { circuits }
    }
}

impl ColumnPhase {
    /// Column round `i`'s message.
    pub(crate) fn round(&self, i: usize) -> [F192; 2] {
        let add = |[a, b]: [F192; 2], [c, d]: [F192; 2]| [a + c, b + d];
        parallel::map_reduce(
            self.circuits.len(),
            || [F192::ZERO; 2],
            |f| {
                if FlockId::ALL[f].k_log() <= i {
                    return [F192::ZERO; 2];
                }
                let [at, wa, bt, wb] = &self.circuits[f];
                add(products(&wa.values, &at.values), products(&wb.values, &bt.values))
            },
            add,
        )
    }

    /// Bind column round `i`'s variable to `x`.
    pub(crate) fn bind(&mut self, i: usize, x: F192) {
        parallel::for_each_mut(&mut self.circuits, |f, tables| {
            if FlockId::ALL[f].k_log() > i {
                tables.iter_mut().for_each(|t| t.fold(x, false));
            }
        });
    }

    /// Each circuit's `A` and `B` at its prefixes of the points, flattened.
    pub(crate) fn finals(&self) -> Vec<F192> {
        (self.circuits.iter())
            .flat_map(|[at, _, bt, _]| [at.values[0], bt.values[0]])
            .collect()
    }
}
