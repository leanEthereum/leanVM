//! The matrix reduction: claims `u^T (a A + b B) w = v` on the flock circuits' matrices to `A` and `B` at one row and one column point.
//!
//! The claims are batched by the powers of one challenge `theta`, every circuit sharing every challenge.
//!
//! - The row phase is a sumcheck over `sum_x sum_c theta^c u_c(x) g_c(x)`, with `g_c = (a_c A + b_c B) w_c`, to a row point `r`.
//! - The column phase is a sumcheck over `sum_y A(r, y) Theta_A(y) + B(r, y) Theta_B(y)`, with `Theta_A = sum_c theta^c u_c(r) a_c w_c`, to a column point `s`.
//!
//! A circuit of fewer variables waits on the rest in each phase, as the dense reduction's smaller polynomials do.

use super::{FoldPair, Msg, ReduceError};
use crate::cpu::Claim;
use crate::tables::{CircuitId, N_CIRCUITS};
use fiat_shamir::ProverState;
use fiat_shamir::arith::{Arith, Verifier};
use flock::lincheck::LincheckCircuit;
use flock::lincheck::MatrixForm;
use flock::zerocheck::{K_SKIP, SkipDomain};
use primitives::field::F192;
use primitives::multilinear::eq_table;

/// A matrix's coefficient in a matrix claim.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Coefficient<E> {
    /// The matrix is not in the claim.
    Zero,
    /// The matrix itself.
    One,
    /// The matrix scaled by this element.
    Of(E),
}

/// A matrix claim's row weight `u`: flock's skip weight at a zerocheck point, or `eq(p, .)`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum RowWeight<E> {
    /// Lagrange weights at `z` over the skip domain, then an eq weight over the other variables.
    Skip { z: E, rest: Vec<E> },
    /// The eq weight at a point.
    Point(Vec<E>),
}

/// A matrix claim's column weight `w`: the lincheck's slices, then an eq weight, or `eq(p, .)`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum ColWeight<E> {
    /// The slices on the low variables, then an eq weight over the other variables.
    Slices { slices: Vec<E>, rest: Vec<E> },
    /// The eq weight at a point.
    Point(Vec<E>),
}

/// `u^T (a A + b B) w = v` on a flock circuit's matrices: `u` and `w` its weights, `a` and `b` its coefficients.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct MatrixClaim<E> {
    /// The flock circuit.
    pub(crate) circuit: CircuitId,
    /// The row weight `u`.
    pub(crate) row: RowWeight<E>,
    /// The column weight `w`.
    pub(crate) col: ColWeight<E>,
    /// The coefficients `a` and `b`.
    pub(crate) coefficients: [Coefficient<E>; 2],
    /// The claimed value.
    pub(crate) value: E,
}

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
    /// The next round's message.
    message: [F192; 2],
}

/// The matrix reduction's prover, in its column phase: per circuit, `A(r, .)`, `Theta_A`, `B(r, .)` and `Theta_B`.
pub(crate) struct ColumnPhase {
    /// Each circuit's pairs: `Theta_A` weighing `A(r, .)`, then `Theta_B` weighing `B(r, .)`.
    circuits: Vec<[FoldPair; 2]>,
    /// The next round's message.
    message: [F192; 2],
}

/// One claim's tables in the row phase.
struct RowTables {
    /// Its circuit's variables.
    k: usize,
    /// Its row weight, scaled by its power of `theta`, weighing `g_c = (a A + b B) w`.
    pair: FoldPair,
}

impl<E: Copy> Coefficient<E> {
    /// The same coefficient, its element mapped by `f`.
    fn map<T>(self, f: &mut impl FnMut(E) -> T) -> Coefficient<T> {
        match self {
            Self::Zero => Coefficient::Zero,
            Self::One => Coefficient::One,
            Self::Of(x) => Coefficient::Of(f(x)),
        }
    }
}

impl<E: Copy> RowWeight<E> {
    /// The same weight, each element mapped by `f`.
    fn map<T>(&self, f: &mut impl FnMut(E) -> T) -> RowWeight<T> {
        match self {
            Self::Skip { z, rest } => RowWeight::Skip {
                z: f(*z),
                rest: rest.iter().map(|&x| f(x)).collect(),
            },
            Self::Point(p) => RowWeight::Point(p.iter().map(|&x| f(x)).collect()),
        }
    }
}

impl<E: Copy> ColWeight<E> {
    /// The same weight, each element mapped by `f`.
    fn map<T>(&self, f: &mut impl FnMut(E) -> T) -> ColWeight<T> {
        match self {
            Self::Slices { slices, rest } => ColWeight::Slices {
                slices: slices.iter().map(|&x| f(x)).collect(),
                rest: rest.iter().map(|&x| f(x)).collect(),
            },
            Self::Point(p) => ColWeight::Point(p.iter().map(|&x| f(x)).collect()),
        }
    }
}

impl<E: Copy> MatrixClaim<E> {
    /// The claim a lincheck leaves: `u^T (A + alpha B) w`, at the zerocheck's skip point and the lincheck's sliced point.
    pub(crate) fn fresh(circuit: CircuitId, claim: &Claim<MatrixForm<E>, E>) -> Self {
        let form = &claim.point;
        Self {
            circuit,
            row: RowWeight::Skip {
                z: form.z_skip,
                rest: form.x_inner_rest.clone(),
            },
            col: ColWeight::Slices {
                slices: form.s_hat_v.clone(),
                rest: form.r_inner_rest.clone(),
            },
            coefficients: [Coefficient::One, Coefficient::Of(form.alpha)],
            value: claim.value,
        }
    }

    /// A child's claims on both matrices of a circuit of `k` variables, at its prefixes of the child's points.
    pub(crate) fn carried(circuit: CircuitId, k: usize, rows: &[E], cols: &[E], values: [E; 2]) -> [Self; 2] {
        let claim = |coefficients, value| Self {
            circuit,
            row: RowWeight::Point(rows[..k].to_vec()),
            col: ColWeight::Point(cols[..k].to_vec()),
            coefficients,
            value,
        };
        [
            claim([Coefficient::One, Coefficient::Zero], values[0]),
            claim([Coefficient::Zero, Coefficient::One], values[1]),
        ]
    }

    /// The same claim, each element mapped by `f`.
    pub(super) fn map<T>(&self, f: &mut impl FnMut(E) -> T) -> MatrixClaim<T> {
        MatrixClaim {
            circuit: self.circuit,
            row: self.row.map(f),
            col: self.col.map(f),
            coefficients: self.coefficients.map(|c| c.map(f)),
            value: f(self.value),
        }
    }
}

/// Values computed once per key, for the claims that share them.
///
/// Claims at one point share their weights' factors: natively their elements are equal, in rows they are the same wires.
struct Cache<K, E>(Vec<(K, E)>);

impl<K: PartialEq, E: Copy> Cache<K, E> {
    /// An empty cache.
    const fn new() -> Self {
        Self(Vec::new())
    }

    /// The value cached under `key`, or `value()` cached under it.
    fn get_or_insert_with(&mut self, key: K, value: impl FnOnce() -> E) -> E {
        if let Some(&(_, v)) = self.0.iter().find(|(k, _)| *k == key) {
            return v;
        }
        let v = value();
        self.0.push((key, v));
        v
    }
}

impl<E: Copy + PartialEq> MatrixReduced<E> {
    /// Verify the reduction of the claims.
    ///
    /// # Errors
    ///
    /// Returns a malformed stream, or the final identity's failure.
    pub(crate) fn verify<V: Verifier<E = E>>(v: &mut V, claims: &[MatrixClaim<E>]) -> Result<Self, ReduceError> {
        let theta = v.verifier_message();
        let powers = v.powers(theta, claims.len());
        let zero = v.zero();
        let mut claim = (claims.iter().zip(&powers)).fold(zero, |acc, (c, &p)| v.mul_add(p, c.value, acc));
        let phase = |v: &mut V, claim: &mut E| -> Result<Vec<E>, ReduceError> {
            (0..CircuitId::MAX_K_LOG)
                .map(|_| {
                    let h = v.read_round(3, *claim, None)?;
                    let x = v.verifier_message();
                    *claim = v.poly_eval(&h, x);
                    Ok(x)
                })
                .collect()
        };
        let rows = phase(v, &mut claim)?;
        let cols = phase(v, &mut claim)?;
        let values = (0..N_CIRCUITS)
            .map(|_| Ok([v.prover_message()?, v.prover_message()?]))
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
    pub(super) fn final_weights<A: Arith<E = E>>(
        a: &mut A,
        claims: &[MatrixClaim<E>],
        powers: &[E],
        rows: &[E],
        cols: &[E],
    ) -> Vec<[E; 2]> {
        let skip_r = a.eq_table(&rows[..K_SKIP]);
        let skip_s = a.eq_table(&cols[..K_SKIP]);
        let zero = a.zero();
        let mut weights = vec![[zero; 2]; N_CIRCUITS];
        let (mut row_values, mut skips, mut col_eqs) = (Cache::new(), Cache::new(), Cache::new());
        for (c, &power) in claims.iter().zip(powers) {
            let k = c.circuit.k_log();
            let u = row_values.get_or_insert_with(&c.row, || c.row.at(a, &rows[..k], &skip_r, &mut skips));
            let w = c.col.at(a, &cols[..k], &skip_s, &mut col_eqs);
            let uw = a.mul(u, w);
            let g = a.mul(power, uw);
            let [wa, wb] = &mut weights[c.circuit.index()];
            *wa = c.coefficients[0].times(a, g, *wa);
            *wb = c.coefficients[1].times(a, g, *wb);
        }
        let mut lifts = Cache::new();
        for (f, pair) in CircuitId::ALL.into_iter().zip(&mut weights) {
            let k = f.k_log();
            let lift = lifts.get_or_insert_with(k, || {
                // What a circuit of `k` variables waits on: the later challenges.
                let lift_r = a.product(&rows[k..]);
                let lift_s = a.product(&cols[k..]);
                a.mul(lift_r, lift_s)
            });
            *pair = pair.map(|w| a.mul(w, lift));
        }
        weights
    }
}

impl<E: Copy + PartialEq> RowWeight<E> {
    /// The weight's multilinear extension at `r`, given the eq table of its skip variables and the skip factors so far.
    fn at<A: Arith<E = E>>(&self, a: &mut A, r: &[E], skip: &[E], skips: &mut Cache<E, E>) -> E {
        match self {
            Self::Skip { z, rest } => {
                let low = skips.get_or_insert_with(*z, || {
                    let vanishing = SkipDomain::FLOCK.vanishing(a, *z);
                    SkipDomain::FLOCK.lagrange_at(a, *z, vanishing, skip)
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
    fn at<'c, A: Arith<E = E>>(&'c self, a: &mut A, s: &[E], skip: &[E], eqs: &mut Cache<(bool, &'c [E]), E>) -> E {
        match self {
            Self::Slices { slices, rest } => {
                let zero = a.zero();
                let low = (slices.iter().zip(skip)).fold(zero, |acc, (&x, &e)| a.mul_add(x, e, acc));
                let high = eqs.get_or_insert_with((true, rest.as_slice()), || a.eq_eval(rest, &s[K_SKIP..]));
                a.mul(low, high)
            }
            Self::Point(p) => eqs.get_or_insert_with((false, p.as_slice()), || a.eq_eval(p, s)),
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
            Self::Skip { z, rest } => SkipDomain::FLOCK.inner_eq_table(*z, rest),
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
    pub(super) fn prove(ps: &mut ProverState, claims: &[MatrixClaim<F192>]) {
        let theta = ps.verifier_message();
        let mut rows = Self::new(claims, theta);
        let r: Vec<F192> = (0..CircuitId::MAX_K_LOG)
            .map(|i| {
                ps.prover_messages(&rows.message());
                let x = ps.verifier_message();
                rows.bind(i, x);
                x
            })
            .collect();
        let mut cols = rows.columns(claims, &r);
        for i in 0..CircuitId::MAX_K_LOG {
            ps.prover_messages(&cols.message());
            let x = ps.verifier_message();
            cols.bind(i, x);
        }
        ps.prover_messages(&cols.finals());
    }

    /// The row phase of the claims under the batching challenge `theta`: each claim's tables, one walk of its circuit each.
    pub(super) fn new(claims: &[MatrixClaim<F192>], theta: F192) -> Self {
        let powers: Vec<F192> = std::iter::successors(Some(F192::ONE), |&p| Some(p * theta))
            .take(claims.len())
            .collect();
        let mut claims = parallel::map_collect(claims.len(), |i| {
            let c = &claims[i];
            let u: Vec<F192> = c.row.table().into_iter().map(|x| powers[i] * x).collect();
            let (ra, rb) = c.circuit.circuit().row_values(&c.col.table());
            let [a, b] = c.coefficients.map(Coefficient::value);
            let g = ra.iter().zip(&rb).map(|(&x, &y)| a * x + b * y).collect();
            RowTables {
                k: c.circuit.k_log(),
                pair: FoldPair::new(u, g),
            }
        });
        let message = Msg::sum_mut(
            &mut claims,
            |_, t| if t.k > 0 { t.pair.message() } else { Msg::default() },
        );
        Self { claims, message }
    }

    /// The next row round's message: `h(0)` and the leading coefficient.
    pub(super) const fn message(&self) -> [F192; 2] {
        self.message
    }

    /// Bind row round `i`'s variable to `x`, and build the next round's message from the folded pairs.
    pub(super) fn bind(&mut self, i: usize, x: F192) {
        self.message = Msg::sum_mut(
            &mut self.claims,
            |_, t| {
                if t.k > i { t.pair.fold(x) } else { Msg::default() }
            },
        );
    }

    /// The column phase at the row point `r`: per circuit, two backward walks for `A(r, .)` and `B(r, .)`, and the claims' column weights.
    pub(super) fn columns(&self, claims: &[MatrixClaim<F192>], r: &[F192]) -> ColumnPhase {
        let mut circuits = parallel::map_collect(N_CIRCUITS, |f| {
            let f = CircuitId::ALL[f];
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
                let scale = lambda * t.pair.u.first();
                let (sa, sb) = (scale * a, scale * b);
                for ((x, y), w) in wa.iter_mut().zip(wb.iter_mut()).zip(c.col.table()) {
                    *x += sa * w;
                    *y += sb * w;
                }
            }
            [FoldPair::new(wa, at), FoldPair::new(wb, bt)]
        });
        let message = Msg::sum_mut(&mut circuits, |f, [a, b]| {
            if CircuitId::ALL[f].k_log() > 0 {
                a.message() ^ b.message()
            } else {
                Msg::default()
            }
        });
        ColumnPhase { circuits, message }
    }
}

impl ColumnPhase {
    /// The next column round's message.
    pub(super) const fn message(&self) -> [F192; 2] {
        self.message
    }

    /// Bind column round `i`'s variable to `x`, and build the next round's message from the folded pairs.
    pub(super) fn bind(&mut self, i: usize, x: F192) {
        self.message = Msg::sum_mut(&mut self.circuits, |f, [a, b]| {
            if CircuitId::ALL[f].k_log() > i {
                a.fold(x) ^ b.fold(x)
            } else {
                Msg::default()
            }
        });
    }

    /// Each circuit's `A` and `B` at its prefixes of the points, flattened.
    pub(super) fn finals(&self) -> Vec<F192> {
        (self.circuits.iter())
            .flat_map(|[a, b]| [a.g.first(), b.g.first()])
            .collect()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::rec::hash;
    use crate::rec::tree::reduce;

    use fiat_shamir::arith::Portable;
    use fiat_shamir::{ProverState, SessionId, VerifierState};
    use primitives::test_util::Rng;

    // Each circuit's matrices at random points: lincheck claims and both carried claims, on three circuits.
    //
    // The lincheck claims share their points as one batch leaves them: one alpha and one skip point, the other coordinates
    // prefixes of shared ones; circuit 0 has a second claim at its first's point with other slices.
    fn matrix_claims(rng: &mut Rng) -> Vec<MatrixClaim<F192>> {
        let k_skip = flock::zerocheck::K_SKIP;
        let (alpha, z_skip) = (rng.ext(), rng.ext());
        let (x, r) = (rng.ext_vec(16), rng.ext_vec(16));
        let mut claims = Vec::new();
        let first = CircuitId::ALL[0];
        for (i, f) in [first, first, CircuitId::ALL[3], hash::CIRCUIT].into_iter().enumerate() {
            let circuit = f.circuit();
            let k = circuit.k_log();
            let form = MatrixForm {
                alpha,
                z_skip,
                x_inner_rest: x[..k - k_skip].to_vec(),
                r_inner_rest: r[..k - k_skip].to_vec(),
                s_hat_v: rng.ext_vec(1 << k_skip),
            };
            let value = form.evaluate(&mut Portable, circuit);
            claims.push(MatrixClaim::fresh(f, &Claim { point: form, value }));
            if i == 0 {
                continue;
            }
            let (rows, cols) = (rng.ext_vec(k), rng.ext_vec(k));
            let (ra, rb) = circuit.row_values(&eq_table(&cols));
            let u = eq_table(&rows);
            let dot = |r: &[F192]| u.iter().zip(r).fold(F192::ZERO, |acc, (&x, &y)| acc + x * y);
            claims.extend(MatrixClaim::carried(f, k, &rows, &cols, [dot(&ra), dot(&rb)]));
        }
        claims
    }

    #[test]
    fn the_matrix_reduction_reduces_to_the_matrices() {
        let mut rng = Rng::new(9);
        let claims = matrix_claims(&mut rng);
        let prove = |claims: &[MatrixClaim<F192>]| {
            let mut ps = ProverState::new(
                &SessionId::tagged(reduce::SESSION_TAG, &SessionId::new(b"tree-test").0),
                &0u64,
            );
            MatrixProver::prove(&mut ps, claims);
            ps.into_proof()
        };
        let verify = |claims: &[MatrixClaim<F192>], proof| {
            let mut vs = VerifierState::new(
                &SessionId::tagged(reduce::SESSION_TAG, &SessionId::new(b"tree-test").0),
                &0u64,
                proof,
            );
            MatrixReduced::verify(&mut vs, claims)
        };
        let proof = prove(&claims);
        let reduced = verify(&claims, &proof).expect("an honest reduction");
        for (f, values) in CircuitId::ALL.into_iter().zip(&reduced.values) {
            let circuit = f.circuit();
            let k = circuit.k_log();
            let (ra, rb) = circuit.row_values(&eq_table(&reduced.cols[..k]));
            let u = eq_table(&reduced.rows[..k]);
            let dot = |r: &[F192]| u.iter().zip(r).fold(F192::ZERO, |acc, (&x, &y)| acc + x * y);
            assert_eq!(*values, [dot(&ra), dot(&rb)], "{f:?}");
        }
        for c in [0, 2] {
            let mut false_claims = claims.clone();
            false_claims[c].value += F192::ONE;
            assert_eq!(
                verify(&false_claims, &proof).err(),
                Some(ReduceError::Matrix),
                "claim {c}"
            );
        }
    }
}
