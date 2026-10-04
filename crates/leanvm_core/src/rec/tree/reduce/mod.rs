//! A node's claim reduction: the claims its verified proofs leave, fresh and carried, become one of each kind.
//!
//! It is a small proof of its own, made natively by the node's prover and verified in the node's rows:
//!
//! - its transcript first binds every verified proof's final state and every hint the claims rest on;
//! - the dense reduction takes every claim on the dense polynomials to one point;
//! - the matrix reduction takes every claim on the flock circuits' matrices to one row point and one column point.
//!
//! Each is a sumcheck: if an input claim is false, an output claim is false but with probability about `(claims + 2 rounds) / |E|`.

mod dense;
mod matrix;

pub(crate) use dense::{DenseProver, DenseReduced, DenseVars};
pub(crate) use matrix::{MatrixProver, MatrixReduced};

use super::claims::NodeClaims;
use crate::arith::Verifier;
use crate::rec::circuit::{Limbs, digest_limbs};
use fiat_shamir::transcript::{Proof, ProverState, TranscriptError, Transmitter};
use primitives::field::{F64, F192};

/// The label every node's reduction transcript starts from.
pub(crate) const LABEL: &[u8] = b"leanvm-tree-reduction";

/// Why a node's reduction refuses.
#[derive(Clone, Copy, Debug, PartialEq, Eq, thiserror::Error)]
pub(crate) enum ReduceError {
    /// The reduction's stream is malformed.
    #[error(transparent)]
    Transcript(#[from] TranscriptError),
    /// A value the transcript binds is not the one the claims rest on.
    #[error("a bound value is not the claims'")]
    Bound,
    /// The dense reduction's final identity fails.
    #[error("the dense reduction's final identity fails")]
    Dense,
    /// The matrix reduction's final identity fails.
    #[error("the matrix reduction's final identity fails")]
    Matrix,
}

/// What a node's reduction leaves: the dense polynomials at one point, the matrices at one row and one column point.
pub(crate) struct Reduced<E> {
    /// The dense reduction's outputs.
    pub(crate) dense: DenseReduced<E>,
    /// The matrix reduction's outputs.
    pub(crate) matrices: MatrixReduced<E>,
}

/// The prover's dense polynomials, each a table of its values: the bytecode table, the image, the fixed polynomial.
#[derive(Clone, Debug)]
pub(crate) struct DenseTables(pub(crate) [Vec<F64>; super::claims::DensePoly::COUNT]);

/// The reduction transcript's starting state.
pub(crate) fn initial_state() -> Limbs {
    digest_limbs(&primitives::hash::hash(LABEL))
}

impl<E: Copy> NodeClaims<E> {
    /// Verify the reduction of these claims, the dense polynomials having the given variables.
    ///
    /// # Errors
    ///
    /// Returns the first check that refuses.
    pub(crate) fn verify<V: Verifier<E = E>>(&self, v: &mut V, vars: &DenseVars) -> Result<Reduced<E>, ReduceError> {
        for &x in &self.bound {
            let read = v.next_scalar()?;
            v.ensure_eq(x, read, || ReduceError::Bound)?;
        }
        let dense = vars.verify(v, &self.dense)?;
        let matrices = MatrixReduced::verify(v, &self.matrices)?;
        Ok(Reduced { dense, matrices })
    }
}

impl NodeClaims<F192> {
    /// Prove the reduction of these claims, which must be true of the given tables.
    #[tracing::instrument(name = "Reduce claims", skip_all)]
    pub(crate) fn prove(&self, vars: &DenseVars, tables: &DenseTables) -> Proof {
        let mut ps = ProverState::from_label(LABEL);
        ps.add_scalars(&self.bound);
        crate::stage!("Dense reduction", || DenseProver::prove(
            &mut ps,
            vars,
            tables,
            &self.dense
        ));
        crate::stage!("Matrix reduction", || MatrixProver::prove(&mut ps, &self.matrices));
        ps.into_proof()
    }
}

/// The table of `f(k)` for `k < n`, written across the pool.
fn table_of(n: usize, f: impl Fn(usize) -> F192 + Sync) -> Vec<F192> {
    if n < PAR_LEN {
        return (0..n).map(f).collect();
    }
    parallel::map_collect(n, f)
}

/// Below this many entries a pass runs on the calling thread.
const PAR_LEN: usize = 1 << 12;

/// `h(0)` and the leading coefficient of `sum_k u(X, k) g(X, k)` over the lowest variable, on the calling thread.
fn products(u: &[F192], g: &[F192]) -> [F192; 2] {
    (0..u.len() / 2).fold([F192::ZERO; 2], |[c0, c2], k| {
        let (u0, u1, g0, g1) = (u[2 * k], u[2 * k + 1], g[2 * k], g[2 * k + 1]);
        [c0 + u0 * g0, c2 + (u0 + u1) * (g0 + g1)]
    })
}

/// The same sums across the pool, `g` of either field, with its product by an element of `E`.
fn products_par<G>(u: &[F192], g: &[G], times: impl Fn(F192, G) -> F192 + Sync) -> [F192; 2]
where
    G: Copy + Sync + std::ops::Add<Output = G>,
{
    let pairs = u.len() / 2;
    let task = |i: usize| {
        (i * PAR_LEN..pairs.min((i + 1) * PAR_LEN)).fold([F192::ZERO; 2], |[c0, c2], k| {
            let (u0, u1, g0, g1) = (u[2 * k], u[2 * k + 1], g[2 * k], g[2 * k + 1]);
            [c0 + times(u0, g0), c2 + times(u0 + u1, g0 + g1)]
        })
    };
    let chunks = pairs.div_ceil(PAR_LEN);
    if chunks <= 1 {
        return task(0);
    }
    let add = |[a, b]: [F192; 2], [c, d]: [F192; 2]| [a + c, b + d];
    parallel::map_reduce(chunks, || [F192::ZERO; 2], task, add)
}

/// A table the prover folds one variable at a time, lowest first, into a second buffer it then swaps with.
#[derive(Clone, Debug)]
struct FoldTable {
    /// The table.
    values: Vec<F192>,
    /// The buffer the next fold writes.
    spare: Vec<F192>,
}

impl FoldTable {
    /// The table of these values.
    const fn new(values: Vec<F192>) -> Self {
        Self {
            values,
            spare: Vec::new(),
        }
    }

    /// Bind the lowest variable to `r`, on the calling thread or across the pool.
    fn fold(&mut self, r: F192, par: bool) {
        let n = self.values.len() / 2;
        self.spare.resize(n, F192::ZERO);
        let t = &self.values;
        let at = |k: usize| t[2 * k] + r * (t[2 * k] + t[2 * k + 1]);
        if par && n >= PAR_LEN {
            parallel::fill(&mut self.spare, at);
        } else {
            for (k, slot) in self.spare.iter_mut().enumerate() {
                *slot = at(k);
            }
        }
        std::mem::swap(&mut self.values, &mut self.spare);
    }
}
