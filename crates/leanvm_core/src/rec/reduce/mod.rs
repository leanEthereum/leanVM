//! A node's claim reduction: the claims its verified proofs leave, fresh and carried, become one of each kind.
//!
//! It is a small proof of its own, made natively by the node's prover and verified by the node's program:
//!
//! - its transcript first binds every verified proof's final state and every hint the claims rest on;
//! - the dense reduction takes every claim on the dense polynomials to one point;
//! - the matrix reduction takes every claim on the flock circuits' matrices to one row point and one column point.
//!
//! Each is a sumcheck: if an input claim is false, an output claim is false but with probability about `(claims + 2 rounds) / |E|`.

use super::claims::{DensePoly, NodeClaims};
use crate::rec::hash::{Limbs, digest_limbs};
use fiat_shamir::arith::Verifier;
use fiat_shamir::transcript::{ProofTranscript, ProverState, TranscriptError, Transmitter};
use primitives::field::{F64, F192, F192Unreduced, mul_base8, mul_unreduced4, mul4};
use std::ops::{Index, IndexMut};
use thiserror::Error;

mod dense;
mod matrix;
#[cfg(test)]
mod tests;

pub(crate) use dense::{DenseProver, DenseReduced, DenseVars};
pub(crate) use matrix::{MatrixProver, MatrixReduced};

/// The label every node's reduction transcript starts from.
pub(crate) const LABEL: &[u8] = b"leanvm-tree-reduction-3";

/// Why a node's reduction refuses.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Error)]
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
pub(crate) struct DenseTables(pub(crate) [Vec<F64>; DensePoly::COUNT]);

impl Index<DensePoly> for DenseTables {
    type Output = Vec<F64>;

    fn index(&self, poly: DensePoly) -> &Vec<F64> {
        &self.0[poly as usize]
    }
}

impl IndexMut<DensePoly> for DenseTables {
    fn index_mut(&mut self, poly: DensePoly) -> &mut Vec<F64> {
        &mut self.0[poly as usize]
    }
}

/// The reduction transcript's starting state.
pub(crate) fn initial_state() -> Limbs {
    digest_limbs(&primitives::hash::hash(LABEL))
}

impl<E: Copy + PartialEq> NodeClaims<E> {
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
    pub(crate) fn prove(&self, vars: &DenseVars, tables: &DenseTables) -> ProofTranscript {
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

/// A round's message, `h(0)` and the leading coefficient, unreduced.
type Msg = [F192Unreduced; 2];

/// The zero message.
const ZERO: Msg = [F192Unreduced::ZERO; 2];

/// The sum of two messages.
fn xor([a, b]: Msg, [c, d]: Msg) -> Msg {
    [a ^ c, b ^ d]
}

/// The entries a pass keeps in L1 at once.
const TILE: usize = 64;

/// An entry of a table a round folds: in `K` before the first round, in `E` after.
trait Entry: Copy + Sync {
    /// `a + r (a + b)`.
    fn fold(a: Self, b: Self, r: F192) -> F192;

    /// The folds of `t`'s pairs into `out`.
    fn fold_into(t: &[Self], r: F192, out: &mut [F192]);

    /// The message of `sum_k w(X, k) t(X, k)` over the lowest variable: `sum_k w(2k) t(2k)` and
    /// `sum_k (w(2k) + w(2k + 1)) (t(2k) + t(2k + 1))`.
    fn dot(w: &[F192], t: &[Self]) -> Msg;
}

impl Entry for F192 {
    fn fold(a: Self, b: Self, r: F192) -> F192 {
        a + r * (a + b)
    }

    fn fold_into(t: &[Self], r: F192, out: &mut [F192]) {
        let (t8, t_rest) = t.as_chunks::<8>();
        let (out4, out_rest) = out.as_chunks_mut::<4>();
        for (o, x) in out4.iter_mut().zip(t8) {
            let d = mul4([r; 4], [x[0] + x[1], x[2] + x[3], x[4] + x[5], x[6] + x[7]]);
            *o = [x[0] + d[0], x[2] + d[1], x[4] + d[2], x[6] + d[3]];
        }
        for (o, x) in out_rest.iter_mut().zip(t_rest.as_chunks::<2>().0) {
            *o = Self::fold(x[0], x[1], r);
        }
    }

    fn dot(w: &[F192], t: &[Self]) -> Msg {
        let (w4, w_rest) = w.as_chunks::<4>();
        let (t4, t_rest) = t.as_chunks::<4>();
        let mut m = ZERO;
        for (a, b) in w4.iter().zip(t4) {
            let p = mul_unreduced4(
                [a[0], a[0] + a[1], a[2], a[2] + a[3]],
                [b[0], b[0] + b[1], b[2], b[2] + b[3]],
            );
            m = xor(m, [p[0] ^ p[2], p[1] ^ p[3]]);
        }
        for (a, b) in w_rest.as_chunks::<2>().0.iter().zip(t_rest.as_chunks::<2>().0) {
            m = xor(m, [a[0].mul_unreduced(b[0]), (a[0] + a[1]).mul_unreduced(b[0] + b[1])]);
        }
        m
    }
}

impl Entry for F64 {
    fn fold(a: Self, b: Self, r: F192) -> F192 {
        F192::from(a) + r.mul_base(a + b)
    }

    fn fold_into(t: &[Self], r: F192, out: &mut [F192]) {
        let (t16, t_rest) = t.as_chunks::<16>();
        let (out8, out_rest) = out.as_chunks_mut::<8>();
        for (o, x) in out8.iter_mut().zip(t16) {
            let d = mul_base8(r, std::array::from_fn(|k| x[2 * k] + x[2 * k + 1]));
            *o = std::array::from_fn(|k| d[k] + F192::from(x[2 * k]));
        }
        for (o, x) in out_rest.iter_mut().zip(t_rest.as_chunks::<2>().0) {
            *o = Self::fold(x[0], x[1], r);
        }
    }

    fn dot(w: &[F192], t: &[Self]) -> Msg {
        let pairs = w.as_chunks::<2>().0.iter().zip(t.as_chunks::<2>().0);
        pairs.fold(ZERO, |m, (a, b)| {
            xor(
                m,
                [
                    a[0].mul_base_unreduced(b[0]),
                    (a[0] + a[1]).mul_base_unreduced(b[0] + b[1]),
                ],
            )
        })
    }
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

    /// The message of `sum_k u(X, k) g(X, k)` over the lowest variable, on the calling thread.
    fn message(u: &Self, g: &Self) -> Msg {
        F192::dot(&u.values, &g.values)
    }

    /// Bind the lowest variable of `u` and `g` to `r`, and the next round's message from the folded pairs.
    fn fold_pair(u: &mut Self, g: &mut Self, r: F192) -> Msg {
        let n = u.values.len() / 2;
        u.spare.resize(n, F192::ZERO);
        g.spare.resize(n, F192::ZERO);
        let outs = u.spare.chunks_mut(TILE).zip(g.spare.chunks_mut(TILE));
        let ins = u.values.chunks(2 * TILE).zip(g.values.chunks(2 * TILE));
        let m = (outs.zip(ins)).fold(ZERO, |m, ((uo, go), (ui, gi))| {
            F192::fold_into(ui, r, uo);
            F192::fold_into(gi, r, go);
            xor(m, F192::dot(uo, go))
        });
        std::mem::swap(&mut u.values, &mut u.spare);
        std::mem::swap(&mut g.values, &mut g.spare);
        m
    }
}
