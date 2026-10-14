//! A node's claim reduction: the claims its verified proofs leave, fresh and carried, become one of each kind.
//!
//! It is a small proof of its own, made natively by the node's prover and verified in the node's rows:
//!
//! - its transcript's instance is every verified proof's final digest and every hint the claims rest on;
//! - the dense reduction takes every claim on the dense polynomials to one point;
//! - the matrix reduction takes every claim on the flock circuits' matrices to one row point and one column point.
//!
//! Each is a sumcheck: if an input claim is false, an output claim is false but with probability about `(claims + 2 rounds) / |E|`.

use crate::rec::circuit::{Builder, Dw, Ew};
use fiat_shamir::arith::Verifier;
use fiat_shamir::{LengthPrefixed, ProofTranscript, ProverState, SessionId, TranscriptError};
use parallel::ChunkView;
use primitives::field::{F64, F192, F192Unreduced};
use std::iter::Sum;
use std::ops::{BitXor, BitXorAssign};
use thiserror::Error;
use tracing::info_span;

mod dense;
mod matrix;

pub(crate) use dense::{Bits, DenseClaim, DenseProver, DenseReduced, DenseTerm, DenseVars};
pub(crate) use matrix::{MatrixClaim, MatrixProver, MatrixReduced};

/// The protocol half of a node's reduction's session tag.
pub(super) const SESSION_TAG: &[u8] = b"leanvm-tree-reduction-5";

/// The polynomials the leaves and the tree's circuits fix, on which tree proofs carry claims.
///
/// A tree whose leaves fix no such polynomial has none: no claim is ever made on it.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum DensePoly {
    /// The leaves' program's stacked bytecode table, if RISC-V proofs are leaves.
    Bytecode,
    /// That program's RAM image, zero padded to a power of two.
    Image,
    /// The leaves' fixed polynomial `W_leaf`, if proofs of a recursion circuit are leaves: that circuit's fixed columns,
    /// stacked.
    Leaf,
    /// The nodes' fixed polynomial `W_node`: the fixed columns of the circuits of a tree's only tier, or of its small
    /// tier, stacked by their kind's index.
    Fixed,
    /// The fixed columns of a claim-set tree's large tier's circuits, stacked by their kind's index; a tree of one
    /// tier has none.
    Wide,
}

/// What a node reduces: the values its transcript binds first, then its dense and matrix claims.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct NodeClaims<E> {
    /// Each verified proof's final state and every hint its claims rest on, which every challenge follows.
    pub(crate) bound: Vec<E>,
    /// The claims on the dense polynomials.
    pub(crate) dense: Vec<DenseClaim<E>>,
    /// The claims on the flock circuits' matrices.
    pub(crate) matrices: Vec<MatrixClaim<E>>,
}

/// Why a node's reduction refuses.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Error)]
pub(crate) enum ReduceError {
    /// The reduction's stream is malformed.
    #[error(transparent)]
    Transcript(#[from] TranscriptError),
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

/// The prover's dense polynomials, each a table of its values, in `DensePoly` order; one the tree lacks is the zero table of no variables.
#[derive(Clone, Debug)]
pub(crate) struct DenseTables(pub(crate) [Vec<F64>; DensePoly::COUNT]);

impl DensePoly {
    /// How many dense polynomials there are.
    pub const COUNT: usize = 5;

    /// Every dense polynomial, in statement order.
    pub const ALL: [Self; Self::COUNT] = [Self::Bytecode, Self::Image, Self::Leaf, Self::Fixed, Self::Wide];
}

impl<E> Default for NodeClaims<E> {
    fn default() -> Self {
        Self {
            bound: Vec::new(),
            dense: Vec::new(),
            matrices: Vec::new(),
        }
    }
}

impl<E: Copy> NodeClaims<E> {
    /// The same claims, each element mapped by `f`.
    pub(crate) fn map<T>(&self, mut f: impl FnMut(E) -> T) -> NodeClaims<T> {
        NodeClaims {
            bound: self.bound.iter().map(|&x| f(x)).collect(),
            dense: self.dense.iter().map(|c| c.map(&mut f)).collect(),
            matrices: self.matrices.iter().map(|c| c.map(&mut f)).collect(),
        }
    }
}

impl NodeClaims<Ew> {
    /// Bind a verified proof's final transcript digest, as two scalars: its first three words, then its fourth.
    pub(crate) fn bind_state(&mut self, b: &mut Builder, state: Dw) {
        let [w0, w1, w2, w3] = b.d_to_k(state);
        self.bound.extend([b.k_to_e([w0, w1, w2]), b.k_to_e1(w3)]);
    }
}

impl<E: Copy + PartialEq> NodeClaims<E> {
    /// Verify the reduction of these claims, the dense polynomials having the given variables.
    ///
    /// The transcript's instance must be the bound values: see the session and instance the prover starts from.
    ///
    /// # Errors
    ///
    /// Returns the first check that refuses.
    pub(crate) fn verify<V: Verifier<E = E>>(&self, v: &mut V, vars: &DenseVars) -> Result<Reduced<E>, ReduceError> {
        let dense = DenseReduced::verify(v, vars, &self.dense)?;
        let matrices = MatrixReduced::verify(v, &self.matrices)?;
        Ok(Reduced { dense, matrices })
    }
}

impl NodeClaims<F192> {
    /// Prove the reduction of these claims, in the tree of the given session, which must be true of the given tables.
    #[tracing::instrument(name = "Reduce claims", skip_all)]
    pub(crate) fn prove(&self, tree: &SessionId, vars: &DenseVars, tables: &DenseTables) -> ProofTranscript {
        let mut ps = ProverState::new(&SessionId::tagged(SESSION_TAG, &tree.0), &LengthPrefixed(&self.bound));
        info_span!("Dense reduction").in_scope(|| DenseProver::prove(&mut ps, vars, tables, &self.dense));
        info_span!("Matrix reduction").in_scope(|| MatrixProver::prove(&mut ps, &self.matrices));
        ps.into_proof()
    }
}

/// A round's message, unreduced: what the claim leaves the round polynomial `h` to send.
///
/// Messages add by XOR, as unreduced products do, and reduce once when sent.
#[derive(Clone, Copy, Debug, Default)]
struct Msg {
    /// `h(0)`.
    at_zero: F192Unreduced,
    /// The leading coefficient.
    leading: F192Unreduced,
}

impl Msg {
    /// The message of these two coefficients.
    const fn new(at_zero: F192Unreduced, leading: F192Unreduced) -> Self {
        Self { at_zero, leading }
    }

    /// The message as it is sent: `h(0)`, then the leading coefficient.
    fn reduce(self) -> [F192; 2] {
        [self.at_zero.reduce(), self.leading.reduce()]
    }

    /// The sum of `task(i)` for `i < count`, each a task of the pool but for a single one, which runs here.
    fn sum_tasks(count: usize, task: impl Fn(usize) -> Self + Sync) -> Self {
        match count {
            0 => Self::default(),
            1 => task(0),
            count => parallel::map_reduce(count, Self::default, task, Self::bitxor),
        }
    }

    /// The sum of `f(i, item)` over the items, each item a task of the pool, reduced.
    fn sum_mut<T: Send>(items: &mut [T], f: impl Fn(usize, &mut T) -> Self + Sync) -> [F192; 2] {
        let chunks = ChunkView::new(items, 1);
        let task = |i: usize| {
            // SAFETY: each item is taken once, and the items outlive the dispatch.
            f(i, &mut unsafe { chunks.get(i) }[0])
        };
        Self::sum_tasks(chunks.len(), task).reduce()
    }
}

impl BitXor for Msg {
    type Output = Self;

    fn bitxor(self, rhs: Self) -> Self {
        Self::new(self.at_zero ^ rhs.at_zero, self.leading ^ rhs.leading)
    }
}

impl BitXorAssign for Msg {
    fn bitxor_assign(&mut self, rhs: Self) {
        *self = *self ^ rhs;
    }
}

impl Sum for Msg {
    fn sum<I: Iterator<Item = Self>>(iter: I) -> Self {
        iter.fold(Self::default(), Self::bitxor)
    }
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
            let d = Self::mul4([r; 4], [x[0] + x[1], x[2] + x[3], x[4] + x[5], x[6] + x[7]]);
            *o = [x[0] + d[0], x[2] + d[1], x[4] + d[2], x[6] + d[3]];
        }
        for (o, x) in out_rest.iter_mut().zip(t_rest.as_chunks::<2>().0) {
            *o = Self::fold(x[0], x[1], r);
        }
    }

    fn dot(w: &[F192], t: &[Self]) -> Msg {
        let (w4, w_rest) = w.as_chunks::<4>();
        let (t4, t_rest) = t.as_chunks::<4>();
        let mut m = Msg::default();
        for (a, b) in w4.iter().zip(t4) {
            let p = Self::mul_unreduced4(
                [a[0], a[0] + a[1], a[2], a[2] + a[3]],
                [b[0], b[0] + b[1], b[2], b[2] + b[3]],
            );
            m ^= Msg::new(p[0] ^ p[2], p[1] ^ p[3]);
        }
        for (a, b) in w_rest.as_chunks::<2>().0.iter().zip(t_rest.as_chunks::<2>().0) {
            m ^= Msg::new(a[0].mul_unreduced(b[0]), (a[0] + a[1]).mul_unreduced(b[0] + b[1]));
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
            let d = F192::mul_base8(r, std::array::from_fn(|k| x[2 * k] + x[2 * k + 1]));
            *o = std::array::from_fn(|k| d[k] + F192::from(x[2 * k]));
        }
        for (o, x) in out_rest.iter_mut().zip(t_rest.as_chunks::<2>().0) {
            *o = Self::fold(x[0], x[1], r);
        }
    }

    fn dot(w: &[F192], t: &[Self]) -> Msg {
        let pairs = w.as_chunks::<2>().0.iter().zip(t.as_chunks::<2>().0);
        pairs
            .map(|(a, b)| {
                Msg::new(
                    a[0].mul_base_unreduced(b[0]),
                    (a[0] + a[1]).mul_base_unreduced(b[0] + b[1]),
                )
            })
            .sum()
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

    /// The table's first entry: its value once every variable is bound.
    fn first(&self) -> F192 {
        self.values[0]
    }
}

/// A weight table `u` and the table `g` it weighs, folded together, round by round.
#[derive(Clone, Debug)]
struct FoldPair {
    /// The weight.
    u: FoldTable,
    /// The weighed table.
    g: FoldTable,
}

impl FoldPair {
    /// The pair of these two tables, of one length.
    const fn new(u: Vec<F192>, g: Vec<F192>) -> Self {
        Self {
            u: FoldTable::new(u),
            g: FoldTable::new(g),
        }
    }

    /// The message of `sum_k u(X, k) g(X, k)` over the lowest variable, on the calling thread.
    fn message(&self) -> Msg {
        F192::dot(&self.u.values, &self.g.values)
    }

    /// Bind the lowest variable of both tables to `r`, and the next round's message from the folded pairs.
    fn fold(&mut self, r: F192) -> Msg {
        let (u, g) = (&mut self.u, &mut self.g);
        let n = u.values.len() / 2;
        u.spare.resize(n, F192::ZERO);
        g.spare.resize(n, F192::ZERO);
        let outs = u.spare.chunks_mut(TILE).zip(g.spare.chunks_mut(TILE));
        let ins = u.values.chunks(2 * TILE).zip(g.values.chunks(2 * TILE));
        let m = (outs.zip(ins))
            .map(|((uo, go), (ui, gi))| {
                F192::fold_into(ui, r, uo);
                F192::fold_into(gi, r, go);
                F192::dot(uo, go)
            })
            .sum();
        std::mem::swap(&mut u.values, &mut u.spare);
        std::mem::swap(&mut g.values, &mut g.spare);
        m
    }
}

#[cfg(test)]
pub(crate) mod tests {
    use super::*;
    use crate::tables::CircuitId;
    use fiat_shamir::ProverState;
    use fiat_shamir::arith::{Arith, Native};

    // Which of a reduction's outputs a forging prover moves along its final identity.
    #[derive(Clone, Copy, Debug)]
    pub(crate) enum Forge {
        Dense,
        Matrix,
    }

    // Move the first two values against each other along `sum_i weights_i values_i`, which stays as it was.
    fn shift(values: &mut [F192], weights: &[F192]) {
        let delta = F192::new(1, 2, 3);
        values[0] += delta;
        values[1] += delta * weights[0] * weights[1].inv();
    }

    // The honest reduction of `claims`, its dense or its matrix outputs moved along their final identity.
    pub(crate) fn forged_reduction(
        tree: &SessionId,
        vars: &DenseVars,
        tables: &DenseTables,
        claims: &NodeClaims<F192>,
        forge: Forge,
    ) -> ProofTranscript {
        let mut ps = ProverState::new(&SessionId::tagged(SESSION_TAG, &tree.0), &LengthPrefixed(&claims.bound));

        let theta = ps.verifier_message();
        let mut dense = DenseProver::new(vars, tables, &claims.dense, theta);
        let point: Vec<F192> = (0..dense.rounds())
            .map(|i| {
                ps.prover_messages(&dense.message());
                let r = ps.verifier_message();
                dense.bind(i, r);
                r
            })
            .collect();
        let mut values = dense.finals();
        if matches!(forge, Forge::Dense) {
            let n_terms = claims.dense.iter().map(|c| c.terms.len()).sum();
            let powers = Native.powers(theta, n_terms);
            let weights: Vec<F192> = (vars.final_weights(&mut Native, &claims.dense, &powers, &point))
                .into_iter()
                .flatten()
                .collect();
            shift(&mut values, &weights);
        }
        ps.prover_messages(&values);

        let theta = ps.verifier_message();
        let mut rows = MatrixProver::new(&claims.matrices, theta);
        let r: Vec<F192> = (0..CircuitId::MAX_K_LOG)
            .map(|i| {
                ps.prover_messages(&rows.message());
                let x = ps.verifier_message();
                rows.bind(i, x);
                x
            })
            .collect();
        let mut cols = rows.columns(&claims.matrices, &r);
        let s: Vec<F192> = (0..CircuitId::MAX_K_LOG)
            .map(|i| {
                ps.prover_messages(&cols.message());
                let x = ps.verifier_message();
                cols.bind(i, x);
                x
            })
            .collect();
        let mut values = cols.finals();
        if matches!(forge, Forge::Matrix) {
            let powers = Native.powers(theta, claims.matrices.len());
            let weights = MatrixReduced::final_weights(&mut Native, &claims.matrices, &powers, &r, &s);
            shift(&mut values, weights.as_flattened());
        }
        ps.prover_messages(&values);
        ps.into_proof()
    }
}
