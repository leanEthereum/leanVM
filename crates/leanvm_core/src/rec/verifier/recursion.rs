//! The verifier of a recursion proof as rows: the recursion machine verifying its own proofs.
//!
//! - The bus and the table sumcheck are the native verifier's code, over rows that hint every fixed column's evaluation.
//! - The hash table's flock reduction and the opening are the replays a RISC-V proof's verifier uses.
//!
//! What the native verifier reads off the circuit, its fixed columns, is left as hinted evaluations.
//! The hash rows' matrices are left as a claim, as a RISC-V proof's circuits' are.

use super::flock::Reduction;
use super::whir::Opening;
use super::{Rows, infallible};
use crate::arith::Arith;
use crate::class_flock;
use crate::cpu::Claim;
use crate::pcs::Rate;
use crate::rec::RecError;
use crate::rec::bus::BusBlocks;
use crate::rec::circuit::{Builder, Dw, Ew, Kw};
use crate::rec::fixed::{FixedColumn, FixedColumns};
use crate::rec::layout::RecLayout;
use crate::rec::proof::TableArgument;
use crate::rec::table::{HashFlock, Table};
use crate::rec::transcript::{ProofSource, Transcript};
use ::flock::lincheck::MatrixForm;
use primitives::field::{F64, F192};
use primitives::multilinear::mle_eval_par;
use std::sync::Arc;

/// What fixes the rows verifying a recursion proof: its circuit's heights and the commitment's rate.
#[derive(Clone, Debug)]
pub(crate) struct RecShape {
    /// The proven circuit's layout.
    layout: RecLayout,
    /// The commitment's rate.
    rate: Rate,
}

/// What verifying a recursion proof in rows leaves as wires.
pub(crate) struct RecRows {
    /// The claim on the hash rows' matrices.
    pub(crate) matrix: Claim<MatrixForm<Ew>, Ew>,
    /// The hinted evaluations of the proof's circuit's fixed columns.
    pub(crate) hints: Vec<FixedHint>,
    /// The transcript's final state, which binds every scalar the proof sent.
    pub(crate) state: Dw,
}

/// One evaluation of a fixed column, taken as a hint: the column, the point, and the hint.
pub(crate) struct FixedHint {
    /// The column.
    pub(crate) column: FixedColumn,
    /// The point, the bus point's prefix of the column's height.
    pub(crate) point: Vec<Ew>,
    /// The hint.
    pub(crate) value: Ew,
}

/// The fixed columns of the recursion proof being verified, whose evaluations the rows take as hints.
///
/// The public table's value columns are its constants plus the statement, which comes first.
/// The rows evaluate the statement's part from its words, and only the constants' part is a hint.
pub(crate) struct FixedHints<'c> {
    /// The proven circuit's fixed columns, which give the hints' values.
    columns: &'c FixedColumns,
    /// The statement's words as limbs.
    statement: &'c [[Kw; 4]],
    /// The statement rows' weights at the last point the public table was evaluated at.
    statement_eq: Option<StatementWeights>,
    /// The hints taken so far.
    hints: Vec<FixedHint>,
}

/// The statement rows' weights `eq(z, p)` at one point: the low part per row, and the high part they share.
struct StatementWeights {
    /// The point.
    point: Vec<Ew>,
    /// Each row's weight on the low coordinates.
    eq: Vec<Ew>,
    /// The weight on the others, which every row shares.
    high: Ew,
}

impl RecShape {
    /// The shape of a recursion proof of a circuit of these heights at this rate.
    ///
    /// # Errors
    ///
    /// Returns an error if the heights admit no layout.
    pub(crate) fn new(taus: [usize; Table::COUNT], rate: Rate) -> Result<Self, RecError> {
        Ok(Self {
            layout: RecLayout::from_taus(taus)?,
            rate,
        })
    }

    /// The verifier of a proof of this shape as rows, reading the proof from the given source.
    ///
    /// The transcript starts from the seed and the hash of the statement's limbs, as the native verifier's does.
    ///
    /// The fixed columns are the proven circuit's, which only a prover holds: its hints are their evaluations.
    pub(crate) fn verify(
        &self,
        b: &mut Builder,
        iv: Dw,
        statement: &[[Kw; 4]],
        columns: &FixedColumns,
        source: ProofSource<'_>,
    ) -> RecRows {
        let limbs: Vec<Kw> = statement.iter().flatten().copied().collect();
        let seed = b.chain(&limbs);
        let [w0, w1, w2, w3] = b.d_to_k(seed);
        let first = b.k_to_e([w0, w1, w2]);
        let mut t = Transcript::new(b, iv, (first, w3), source);
        let mut hints = FixedHints {
            columns,
            statement,
            statement_eq: None,
            hints: Vec::new(),
        };
        let mut r = Rows::hinting(b, &mut t, &mut hints);

        let root = r.t.next_root(r.b);
        let constants = std::array::from_fn(|j| Arc::clone(columns.get(FixedColumn::Constant(j))));
        let blocks = BusBlocks::new(columns, constants, &self.layout);
        let slots = r.scope("bus and tables", |r| {
            infallible(TableArgument::new(&self.layout, blocks).verify(r))
        });
        let shape = class_flock::shape(HashFlock::index());
        let tau = self.layout.tau(Table::Hash);
        let reduction = r.scope("flock", |r| Reduction::replay(r, shape, tau));
        let window = self.layout.hash_window();
        let rings = [::flock::reduction::ring_switch_verify(
            window.n_vars,
            window.offset,
            &reduction.slice,
        )];
        let opening = Opening {
            slots: &slots,
            rings: &rings,
            shape: self.layout.shape,
            log_inv_rate: self.rate.log_inv_rate().into(),
        };
        r.scope("opening", |r| opening.verify(r, root));
        if !r.t.finished() {
            r.scope("transcript", |r| {
                r.b.fail("the proof has data the verifier never reads");
            });
        }
        RecRows {
            matrix: reduction.matrix,
            hints: hints.hints,
            state: t.state(),
        }
    }
}

impl FixedHints<'_> {
    /// A public column's evaluation at a point, its fixed part a hint whose value the column gives.
    ///
    /// # Panics
    ///
    /// Panics if the column is none of the fixed columns: the bus of a recursion proof reads no other public column.
    pub(super) fn evaluate(&mut self, b: &mut Builder, column: &[F64], point: &[Ew]) -> Ew {
        let fixed = (self.columns)
            .locate(column)
            .expect("a recursion proof's bus reads only its fixed columns");
        let at: Vec<F192> = point.iter().map(|&w| b.e(w)).collect();
        let value = b.free_e(mle_eval_par(column, &at));
        self.hints.push(FixedHint {
            column: fixed,
            point: point.to_vec(),
            value,
        });
        match fixed {
            FixedColumn::Next(_) => value,
            FixedColumn::Constant(j) => {
                let statement = self.statement_at(b, j, point);
                b.add(value, statement)
            }
        }
    }

    /// The statement's share of the public table's limb-`j` column at a point `p`: `sum_{z < S} eq(z, p) limb_j(word_z)`.
    fn statement_at(&mut self, b: &mut Builder, j: usize, point: &[Ew]) -> Ew {
        let weights = match self.statement_eq.take() {
            Some(weights) if weights.point == point => weights,
            _ => StatementWeights::new(b, self.statement.len(), point),
        };
        let zero = b.zero();
        let low = (weights.eq.iter().zip(self.statement)).fold(zero, |acc, (&e, word)| b.mul_k_add(e, word[j], acc));
        let at = b.mul(low, weights.high);
        self.statement_eq = Some(weights);
        at
    }
}

impl StatementWeights {
    /// The weights of the first `n` rows at a point `p`.
    ///
    /// Those rows' indices have no bit past the low `log2(n)`, so `eq(z, p)` is the low weight times `prod (1 + p_i)` above it.
    fn new(b: &mut Builder, n: usize, point: &[Ew]) -> Self {
        let low = crate::log2_ceil_usize(n.max(1));
        assert!(low <= point.len(), "the statement fits the public table");
        let eq = b.eq_table_prefix(&point[..low], n);
        let one = b.one();
        let high = (point[low..].iter()).fold(one, |acc, &x| b.times_one_plus(acc, x));
        Self {
            point: point.to_vec(),
            eq,
            high,
        }
    }
}
