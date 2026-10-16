//! The verifier of a recursion proof as rows: the recursion machine verifying its own proofs.
//!
//! - The bus and the table sumcheck are the native verifier's code, over rows that hint every fixed column's evaluation.
//! - The hash table's flock reduction and the opening are the native verifier's code.
//!
//! What the native verifier reads off the circuit, its fixed columns, is left as hinted evaluations.
//! The hash rows' matrices are left as a claim, as a RISC-V proof's circuits' are.

use super::{Rows, infallible};
use crate::commitment::Rate;
use crate::cpu::Claim;
use crate::rec::RecError;
use crate::rec::bus::BusBlocks;
use crate::rec::circuit::{Builder, Dw, Ew, Kw};
use crate::rec::fixed::{FixedColumn, FixedColumns};
use crate::rec::layout::RecLayout;
use crate::rec::proof::TableArgument;
use crate::rec::table::PerRecTable;
use crate::rec::transcript::{ProofSource, Transcript};
use fiat_shamir::SessionId;
use fiat_shamir::arith::Arith;
use flock::lincheck::MatrixForm;
use primitives::field::F192;
use primitives::multilinear::mle_eval_par;

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
    pub(crate) fn new(taus: PerRecTable<usize>, rate: Rate) -> Result<Self, RecError> {
        Ok(Self {
            layout: RecLayout::from_taus(taus)?,
            rate,
        })
    }

    /// The verifier of a proof of this shape as rows, reading the proof from the given source.
    ///
    /// The transcript starts from the session, then absorbs the statement as its instance, as the native verifier does.
    ///
    /// The fixed columns are the proven circuit's, which only a prover holds: its hints are their evaluations.
    pub(crate) fn verify(
        &self,
        b: &mut Builder,
        session: &SessionId,
        statement: &[[Kw; 4]],
        columns: &FixedColumns,
        source: ProofSource<'_>,
    ) -> RecRows {
        // The instance: the statement's limbs, their count first.
        let count = b.k_const(4 * statement.len() as u64);
        let instance: Vec<Kw> = std::iter::once(count)
            .chain(statement.as_flattened().iter().copied())
            .collect();
        let mut t = Transcript::new(b, session, &instance, source);
        let mut hints = FixedHints {
            columns,
            statement,
            statement_eq: None,
            hints: Vec::new(),
        };
        let constants = std::array::from_fn(|j| columns.public(FixedColumn::Constant(j)));
        let blocks = BusBlocks::new(columns, constants, &self.layout);
        b.mark(|| blocks.mark_lines());
        let mut r = Rows::hinting(b, &mut t, &mut hints);

        let matrices = infallible(TableArgument::new(&self.layout, blocks).verify_core(&mut r, self.rate));
        RecRows {
            matrix: matrices.into(),
            hints: hints.hints,
            state: t.digest(b),
        }
    }
}

impl FixedHints<'_> {
    /// A fixed column's evaluation at a point, its fixed part a hint whose value the column gives.
    pub(super) fn evaluate(&mut self, b: &mut Builder, column: FixedColumn, point: &[Ew]) -> Ew {
        let at: Vec<F192> = point.iter().map(|&w| b.e(w)).collect();
        let value = b.free_e(mle_eval_par(self.columns.get(column), &at));
        self.hints.push(FixedHint {
            column,
            point: point.to_vec(),
            value,
        });
        match column {
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::rec::verifier::tests::LABEL;

    use crate::commitment::Rate;
    use crate::rec::circuit::{Builder, Circuit, Finished, Kw, Limbs};
    use crate::rec::fixed::FixedColumns;
    use crate::rec::hash;
    use crate::rec::proof::CircuitKey;
    use crate::rec::transcript::ProofSource;

    use fiat_shamir::SessionId;

    use primitives::field::F192;

    // A recursion proof of a small circuit, as rows of another.
    fn recursion_rows(
        circuit: &Circuit,
        statement: &[Limbs],
        columns: &FixedColumns,
        source: ProofSource<'_>,
    ) -> (Builder, RecRows) {
        let shape = RecShape::new(circuit.heights(), Rate::MIN).expect("a layout");
        let mut b = Builder::new();
        let limbs: Vec<[Kw; 4]> = statement.iter().map(|w| w.map(|l| b.free_k(l))).collect();
        let rows = shape.verify(&mut b, &SessionId::new(LABEL), &limbs, columns, source);
        (b, rows)
    }

    // The rows hold on an honest proof, leave a hash matrix claim that settles and true fixed hints, and are the shape's rows.
    #[test]
    fn a_recursion_proof_in_rows_is_its_verifier() {
        let mut b = Builder::new();
        let x = b.free_e(F192::new(3, 5, 7));
        let y = b.e_const(F192::new(11, 13, 17));
        let mut acc = b.d_const([1, 2, 3, 4]);
        let observe = b.k_const(1);
        let mut e = x;
        for _ in 0..40 {
            e = b.mul_add(e, y, x);
            acc = b.compress(acc, e, observe).0;
        }
        let w = b.free_k(0xfeed);
        b.split(w);
        b.expose(acc);
        b.expose(e);
        let Finished {
            circuit,
            assignment: a,
            failures,
        } = b.finish();
        assert!(failures.is_empty(), "{failures:?}");
        let session = SessionId::new(LABEL);
        let key = CircuitKey::new(circuit.clone()).expect("the circuit fits");
        let proof = key.prove(&a, &session, Rate::MIN);
        let openings = key
            .verify(a.statement(), &session, Rate::MIN, &proof)
            .expect("an honest proof");
        let columns = key.fixed();

        let (b, rows) = recursion_rows(&circuit, a.statement(), columns, ProofSource::Proof(&proof, &openings));
        let form = rows.matrix.point.map(|w| b.e(w));
        assert_eq!(
            form.evaluate(hash::CIRCUIT.circuit()),
            b.e(rows.matrix.value),
            "the hash rows' matrix claim settles"
        );
        for hint in &rows.hints {
            let point: Vec<F192> = hint.point.iter().map(|&w| b.e(w)).collect();
            let column = columns.get(hint.column);
            assert_eq!(b.e(hint.value), primitives::multilinear::mle_eval(column, &point));
        }
        let Finished {
            circuit: proven,
            failures,
            ..
        } = b.finish();
        assert!(failures.is_empty(), "{failures:?}");
        let zeros = FixedColumns::zeros(&circuit.heights());
        let (shaped, _) = recursion_rows(&circuit, a.statement(), &zeros, ProofSource::Shape);
        assert!(proven == shaped.finish().circuit, "the shape builds another circuit");

        // A tampered scalar, and a statement word the proof is not of.
        let mut forged = proof.clone();
        forged.narg[24 * 7 + 8] ^= 1;
        let (b, _) = recursion_rows(&circuit, a.statement(), columns, ProofSource::Proof(&forged, &openings));
        assert!(!b.finish().failures.is_empty(), "a forged scalar passes");
        let mut statement = a.statement().to_vec();
        statement[1][2] ^= 1;
        let (b, _) = recursion_rows(&circuit, &statement, columns, ProofSource::Proof(&proof, &openings));
        assert!(!b.finish().failures.is_empty(), "another statement passes");
    }
}
