//! The recursion machine's bus: every slot carries its wire, and the slots of a wire class form a copy cycle.
//!
//! Every slot of row `z` carries `(key, v0, v1, v2, v3)` on the bus:
//!
//! - it pulls the tuple at its own key;
//! - it pushes the tuple at `next`, a public column holding the key of the next slot of its wire class.
//!
//! The slots of a class, in table, row and slot order, form one cycle.
//! A padding row's `next` is its own key, which cancels whatever it carries.

use super::circuit::{Circuit, Limbs, PubSource};
use super::layout::RecLayout;
use super::table::Table;
use crate::colval::ColVal;
use crate::constraints;
use crate::leaf::{self, Block, BusForm, BusProof, BusVerify, Coord};
use fiat_shamir::transcript::{ProverState, VerifierState};
use primitives::field::{F64, F192};
use std::sync::Arc;

/// A slot's key on the bus: its index among all tables' slots in the high 32 bits, its row in the low 32.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct SlotKey(u64);

/// Each slot's `next` column: the key of the next slot of its wire class, its own on a padding row.
#[derive(Clone, Debug)]
pub(crate) struct CopyCycles {
    /// Per slot among all tables' slots, one key per row of its table.
    next: Vec<Vec<F64>>,
}

/// The bus's push and pull blocks: the public table's pair, which no table owns, then one pair per owned slot.
#[derive(Clone, Debug)]
pub(crate) struct BusBlocks {
    push: Vec<Block>,
    pull: Vec<Block>,
}

/// A table's whole summand in the constraint batch: its bus forms and its identities, already weighted.
pub(crate) struct TableSummand(BusForm);

impl SlotKey {
    /// Slot `slot` of `table` at row `row`, which is below `2^32`.
    pub(crate) const fn new(table: Table, slot: usize, row: usize) -> Self {
        Self(((table.first_slot() + slot) as u64) << 32 | row as u64)
    }

    /// Its slot's index among all tables' slots.
    const fn global_slot(self) -> usize {
        (self.0 >> 32) as usize
    }

    /// Its row.
    const fn row(self) -> usize {
        (self.0 & u32::MAX as u64) as usize
    }

    /// The key as a `K` word.
    const fn to_f64(self) -> F64 {
        F64(self.0)
    }

    /// A slot's keys down its rows, as a column: the key at row `z` is row zero's XOR `z`.
    const fn column(table: Table, slot: usize) -> Coord {
        Coord::IntIndex {
            base: Self::new(table, slot, 0).to_f64(),
            shift: 0,
        }
    }
}

impl CopyCycles {
    /// The cycles of a circuit's wire classes, at the given table heights.
    pub(crate) fn of(circuit: &Circuit, taus: &[usize; Table::COUNT]) -> Self {
        let mut next: Vec<Vec<F64>> = (Table::ALL.into_iter())
            .flat_map(|t| {
                let height = 1 << taus[t as usize];
                (0..t.n_slots()).map(move |s| (0..height).map(|z| SlotKey::new(t, s, z).to_f64()).collect())
            })
            .collect();
        let mut link = |from: SlotKey, to: SlotKey| next[from.global_slot()][from.row()] = to.to_f64();

        // Each class's first and last slot so far: every slot links the last to itself.
        let mut ends: Vec<Option<(SlotKey, SlotKey)>> = vec![None; circuit.n_classes()];
        for t in Table::ALL {
            let n = t.n_slots();
            for (i, &class) in circuit.classes.of(t).iter().enumerate() {
                let key = SlotKey::new(t, i % n, i / n);
                match &mut ends[class as usize] {
                    Some((_, last)) => {
                        link(*last, key);
                        *last = key;
                    }
                    end @ None => *end = Some((key, key)),
                }
            }
        }
        // The last slot closes the cycle back to the first.
        for (first, last) in ends.into_iter().flatten() {
            link(last, first);
        }
        Self { next }
    }

    /// Take slot `slot` of `table`'s column.
    fn take(&mut self, table: Table, slot: usize) -> Vec<F64> {
        std::mem::take(&mut self.next[table.first_slot() + slot])
    }
}

impl BusBlocks {
    /// The blocks of a circuit at a layout's heights, the public rows reading the statement.
    pub(crate) fn new(circuit: &Circuit, statement: &[Limbs], layout: &RecLayout) -> Self {
        let mut next = CopyCycles::of(circuit, &layout.taus);
        let mut blocks = Self {
            push: Vec::new(),
            pull: Vec::new(),
        };
        let public = Table::Pub;
        let values = Self::public_values(circuit, statement, layout.tau(public));
        blocks.add_pair(public, 0, layout.tau(public), next.take(public, 0), values);
        for table in Table::OWNED {
            let base = RecLayout::columns(table).start;
            for s in 0..table.n_slots() {
                let limbs = table.slot(s).offset(base).into();
                blocks.add_pair(table, s, layout.tau(table), next.take(table, s), limbs);
            }
        }
        blocks
    }

    /// The public table's four value columns: each row's constant or statement word.
    fn public_values(circuit: &Circuit, statement: &[Limbs], tau: usize) -> Vec<Coord> {
        let mut values: [Vec<F64>; 4] = std::array::from_fn(|_| vec![F64::ZERO; 1 << tau]);
        for (z, source) in circuit.pubs.iter().enumerate() {
            let v = match *source {
                PubSource::Const(v) => v,
                PubSource::Statement(i) => statement[i],
            };
            for (column, &v) in values.iter_mut().zip(&v) {
                column[z] = F64(v);
            }
        }
        values.into_iter().map(|v| Coord::Public(Arc::new(v))).collect()
    }

    /// A slot's pull block at its own keys and its push block at `next`, both carrying `limbs`.
    ///
    /// An owned table's blocks are its own, the public table's the framework's.
    fn add_pair(&mut self, table: Table, slot: usize, tau: usize, next: Vec<F64>, limbs: Vec<Coord>) {
        let block = |key: Coord, limbs: Vec<Coord>| {
            let coords = std::iter::once(key).chain(limbs).collect();
            match table {
                Table::Pub => Block::framework(tau, coords),
                owned => Block::table(owned as usize, tau, coords),
            }
        };
        self.pull.push(block(SlotKey::column(table, slot), limbs.clone()));
        self.push.push(block(Coord::Public(Arc::new(next)), limbs));
    }

    /// Prove the bus balances over the global columns.
    pub(crate) fn prove(&self, cols: &[&[F64]], ps: &mut ProverState) -> BusProof {
        leaf::prove_balance(&self.push, &self.pull, &[], cols, &RecLayout::TABLE_COLUMNS, ps)
    }

    /// Verify the bus balances.
    ///
    /// # Errors
    ///
    /// Returns the first check of the balance that refuses.
    pub(crate) fn verify(&self, vs: &mut VerifierState) -> Result<BusVerify, leaf::Error> {
        let bus = leaf::verify_balance(&self.push, &self.pull, &[], &RecLayout::TABLE_COLUMNS, vs)?;
        debug_assert!(
            bus.sparse.iter().all(Vec::is_empty) && bus.producers.is_empty(),
            "the machine's target has no share for sparse columns or producers"
        );
        Ok(bus)
    }
}

impl TableSummand {
    /// Each owned table's summand.
    ///
    /// Its push and pull forms weigh `1` and `xi`, then each identity has a power of `xi` of its own from `xi^2`.
    /// The tables' ranges of powers are disjoint.
    pub(crate) fn batch(forms: &[Vec<BusForm>; 2], xi: F192) -> Vec<Self> {
        let ids = Table::OWNED.map(Table::identities);
        let offsets = constraints::xi_offsets(ids.iter().map(Vec::len));
        (ids.into_iter().zip(offsets).enumerate())
            .map(|(t, (ids, offset))| {
                let mut power = (0..offset).fold(xi * xi, |p, _| p * xi);
                let mut parts = vec![forms[0][t].clone(), forms[1][t].scaled(xi)];
                for id in ids {
                    parts.push(id.scaled(power));
                    power *= xi;
                }
                Self(BusForm::sum(parts))
            })
            .collect()
    }
}

impl constraints::Summand for TableSummand {
    #[inline(always)]
    fn eval<V: ColVal>(&self, cols: &[V], quadratic: bool) -> F192 {
        V::reduce(self.0.eval_unreduced(cols, quadratic))
    }
}
