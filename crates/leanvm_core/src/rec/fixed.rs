//! The columns of a circuit's bus that its wiring alone fixes.
//!
//! - Each slot's `next` column holds the key of the next slot of its wire class, its own key on a padding row.
//! - The public table's four constant columns hold each constant row's limbs, zero on the statement's rows.
//!
//! Two circuits of the same heights differ exactly where these columns do, so the columns name the circuit.

use super::bus::SlotKey;
use super::circuit::{Circuit, Limbs, PubSource};
use super::table::Table;
use primitives::field::F64;
use std::sync::Arc;

/// How many slots all tables have together.
const N_SLOTS: usize = Table::Pub.first_slot() + Table::Pub.n_slots();

/// One fixed column of a circuit's bus.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum FixedColumn {
    /// The `next` column of a slot, by its index among all tables' slots.
    Next(usize),
    /// Limb `j` of the public table's constants.
    Constant(usize),
}

/// A circuit's fixed columns, each at its table's height, in stacking order.
///
/// Every column is its own allocation, which a bus block shares: a verifier recognizes a column by its address.
#[derive(Clone, Debug)]
pub(crate) struct FixedColumns {
    /// The columns, in stacking order.
    columns: Vec<Arc<Vec<F64>>>,
}

impl FixedColumn {
    /// How many fixed columns a circuit has.
    pub(crate) const COUNT: usize = N_SLOTS + 4;

    /// The column at an index of the stacking order: every slot's `next`, then the four constant limbs.
    pub(crate) const fn at(index: usize) -> Self {
        if index < N_SLOTS {
            Self::Next(index)
        } else {
            Self::Constant(index - N_SLOTS)
        }
    }

    /// Its index in the stacking order.
    pub(crate) const fn index(self) -> usize {
        match self {
            Self::Next(slot) => slot,
            Self::Constant(j) => N_SLOTS + j,
        }
    }

    /// The table whose height the column has.
    pub(crate) fn table(self) -> Table {
        match self {
            Self::Next(slot) => (Table::ALL.into_iter().rev())
                .find(|t| t.first_slot() <= slot)
                .expect("slot 0 is the first table's"),
            Self::Constant(_) => Table::Pub,
        }
    }
}

impl FixedColumns {
    /// The fixed columns of a circuit at the given table heights.
    ///
    /// The slots of a wire class, in table, row and slot order, form one cycle: each slot's `next` is the following one's key.
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

        let mut constants: [Vec<F64>; 4] = std::array::from_fn(|_| vec![F64::ZERO; 1 << taus[Table::Pub as usize]]);
        for (z, source) in circuit.pubs.iter().enumerate() {
            if let PubSource::Const(v) = *source {
                for (column, &v) in constants.iter_mut().zip(&v) {
                    column[z] = F64(v);
                }
            }
        }
        Self {
            columns: next.into_iter().chain(constants).map(Arc::new).collect(),
        }
    }

    /// Zero columns at the given heights: what a circuit built from shapes alone reads, whose rows never depend on them.
    pub(crate) fn zeros(taus: &[usize; Table::COUNT]) -> Self {
        let columns = (0..FixedColumn::COUNT)
            .map(|c| Arc::new(vec![F64::ZERO; 1 << taus[FixedColumn::at(c).table() as usize]]))
            .collect();
        Self { columns }
    }

    /// A column.
    pub(crate) fn get(&self, column: FixedColumn) -> &Arc<Vec<F64>> {
        &self.columns[column.index()]
    }

    /// The column whose values these are, recognized by its address.
    pub(crate) fn locate(&self, values: &[F64]) -> Option<FixedColumn> {
        (self.columns.iter())
            .position(|c| std::ptr::eq(c.as_slice(), values))
            .map(FixedColumn::at)
    }

    /// The public table's four value columns: the constants, with the statement's words on their rows, which come first.
    pub(crate) fn public_values(&self, statement: &[Limbs]) -> [Arc<Vec<F64>>; 4] {
        std::array::from_fn(|j| {
            let mut column = self.get(FixedColumn::Constant(j)).to_vec();
            for (cell, word) in column.iter_mut().zip(statement) {
                *cell = F64(word[j]);
            }
            Arc::new(column)
        })
    }
}
