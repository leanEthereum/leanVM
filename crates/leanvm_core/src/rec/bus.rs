//! The recursion machine's bus: every slot carries its wire, and the slots of a wire class form a copy cycle.
//!
//! Every slot of row `z` carries `(key, v0, v1, v2, v3)` on the bus:
//!
//! - it pulls the tuple at its own key;
//! - it pushes the tuple at `next`, a public column holding the key of the next slot of its wire class.
//!
//! The slots of a class, in table, row and slot order, form one cycle.
//! A padding row's `next` is its own key, which cancels whatever it carries.

use super::fixed::{FixedColumn, FixedColumns};
use super::layout::RecLayout;
use super::table::Table;
use crate::arith::{Arith, Verifier};
use crate::colval::ColVal;
use crate::constraints::{Residual, Summand};
use crate::leaf::{Block, BusError, BusForm, BusProof, BusVerify, Coord};
use crate::{constraints, leaf};
use fiat_shamir::transcript::ProverState;
use primitives::field::{F64, F192};
use std::sync::Arc;

/// A slot's key on the bus: its index among all tables' slots in the high 32 bits, its row in the low 32.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct SlotKey(u64);

/// The bus's push and pull blocks: the public table's pair, which no table owns, then one pair per owned slot.
#[derive(Clone, Debug)]
pub(crate) struct BusBlocks {
    push: Vec<Block>,
    pull: Vec<Block>,
}

/// A table's whole summand in the prover's constraint batch: its bus forms and its identities, already weighted.
pub(crate) struct TableSummand(BusForm);

/// A table's summand as the verifiers evaluate it at the batch's point: its two bus forms and its weighted identities.
pub(crate) struct TableResidual<'a, E> {
    forms: [&'a BusForm<E>; 2],
    xi: E,
    /// Each identity and its power of `xi`.
    identities: Vec<(BusForm, E)>,
}

impl SlotKey {
    /// Slot `slot` of `table` at row `row`, which is below `2^32`.
    pub(crate) const fn new(table: Table, slot: usize, row: usize) -> Self {
        Self(((table.first_slot() + slot) as u64) << 32 | row as u64)
    }

    /// Its slot's index among all tables' slots.
    pub(crate) const fn global_slot(self) -> usize {
        (self.0 >> 32) as usize
    }

    /// Its row.
    pub(crate) const fn row(self) -> usize {
        (self.0 & u32::MAX as u64) as usize
    }

    /// The key as a `K` word.
    pub(crate) const fn to_f64(self) -> F64 {
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

impl BusBlocks {
    /// The blocks at a layout's heights, over a circuit's fixed columns and the public table's value columns.
    pub(crate) fn new(fixed: &FixedColumns, public: [Arc<Vec<F64>>; 4], layout: &RecLayout) -> Self {
        let mut blocks = Self {
            push: Vec::new(),
            pull: Vec::new(),
        };
        let next = |table: Table, slot: usize| Arc::clone(fixed.get(FixedColumn::Next(table.first_slot() + slot)));
        let values = public.into_iter().map(Coord::Public).collect();
        let public = Table::Pub;
        blocks.add_pair(public, 0, layout.tau(public), next(public, 0), values);
        for table in Table::OWNED {
            let base = RecLayout::columns(table).start;
            for s in 0..table.n_slots() {
                let limbs = table.slot(s).offset(base).into();
                blocks.add_pair(table, s, layout.tau(table), next(table, s), limbs);
            }
        }
        blocks
    }

    /// A slot's pull block at its own keys and its push block at `next`, both carrying `limbs`.
    ///
    /// An owned table's blocks are its own, the public table's the framework's.
    fn add_pair(&mut self, table: Table, slot: usize, tau: usize, next: Arc<Vec<F64>>, limbs: Vec<Coord>) {
        let block = |key: Coord, limbs: Vec<Coord>| {
            let coords = std::iter::once(key).chain(limbs).collect();
            match table {
                Table::Pub => Block::framework(tau, coords),
                owned => Block::table(owned as usize, tau, coords),
            }
        };
        self.pull.push(block(SlotKey::column(table, slot), limbs.clone()));
        self.push.push(block(Coord::Public(next), limbs));
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
    pub(crate) fn verify<V: Verifier>(&self, v: &mut V) -> Result<BusVerify<V::E>, BusError> {
        let bus = leaf::verify_balance(v, &self.push, &self.pull, &[], &RecLayout::TABLE_COLUMNS)?;
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

impl<'a, E: Copy> TableResidual<'a, E> {
    /// Each owned table's residual, its powers of `xi` those of the prover's batch.
    pub(crate) fn batch<A: Arith<E = E>>(a: &mut A, forms: &'a [Vec<BusForm<E>>; 2], xi: E) -> Vec<Self> {
        let ids = Table::OWNED.map(Table::identities);
        let n_ids: usize = ids.iter().map(Vec::len).sum();
        let powers = a.powers(xi, 2 + n_ids);
        let mut powers = powers[2..].iter().copied();
        (ids.into_iter().enumerate())
            .map(|(t, ids)| Self {
                forms: [&forms[0][t], &forms[1][t]],
                xi,
                identities: ids.into_iter().zip(powers.by_ref()).collect(),
            })
            .collect()
    }
}

impl<A: Arith> Residual<A> for TableResidual<'_, A::E> {
    fn value_at(&self, a: &mut A, cols: &[A::E]) -> A::E {
        let push = self.forms[0].at(a, cols);
        let pull = self.forms[1].at(a, cols);
        let forms = a.mul_add(self.xi, pull, push);
        (self.identities.iter()).fold(forms, |acc, (id, power)| {
            let value = id.at_constants(a, cols);
            a.mul_add(*power, value, acc)
        })
    }
}

impl Summand for TableSummand {
    #[inline(always)]
    fn eval<V: ColVal>(&self, cols: &[V], quadratic: bool) -> F192 {
        V::reduce(self.0.eval_unreduced(cols, quadratic))
    }
}
