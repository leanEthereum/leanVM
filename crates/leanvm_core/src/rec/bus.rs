//! The recursion machine's bus: every slot carries its wire, and the slots of a wire class form a copy cycle.
//!
//! Every slot of row `z` carries `(key, v0, v1, v2, v3)` on the bus:
//!
//! - it pulls the tuple at its own key;
//! - it pushes the tuple at `next`, a public column holding the key of the next slot of its wire class.
//!
//! The slots of a class, in table, row and slot order, form one cycle.
//! A padding row's `next` is its own key, which cancels whatever it carries.
//!
//! A step or link row also pushes and pulls one dynamic tuple `(key, x0, x1, act, 0)`, keyed by its data:
//!
//! - `act` is its table's activity column, one on the circuit's rows and zero on padding rows, so a padding row's
//!   tuples, equal when its columns are zero, meet no real row's;
//! - every dynamic key has bit 63 set, which no slot key has.

use super::fixed::{FixedColumn, FixedColumns};
use super::layout::RecLayout;
use super::table::Table;
use crate::bus::{Block, BusError, BusForm, BusProof, BusVerify, Coord, PackedForm, PublicColumn, PublicColumns};
use crate::constraints::{Residual, Summand};
use crate::{bus, constraints};
use fiat_shamir::ProverState;
use fiat_shamir::arith::{Arith, Verifier};
use primitives::field::{F64, F192, Subfield};

/// A slot's key on the bus: its index among all tables' slots in the high 32 bits, its row in the low 32.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct SlotKey(u64);

/// The bus's push and pull blocks: the public table's pair, which no table owns, then per present owned table one pair
/// per slot and its dynamic pair, if it has one.
///
/// An owned table's blocks name it by its index among the present tables, whose columns the blocks read.
#[derive(Clone, Debug)]
pub(crate) struct BusBlocks {
    push: Vec<Block>,
    pull: Vec<Block>,
    /// Each present owned table's first global column and its number of columns.
    tables: Vec<(usize, usize)>,
}

/// A table's whole summand in the prover's constraint batch: its bus forms and its identities, already weighted.
pub(crate) struct TableSummand(PackedForm);

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

    /// The keys of this key's slot down its rows, as a column: the key at row `z` is row zero's XOR `z`.
    const fn column(self) -> Coord {
        Coord::IntIndex {
            base: F64(self.0 & !(u32::MAX as u64)),
            shift: 0,
        }
    }
}

impl BusBlocks {
    /// The blocks at a layout's heights, over a circuit's fixed columns and the public table's value columns.
    ///
    /// A table the layout leaves out has no block.
    pub(crate) fn new(fixed: &FixedColumns, public: [PublicColumn; 4], layout: &RecLayout) -> Self {
        let mut blocks = Self {
            push: Vec::new(),
            pull: Vec::new(),
            tables: layout.spans(),
        };
        let next = |table: Table, slot: usize| fixed.public(FixedColumn::Next(table.first_slot() + slot));
        let values = public.into_iter().map(Coord::Public).collect();
        let public = Table::Pub;
        let framework = |tau, coords| Block::framework(tau, coords);
        blocks.add_pair(
            SlotKey::new(public, 0, 0).column(),
            next(public, 0),
            values,
            framework,
            layout.tau(public),
        );
        for (index, &table) in layout.present.iter().enumerate() {
            let (base, tau) = (RecLayout::columns(table).start, layout.tau(table));
            let owned = |tau, coords| Block::table(index, tau, coords);
            for s in 0..table.n_slots() {
                let limbs = table.slot(s).offset(base).into();
                blocks.add_pair(SlotKey::new(table, s, 0).column(), next(table, s), limbs, owned, tau);
            }
            if let Some(tuples) = table.dynamic() {
                let active = fixed.public(FixedColumn::Active(table));
                let [push, pull] = tuples.map(|tuple| {
                    let coords = tuple.map(|c| c.offset(base)).into_iter();
                    let coords = coords
                        .chain([Coord::Public(active.clone()), Coord::Const(F64::ZERO)])
                        .collect();
                    owned(tau, coords)
                });
                blocks.push.push(push);
                blocks.pull.push(pull);
            }
        }
        blocks
    }

    /// A slot's pull block at its own keys and its push block at `next`, both carrying `limbs`, made by `block`: an
    /// owned table's own, the public table's the framework's.
    fn add_pair(
        &mut self,
        keys: Coord,
        next: PublicColumn,
        limbs: Vec<Coord>,
        block: impl Fn(usize, Vec<Coord>) -> Block,
        tau: usize,
    ) {
        let coords = |key: Coord, limbs: Vec<Coord>| std::iter::once(key).chain(limbs).collect();
        self.pull.push(block(tau, coords(keys, limbs.clone())));
        self.push.push(block(tau, coords(Coord::Public(next), limbs)));
    }

    /// Prove the bus balances over the global columns.
    pub(crate) fn prove(&self, cols: &[&[F64]], ps: &mut ProverState) -> BusProof {
        bus::prove_balance(&self.push, &self.pull, &[], 0, cols, &self.tables, ps)
    }

    /// Verify the bus balances.
    ///
    /// # Errors
    ///
    /// Returns the first check of the balance that refuses.
    pub(crate) fn verify<V: Verifier + PublicColumns>(&self, v: &mut V) -> Result<BusVerify<V::E>, BusError> {
        let bus = bus::verify_balance(v, &self.push, &self.pull, &[], 0, &self.tables)?;
        debug_assert!(
            bus.sparse.iter().all(Vec::is_empty) && bus.producers.is_empty(),
            "the machine's target has no share for sparse columns or producers"
        );
        Ok(bus)
    }
}

impl TableSummand {
    /// Each present owned table's summand, in the order of `tables`, the bus's.
    ///
    /// Its push and pull forms weigh `1` and `xi`, then each identity has a power of `xi` of its own from `xi^2`.
    /// The tables' ranges of powers are disjoint.
    pub(crate) fn batch(tables: &[Table], forms: &[Vec<BusForm>; 2], xi: F192) -> Vec<Self> {
        let ids: Vec<Vec<BusForm>> = tables.iter().map(|t| t.identities()).collect();
        let offsets = constraints::xi_offsets(ids.iter().map(Vec::len));
        (ids.into_iter().zip(offsets).enumerate())
            .map(|(t, (ids, offset))| {
                let mut power = (0..offset).fold(xi * xi, |p, _| p * xi);
                let mut parts = vec![forms[0][t].clone(), forms[1][t].scaled(xi)];
                for id in ids {
                    parts.push(id.scaled(power));
                    power *= xi;
                }
                Self(PackedForm::new(BusForm::sum(parts)))
            })
            .collect()
    }
}

impl<'a, E: Copy> TableResidual<'a, E> {
    /// Each present owned table's residual, in the order of `tables`, its powers of `xi` those of the prover's batch.
    pub(crate) fn batch<A: Arith<E = E>>(
        a: &mut A,
        tables: &[Table],
        forms: &'a [Vec<BusForm<E>>; 2],
        xi: E,
    ) -> Vec<Self> {
        let ids: Vec<Vec<BusForm>> = tables.iter().map(|t| t.identities()).collect();
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
    fn eval<V: Subfield>(&self, cols: &[V], quadratic: bool) -> F192 {
        self.0.eval_unreduced(cols, quadratic).reduce()
    }
}
