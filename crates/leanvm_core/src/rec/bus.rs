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
use crate::bus::{Block, BusError, BusForm, BusProof, BusVerify, Coord, PackedForm, PublicColumn, PublicColumns};
use crate::constraints::{Residual, Summand};
use crate::{bus, constraints};
use fiat_shamir::ProverState;
use fiat_shamir::arith::{Arith, Verifier};
use primitives::field::{F64, F192, Subfield};

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
    pub(crate) fn new(fixed: &FixedColumns, public: [PublicColumn; 4], layout: &RecLayout) -> Self {
        let mut blocks = Self {
            push: Vec::new(),
            pull: Vec::new(),
        };
        let next = |table: Table, slot: usize| fixed.public(FixedColumn::Next(table.first_slot() + slot));
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
    fn add_pair(&mut self, table: Table, slot: usize, tau: usize, next: PublicColumn, limbs: Vec<Coord>) {
        let block = |key: Coord, limbs: Vec<Coord>| {
            let coords = std::iter::once(key).chain(limbs).collect();
            match table {
                Table::Pub => Block::framework(tau, coords),
                owned => Block::table(owned as usize, tau, coords),
            }
        };
        self.pull
            .push(block(SlotKey::new(table, slot, 0).column(), limbs.clone()));
        self.push.push(block(Coord::Public(next), limbs));
    }

    /// Prove the bus balances over the global columns.
    pub(crate) fn prove(&self, cols: &[&[F64]], ps: &mut ProverState) -> BusProof {
        bus::prove_balance(&self.push, &self.pull, &[], 0, cols, &RecLayout::TABLE_COLUMNS, ps)
    }

    /// Verify the bus balances.
    ///
    /// # Errors
    ///
    /// Returns the first check of the balance that refuses.
    pub(crate) fn verify<V: Verifier + PublicColumns>(&self, v: &mut V) -> Result<BusVerify<V::E>, BusError> {
        let bus = bus::verify_balance(v, &self.push, &self.pull, &[], 0, &RecLayout::TABLE_COLUMNS)?;
        debug_assert!(
            bus.sparse.iter().all(Vec::is_empty) && bus.producers.is_empty(),
            "the machine's target has no share for sparse columns or producers"
        );
        Ok(bus)
    }

    /// The blocks as `Builder::mark` lines, for `checkbind`'s side certificate (`Bind.SideCert`): per side (push, then
    /// pull) a line `bus side s mu n`, then a line `bus block kappa offset owner coords...` per block, at the offsets
    /// `bus::verify_balance` lays it at (`bus::layout`) and `owner` `-` or `table:base`, its columns' base.
    pub(crate) fn mark_lines(&self) -> String {
        let lays = [bus::layout(&self.push, &[]), bus::layout(&self.pull, &[])];
        let mu = lays[0].mu.max(lays[1].mu);
        let mut lines = Vec::new();
        for (s, (blocks, lay)) in [&self.push, &self.pull].into_iter().zip(&lays).enumerate() {
            lines.push(format!("bus side {s} {mu} {}", blocks.len()));
            for (block, offset) in blocks.iter().zip(&lay.offsets) {
                let owner = block
                    .owner
                    .map_or_else(|| "-".into(), |t| format!("{t}:{}", RecLayout::TABLE_COLUMNS[t].0));
                let coords: Vec<String> = block.coords.iter().map(coord_word).collect();
                lines.push(format!(
                    "bus block {} {offset} {owner} {}",
                    block.kappa,
                    coords.join(" ")
                ));
            }
        }
        lines.join("\n")
    }
}

/// A coordinate as one word of a `bus block` mark: `k` a constant, `c` a column, `x` a product, `s` a scaled column,
/// `i` an index column (`base.shift`), `pn`/`pc` a fixed `Next`/`Constant` public column (`p` another), `y` a sparse
/// one, a sum its terms joined by `+` (`e` if it has none).
fn coord_word(c: &Coord) -> String {
    match c {
        Coord::Const(v) => format!("k{}", v.0),
        Coord::Col(i) => format!("c{i}"),
        Coord::Prod(i, j) => format!("x{i}.{j}"),
        Coord::Scaled(v, i) => format!("s{}.{i}", v.0),
        Coord::IntIndex { base, shift } => format!("i{}.{shift}", base.0),
        Coord::Public(p) => match p.fixed {
            Some(FixedColumn::Next(s)) => format!("pn{s}"),
            Some(FixedColumn::Constant(j)) => format!("pc{j}"),
            None => "p".into(),
        },
        Coord::Sparse(_) => "y".into(),
        Coord::Sum(cs) if cs.is_empty() => "e".into(),
        Coord::Sum(cs) => cs.iter().map(coord_word).collect::<Vec<_>>().join("+"),
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
                Self(PackedForm::new(BusForm::sum(parts)))
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
    fn eval<V: Subfield>(&self, cols: &[V], quadratic: bool) -> F192 {
        self.0.eval_unreduced(cols, quadratic).reduce()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::rec::circuit::{Builder, Finished, Kw};

    // The plan the Lean copy argument assumes (`Rec.Balanced`, `Rec.bus_copy_sound`): every slot, the public table's
    // first, pulls its own key and pushes its `next` key, both blocks carrying the same limbs at the same height.
    #[test]
    fn every_slot_pulls_its_key_and_pushes_its_next_with_its_limbs() {
        let mut b = Builder::new();
        let x = b.free_e(F192::new(3, 5, 7));
        let y = b.e_const(F192::new(11, 13, 17));
        let one = b.one();
        let p = b.mul_add(x, y, one);
        let w: [Kw; 4] = std::array::from_fn(|i| b.free_k(10 + i as u64));
        let d = b.k_to_d(w);
        b.expose(p);
        b.expose(d);
        let Finished {
            circuit, assignment, ..
        } = b.finish();
        let layout = RecLayout::new(&circuit).unwrap();
        let fixed = FixedColumns::new(&circuit);
        let blocks = BusBlocks::new(&fixed, fixed.public_values(&assignment.statement), &layout);

        let slots: Vec<(Table, usize)> = std::iter::once((Table::Pub, 0))
            .chain(
                Table::OWNED
                    .into_iter()
                    .flat_map(|t| (0..t.n_slots()).map(move |s| (t, s))),
            )
            .collect();
        assert_eq!(blocks.pull.len(), slots.len());
        assert_eq!(blocks.push.len(), slots.len());
        let show = |c: &[Coord]| format!("{c:?}");
        for ((pull, push), &(table, slot)) in blocks.pull.iter().zip(&blocks.push).zip(&slots) {
            assert_eq!((pull.kappa, pull.owner), (push.kappa, push.owner));
            assert_eq!(show(&pull.coords[1..]), show(&push.coords[1..]));
            assert_eq!(show(&pull.coords[..1]), show(&[SlotKey::new(table, slot, 0).column()]));
            let next = fixed.public(FixedColumn::Next(table.first_slot() + slot));
            assert_eq!(show(&push.coords[..1]), show(&[Coord::Public(next)]));
        }
    }
}
