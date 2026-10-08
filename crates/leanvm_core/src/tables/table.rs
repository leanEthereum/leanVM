//! One instruction table's circuit bindings and bus interactions.

use super::bus::{FlushBuilder, Separator};
use super::columns::Columns;
use super::{BAD_SLOT, EXIT_SLOT, Part, PerTable, TableId, Word};
use crate::constraints::{BitColumns, BitField};
use crate::leaf::BusForm;
use crate::leaf::Coord::{self, Col, Const, Scaled};
use crate::rv::{ExtReg, Reg, RegisterFile};
use primitives::field::{F64, F192, g_pow};
use std::sync::OnceLock;

/// Circuit bindings and bus interactions for one instruction class.
///
/// Column indices are local to this table, including its virtual circuit columns.
pub struct ClassTable {
    /// The table.
    pub(super) id: TableId,

    /// Local column layout, including aliases for unchanged memory values.
    pub(super) cols: Columns,

    /// Class circuit ports in input-then-output order.
    class_ports: Vec<Word>,

    /// Clock circuit ports in input-then-output order.
    clock_ports: Vec<Word>,
}

impl ClassTable {
    /// All instruction tables, built once in protocol order.
    pub fn all() -> &'static PerTable<Self> {
        static TABLES: OnceLock<PerTable<ClassTable>> = OnceLock::new();
        TABLES.get_or_init(|| PerTable::from_fn(Self::new))
    }

    /// Build the columns and ports of a validated class specification.
    fn new(id: TableId) -> Self {
        let spec = id.spec();
        spec.assert_valid();
        let cols = Columns::new(spec);
        let table = Self {
            id,
            cols,
            class_ports: spec.ports().collect(),
            clock_ports: spec.clock_ports(),
        };
        table.assert_x0_is_constant();
        table.assert_linear_if_circuit();
        table
    }

    /// Asserts that no access of the table can change register cell 0, `x0`.
    ///
    /// - A read pushes back the value it pulls.
    /// - A register access that changes its cell does so at the entry's destination, which the decoder keeps in `1..=32`.
    ///
    /// So `x0` keeps its zero seed, and an extension register holding a constant keeps it: the decoder never names
    /// one as a destination.
    ///
    /// # Panics
    ///
    /// Panics if an access that may reach the registers changes its cell elsewhere than at the entry's destination.
    fn assert_x0_is_constant(&self) {
        let bus = self.flushes();
        let destination = &bus.pull[1][Self::DESTINATION_SLOT];
        // Pushes are the state, then the accesses; pulls are the state, the bytecode, then the accesses.
        for (push, pull) in bus.push[1..].iter().zip(&bus.pull[2..]) {
            let memory = matches!(push[0], Const(sep) if sep == Separator::Memory.value());
            let read =
                (pull[3..].iter().zip(&push[3..])).all(|pair| matches!(pair, (Col(old), Col(new)) if old == new));
            let at_destination = matches!((&push[1], destination), (Col(at), Col(ad)) if at == ad);
            assert!(
                memory || read || at_destination,
                "{} writes a register other than its destination",
                self.id.spec().name
            );
        }
    }

    /// The register numbers a row reads off its entry: `a1`, then `a2` and `ad` where the row has them.
    ///
    /// - They are bit columns, packed into a committed word with the other tables' of the same height.
    /// - A register read is below 32, five bits; a cell written may be the sink, 32, six bits.
    /// - An extension register is below 128, seven bits.
    pub(crate) fn register_bits(&self) -> BitColumns {
        let c = &self.cols;
        // An element's move names an integer register, its base, then an extension register.
        let (first, read, written) = match (c.ext, c.element) {
            (Some(_), _) => (ExtReg::BITS, ExtReg::BITS, ExtReg::BITS),
            (_, Some(_)) => (Reg::BITS, ExtReg::BITS, ExtReg::BITS),
            _ => (Reg::BITS, Reg::BITS, RegisterFile::LOG_CELLS),
        };
        let field = |col, width| BitField { col, width };
        BitColumns {
            fields: [
                Some(field(c.a1, first)),
                c.rs2.map(|r| field(r.a2, read)),
                // A compression reads the register its destination names.
                (c.rd.map(|rd| field(rd.ad, written))).or_else(|| c.block.map(|b| field(b.ad, Reg::BITS))),
            ]
            .into_iter()
            .flatten()
            .collect(),
        }
    }

    /// Whether the bus point settles the table: a table with a class circuit flushes only linear tuples.
    pub(crate) const fn settled_at_bus(&self) -> bool {
        self.id.spec().has_circuit()
    }

    /// The columns the table sumcheck folds, in order: all of them, or only the register numbers of a settled table.
    ///
    /// Why: a settled table's other columns are sent at the bus point, but its register numbers are read through their
    /// word's bits, which share the table sumcheck's point with the other words.
    pub(crate) fn summed_columns(&self) -> Vec<usize> {
        if self.settled_at_bus() {
            self.register_bits().fields.iter().map(|f| f.col).collect()
        } else {
            (0..self.n_committed_columns()).collect()
        }
    }

    /// The register numbers among the summed columns, each at its place among them.
    pub(crate) fn summed_bits(&self) -> BitColumns {
        let cols = self.summed_columns();
        let at = |col| {
            cols.iter()
                .position(|&c| c == col)
                .expect("a register number is summed")
        };
        BitColumns {
            fields: (self.register_bits().fields.into_iter())
                .map(|f| BitField { col: at(f.col), ..f })
                .collect(),
        }
    }

    /// A bus form of the table as the table sumcheck folds it, over the summed columns.
    ///
    /// A settled table's is the form's part on its register numbers: the bus point settles the rest.
    pub(crate) fn summed_form<E: Copy>(&self, form: &BusForm<E>, zero: E) -> BusForm<E> {
        if self.settled_at_bus() {
            form.on(&self.summed_columns(), zero)
        } else {
            form.clone()
        }
    }

    /// Asserts that a table with a class circuit puts no product of columns on the bus.
    ///
    /// Such a table is settled at the bus's point, where only a linear form factors through its columns.
    ///
    /// # Panics
    ///
    /// Panics on a product in a table with a class circuit.
    fn assert_linear_if_circuit(&self) {
        let bus = self.flushes();
        let linear = bus.push.iter().chain(&bus.pull).flatten().all(Coord::is_linear);
        assert!(
            !self.id.spec().has_circuit() || linear,
            "{}: a product on the bus",
            self.id.spec().name
        );
    }

    /// Number of columns, the virtual ones included.
    pub const fn n_committed_columns(&self) -> usize {
        self.cols.len()
    }

    /// The port words of one of the table's circuits.
    pub fn ports(&self, part: Part) -> &[Word] {
        match part {
            Part::Class => &self.class_ports,
            Part::Clock => &self.clock_ports,
        }
    }

    /// One circuit's words that are columns, as `(port, local column)`.
    pub(crate) fn word_columns(&self, part: Part) -> impl Iterator<Item = (usize, usize)> + '_ {
        self.ports(part)
            .iter()
            .enumerate()
            .filter_map(|(port, &w)| Some((port, self.cols.column(w)?)))
    }

    /// Build the state transition, bytecode lookup, and ordered memory accesses.
    pub(crate) fn flushes(&self) -> FlushBuilder {
        let mut bus = FlushBuilder::new();
        self.flush_state(&mut bus);
        bus.read(self.bytecode_tuple());
        self.flush_accesses(&mut bus);
        bus
    }

    /// Bind the next instruction and clock to the current state.
    ///
    /// The successor is linear in the row's columns: `pc + 4`, plus the circuit's jump for a class with control flow.
    fn flush_state(&self, bus: &mut FlushBuilder) {
        let c = &self.cols;
        let npc = c.control.map_or(Col(c.pc4), |control| control.next_pc(c.pc4));
        let exit = c.control.map_or(Const(F64::ZERO), |control| Col(control.exit));
        bus.state(c.pc, c.ts, c.step, npc, exit);
    }

    /// The bytecode tuple's coordinate holding the cell the entry writes.
    pub(crate) const DESTINATION_SLOT: usize = 6;

    /// Read the public decoded entry, using constants for absent register and circuit ports.
    fn bytecode_tuple(&self) -> Vec<Coord> {
        let c = &self.cols;
        // A row without flags, an `rs2` read, an `rd` write or an immediate reads its constant off the entry.
        // Those constants are zero, `x0`, the sink, and zero.
        //
        // An extension-field product's three selectors are the entry's flags, immediate and offset slots.
        let selector = |k: usize| c.ext.map(|x| Col(x.flags + k));
        let mut entry = vec![
            Separator::Bytecode.coordinate(),
            Col(c.pc),
            Const(g_pow(self.id.index())),
            (c.flags.map(Col).or_else(|| selector(0))).unwrap_or(Const(F64::ZERO)),
            Col(c.a1),
            c.rs2.map_or(Const(F64::ZERO), |r| Col(r.a2)),
            (c.rd.map(|rd| Col(rd.ad)).or_else(|| c.block.map(|b| Col(b.ad))))
                .unwrap_or(Const(F64(RegisterFile::SINK as u64))),
            (c.imm
                .map(Col)
                .or_else(|| selector(1))
                .or_else(|| c.block.map(|b| Col(b.a3))))
            .unwrap_or(Const(F64::ZERO)),
            Col(c.pc4),
        ];
        if let Some(dt) = c.control.map(|control| Col(control.dt)).or_else(|| selector(2)) {
            entry.push(dt);
        }
        if let Some(bad) = c.bad {
            entry.resize(BAD_SLOT, Const(F64::ZERO));
            entry.push(Col(bad));
        }
        entry.resize(EXIT_SLOT, Const(F64::ZERO));
        entry.push(c.control.map_or(Const(F64::ZERO), |k| Col(k.exit)));
        entry
    }

    /// Bind register, cell, block, and limb values to their ordered memory accesses.
    fn flush_accesses(&self, bus: &mut FlushBuilder) {
        let c = &self.cols;
        // The accesses' columns are in the order the row makes them.
        let mut accesses = bus.accesses(c.ts, c.prev, self.id.spec().slots());
        if let (Some(x), Some(r), Some(rd)) = (c.ext, c.rs2, c.rd) {
            // Each access is one extension register, three limbs.
            //
            // A base-field `b` is an integer register, under a separator that is a form in the selector `base`:
            //
            //     separator   extension + base·(extension + integer)
            let (ext, int) = (Separator::ExtRegisters.value(), Separator::Registers.value());
            let second = Coord::Sum(vec![Const(ext), Scaled(ext + int, x.flags + 1)]);
            accesses.write_wide(Const(ext), Col(c.a1), x.operand(0), x.operand(0));
            accesses.write_wide(second, Col(r.a2), x.operand(1), x.operand(1));
            accesses.write_wide(Const(ext), Col(rd.ad), x.operand(2), x.result());
            accesses.finish();
            return;
        }
        accesses.read(Separator::Registers.coordinate(), Col(c.a1), Col(c.v1));
        if let Some(e) = c.element {
            // The extension register, read by a store and rewritten by a load, then the element's three words at
            // `address ^ 8k`, which is `address + 8k` in the field: read by a load, rewritten by a store.
            let ext = Separator::ExtRegisters.coordinate();
            let limbs: [Coord; 3] = std::array::from_fn(|k| Col(e.limbs + k));
            let old: [Coord; 3] = std::array::from_fn(|k| Col(e.old + k));
            let (register, words) = match (c.rs2, c.rd) {
                (Some(r), _) => ((Col(r.a2), limbs.clone()), old),
                (_, Some(rd)) => ((Col(rd.ad), old), limbs.clone()),
                _ => unreachable!("an element's move names an extension register"),
            };
            accesses.write_wide(ext, register.0, register.1, limbs.clone());
            for (k, word) in words.into_iter().enumerate() {
                let addr = Coord::Sum(vec![Col(e.address), Const(F64(8 * k as u64))]);
                accesses.write(Separator::Memory.coordinate(), addr, word, limbs[k].clone());
            }
            accesses.finish();
            return;
        }
        if let Some(r) = c.rs2 {
            accesses.read(Separator::Registers.coordinate(), Col(r.a2), Col(r.v2));
        }
        // The destination receives the circuit's output, which is the link of a jump that links.
        if let Some(rd) = c.rd {
            accesses.write(
                Separator::Registers.coordinate(),
                Col(rd.ad),
                Col(rd.vd_old),
                Col(rd.out),
            );
        }
        // Misaligned or unmapped addresses name no seeded cell.
        // Doubleword moves share their value column on the read and write sides.
        if let Some(ram) = c.ram {
            accesses.write(
                Separator::Memory.coordinate(),
                Col(ram.address),
                Col(ram.cell),
                Col(ram.new),
            );
        }
        // A compression: its third and fourth registers, read, then its words, word `k` of each at its pointer
        // `^ 8k`, which is the pointer `+ 8k` in the field: the chaining value at `v1`, the message at `v2`, both
        // read, and the result at `vd`, rewritten.
        if let (Some(block), Some(r)) = (c.block, c.rs2) {
            accesses.read(Separator::Registers.coordinate(), Col(block.a3), Col(block.v3));
            accesses.read(Separator::Registers.coordinate(), Col(block.ad), Col(block.vd));
            let at = |pointer: usize, k: usize| Coord::Sum(vec![Col(pointer), Const(F64(8 * k as u64))]);
            let memory = Separator::Memory.coordinate();
            for k in 0..12 {
                let addr = if k < 4 { at(c.v1, k) } else { at(r.v2, k - 4) };
                accesses.read(memory.clone(), addr, Col(block.words + k));
            }
            for k in 0..4 {
                accesses.write(memory.clone(), at(block.vd, k), Col(block.old + k), Col(block.out + k));
            }
        }
        accesses.finish();
    }

    /// The identities the table proves of every one of its rows, in local column indices: none for a class with a
    /// circuit, and for the extension-field product its three new limbs and what its selectors require.
    ///
    /// With `d_m = sum_{i + j = m} a_i b_j`, the product's coefficient of `y^m` (products in `K`), the reduction
    /// `y^3 = y + 1`, `y^4 = y^2 + y` has coefficients in `GF(2)`, so each new limb is a sum of `K` products:
    ///
    /// ```text
    ///     c'_0 = accumulate·c_0 + d_0 + d_3          d_3 = a_1 b_2 + a_2 b_1
    ///     c'_1 = accumulate·c_1 + d_1 + d_3 + d_4    d_4 = a_2 b_2
    ///     c'_2 = accumulate·c_2 + d_2 + d_4
    /// ```
    ///
    /// Each form is the difference of the two sides, which vanishes on a row exactly when the row's new limb is its
    /// product: degree 2, every coefficient one. Then:
    ///
    /// ```text
    ///     base·b_1 = base·b_2 = 0      a base-field operand is one word
    ///     zero·c'_i = 0                a checked product is zero
    /// ```
    pub(crate) fn identities(&self) -> Vec<BusForm> {
        let Some(x) = self.cols.ext else {
            return Vec::new();
        };
        let (a, b, old) = (x.limbs, x.limbs + 3, x.limbs + 6);
        let (accumulate, base, zero) = (x.flags, x.flags + 1, x.flags + 2);
        let product = |i: usize, j: usize| {
            let mut form = BusForm::new(self.n_committed_columns(), F192::ZERO);
            form.prods.push((i, j, F192::ONE));
            form
        };
        let limbs = (0..3).map(|i| {
            let mut form = product(accumulate, old + i);
            form.coeffs[x.new + i] = F192::ONE;
            for (j, k) in (0..3).flat_map(|j| (0..3).map(move |k| (j, k))) {
                let lands = match j + k {
                    3 => i < 2,
                    4 => i > 0,
                    m => m == i,
                };
                if lands {
                    form.prods.push((a + j, b + k, F192::ONE));
                }
            }
            form
        });
        let word = (1..3).map(|i| product(base, b + i));
        let checked = (0..3).map(|i| product(zero, x.new + i));
        limbs.chain(word).chain(checked).collect()
    }
}

#[cfg(test)]
mod tests {
    use super::super::Clock;
    use super::*;
    use crate::colval::ColVal;
    use crate::rv::Ext;

    fn check_columns(coordinate: &Coord, width: usize) {
        // Every table-side coordinate must use its own local span of columns.
        match coordinate {
            Col(index) => assert!(*index < width),
            Coord::Prod(a, b) => assert!(*a < width && *b < width),
            Scaled(_, index) => assert!(*index < width),
            Coord::Sum(terms) => terms.iter().for_each(|term| check_columns(term, width)),
            Const(_) => {}
            _ => panic!("a table tuple contains a nonlocal coordinate"),
        }
    }

    #[test]
    fn every_table_binds_its_ports_and_accesses_within_its_local_columns() {
        for (_, table) in ClassTable::all().iter() {
            let width = table.n_committed_columns();
            let accesses = table.id.spec().n_accesses();
            let slots = table.id.spec().slots();
            assert_eq!(slots.len(), accesses);
            assert!(slots.iter().all(|&slot| slot < 1 << Clock::SLOT_BITS));
            for part in [Part::Class, Part::Clock] {
                for (_, column) in table.word_columns(part) {
                    assert!(column < width);
                }
            }
            // A row pulls state and bytecode, then pulls and pushes one tuple per access.
            let bus = table.flushes();
            assert_eq!(bus.push.len(), 1 + accesses);
            assert_eq!(bus.pull.len(), 2 + accesses);
            assert_eq!(bus.pull[1].len(), EXIT_SLOT + 1);
            for tuple in bus.push.iter().chain(&bus.pull) {
                for coordinate in tuple {
                    check_columns(coordinate, width);
                }
            }
        }
    }

    proptest::proptest! {
        #[test]
        fn the_identities_are_the_extension_product(
            limbs in proptest::array::uniform9(proptest::prelude::any::<u64>()),
            flags in proptest::sample::select(Ext::LEGAL),
            wrong in 0usize..3,
            bit in 0u32..64,
        ) {
            // Invariant: on a row, the identities vanish exactly when the new limbs are the reference's, a base-field
            // operand is one word, and a checked product is zero.
            let table = TableId::EXT.class_table();
            let x = table.cols.ext.unwrap();
            let [a, mut b, c]: [[u64; 3]; 3] = std::array::from_fn(|i| std::array::from_fn(|k| limbs[3 * i + k]));
            if flags & Ext::BASE != 0 {
                (b[1], b[2]) = (0, 0);
            }
            let new = Ext { flags, a, b, c }.eval();
            let mut row = vec![F64::ZERO; table.n_committed_columns()];
            for (i, limb) in a.into_iter().chain(b).chain(c).enumerate() {
                row[x.limbs + i] = F64(limb);
            }
            row[x.new..x.new + 3].copy_from_slice(&new.map(F64));
            for k in 0..3 {
                row[x.flags + k] = F64(flags >> k & 1);
            }
            let values = |row: &[F64]| table.identities().iter().map(|form| <F64 as ColVal>::reduce(form.eval_unreduced(row, false))).collect::<Vec<_>>();

            // The product's limbs and the operand's width hold; a checked form holds exactly on a zero result.
            let honest = values(&row);
            proptest::prop_assert_eq!(&honest[..5], &[F192::ZERO; 5]);
            for i in 0..3 {
                proptest::prop_assert_eq!(honest[5 + i] == F192::ZERO, flags & Ext::ZERO == 0 || new[i] == 0);
            }

            // Mutation: one bit of one new limb, which only that limb's identity and its check read.
            row[x.new + wrong].0 ^= 1 << bit;
            for (i, value) in values(&row)[..3].iter().enumerate() {
                proptest::prop_assert_eq!(*value == F192::ZERO, i != wrong);
            }
            row[x.new + wrong].0 ^= 1 << bit;

            // Mutation: a base-field operand with a high limb.
            row[x.limbs + 4] = F64(1 << bit);
            proptest::prop_assert_eq!(values(&row)[3] == F192::ZERO, flags & Ext::BASE == 0);
        }
    }
}
