//! One instruction table's circuit bindings and bus interactions.

use super::bus::{FlushBuilder, Separator};
use super::columns::Columns;
use super::spec::Ram;
use super::{BAD_SLOT, EXIT_SLOT, Part, PerTable, TableId, Word};
use crate::constraints::{BitColumns, BitField};
use crate::cpu::{Payload, RowRef};
use crate::leaf::BusForm;
use crate::leaf::Coord::{self, Col, Const, Scaled, Sum};
use crate::rv::{Ext, Hash, Reg, RegisterFile, RiscvProgram};
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

    /// Operand circuit ports in input-then-output order.
    operand_ports: Vec<Word>,
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
            operand_ports: spec.operand_ports().collect(),
        };
        table.assert_linear_if_circuit();
        table
    }

    /// The register numbers a row reads off its entry: `a1`, then `a2` and `ad` where the row has them.
    ///
    /// - They are bit columns, packed into a committed word with the other tables' of the same height.
    /// - A register read is below 32, five bits; a cell written may be the sink, 32, six bits.
    pub(crate) fn register_bits(&self) -> BitColumns {
        let c = &self.cols;
        let read = |col| BitField { col, width: Reg::BITS };
        let written = |col| BitField {
            col,
            width: RegisterFile::LOG_CELLS,
        };
        let ad = (c.rd.map(|rd| written(rd.ad))).or_else(|| c.pointer.map(|p| read(p.ad)));
        BitColumns {
            fields: [Some(read(c.a1)), c.rs2.map(|r| read(r.a2)), ad]
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
            Part::Operands => &self.operand_ports,
        }
    }

    /// One circuit's words that are columns, as `(port, local column)`.
    pub(crate) fn word_columns(&self, part: Part) -> impl Iterator<Item = (usize, usize)> + '_ {
        self.ports(part)
            .iter()
            .enumerate()
            .filter_map(|(port, &w)| Some((port, self.cols.column(w)?)))
    }

    /// Build the state transition, the bytecode lookup, and the pulls of the logs' accesses.
    pub(crate) fn flushes(&self) -> FlushBuilder {
        let mut bus = FlushBuilder::new();
        self.flush_state(&mut bus);
        bus.pull(self.bytecode_tuple());
        bus.pull(self.register_cycle());
        self.flush_memory(&mut bus);
        bus
    }

    /// Bind the next instruction, the next cycle and the next memory position to the current state.
    ///
    /// The successor is linear in the row's columns: `pc + 4`, plus the circuit's jump for a class with control flow.
    fn flush_state(&self, bus: &mut FlushBuilder) {
        let c = &self.cols;
        let npc = c.control.map_or(Col(c.pc4), |control| control.next_pc(c.pc4));
        let exit = c.control.map_or(Const(F64::ZERO), |control| Col(control.exit));
        bus.state(
            c.pc,
            c.time,
            c.position,
            npc,
            self.access_position(self.id.spec().ram.accesses()),
            exit,
        );
    }

    /// The memory position of the row's access `k`, or for `k` its accesses past the last.
    ///
    /// A base-field extension operand's two high limbs are no access, so the accesses after them move back two.
    fn access_position(&self, k: usize) -> Coord {
        let c = &self.cols;
        let scaled = |k: usize, col: usize| if k == 0 { Col(col) } else { Scaled(g_pow(k), col) };
        match (self.id.spec().ram, c.limbs) {
            (Ram::Limbs, Some(limbs)) => match k {
                0..=3 => scaled(k, c.position),
                4 | 5 => Sum(vec![scaled(k, c.position), scaled(k, limbs.base_position)]),
                _ => Sum(vec![
                    scaled(k, c.position),
                    Scaled(g_pow(k - 2) + g_pow(k), limbs.base_position),
                ]),
            },
            _ => scaled(k, c.position),
        }
    }

    /// The register log's cycle the row is: its register numbers around its position, the values read, then the value
    /// written.
    ///
    /// A row without an `rs2` read reads `x0`, one without a write writes zero to the sink, and a row reading an
    /// address in `rd` is under the pointer separator, which forbids its write.
    fn register_cycle(&self) -> Vec<Coord> {
        let c = &self.cols;
        let separator = if c.pointer.is_some() {
            Separator::Pointer
        } else {
            Separator::Registers
        };
        let (ad, written) = match (c.rd, c.pointer) {
            (Some(rd), _) => (Col(rd.ad), Col(rd.out)),
            (_, Some(p)) => (Col(p.ad), Col(p.vd)),
            _ => (Const(F64(RegisterFile::SINK as u64)), Const(F64::ZERO)),
        };
        vec![
            separator.coordinate(),
            Col(c.a1),
            Col(c.time),
            c.rs2.map_or(Const(F64::ZERO), |r| Col(r.a2)),
            ad,
            Col(c.v1),
            c.rs2.map_or(Const(F64::ZERO), |r| Col(r.v2)),
            written,
        ]
    }

    /// Pull each of the row's memory accesses at its position: the address, the cell before, then after.
    ///
    /// Misaligned or unmapped addresses name no cell of the log.
    fn flush_memory(&self, bus: &mut FlushBuilder) {
        let c = &self.cols;
        let mut access = |k: usize, address: Coord, old: usize, new: usize| {
            bus.pull(vec![
                Separator::Memory.coordinate(),
                address,
                self.access_position(k),
                Col(old),
                Col(new),
            ]);
        };
        if let Some(ram) = c.ram {
            access(0, Col(ram.address), ram.cell, ram.new);
        }
        // The hash's block: word `k` at `v1 ^ 8k`, which is `v1 + 8k` in the field.
        if let Some(block) = c.block {
            for k in 0..Hash::WORDS {
                let address = Sum(vec![Col(c.v1), Const(F64(8 * k as u64))]);
                access(k, address, block.words + k, block.left(k));
            }
        }
        // The limbs: each operand's first at its pointer, the others at the addresses the operand circuit computes.
        if let (Some(limbs), Some(r), Some(p)) = (c.limbs, c.rs2, c.pointer) {
            let pointers = [c.v1, r.v2, p.vd];
            for k in 0..Ext::LIMBS {
                access(k, Col(limbs.address(k, pointers)), limbs.limbs + k, limbs.left(k));
            }
        }
    }

    /// Read the public decoded entry, using constants for absent register and circuit ports.
    fn bytecode_tuple(&self) -> Vec<Coord> {
        let c = &self.cols;
        // A row without flags, an `rs2` read, an `rd` write or an immediate reads its constant off the entry.
        // Those constants are zero, `x0`, the sink, and zero.
        let mut entry = vec![
            Separator::Bytecode.coordinate(),
            Col(c.pc),
            Const(g_pow(self.id.index())),
            c.flags.map_or(Const(F64::ZERO), Col),
            Col(c.a1),
            c.rs2.map_or(Const(F64::ZERO), |r| Col(r.a2)),
            match (c.rd, c.pointer) {
                (Some(rd), _) => Col(rd.ad),
                (_, Some(pointer)) => Col(pointer.ad),
                _ => Const(F64(RegisterFile::SINK as u64)),
            },
            c.imm.map_or(Const(F64::ZERO), Col),
            Col(c.pc4),
        ];
        if let Some(control) = c.control {
            entry.push(Col(control.dt));
        }
        if let Some(bad) = c.bad {
            entry.resize(BAD_SLOT, Const(F64::ZERO));
            entry.push(Col(bad));
        }
        entry.resize(EXIT_SLOT, Const(F64::ZERO));
        entry.push(c.control.map_or(Const(F64::ZERO), |k| Col(k.exit)));
        entry
    }

    /// Every local column of one row: what the table's fill writes for it.
    pub(crate) fn row_columns(&self, p: &RiscvProgram, r: RowRef<'_>) -> Vec<F64> {
        let (c, row) = (&self.cols, r.row);
        let at = p.fetch(row.index as usize);
        let (e, pc) = (at.entry, p.pc_of(row.index as usize));
        let mut out = vec![F64::ZERO; self.n_committed_columns()];
        for (col, value) in [
            (c.pc, pc),
            (c.time, row.time),
            (c.position, row.position),
            (c.a1, e.a1 as u64),
            (c.pc4, pc.wrapping_add(4)),
            (c.v1, row.v1),
        ] {
            out[col] = F64(value);
        }
        let mut set = |col: usize, word: Word| out[col] = F64(word.value(r, at));
        if let Some(flags) = c.flags {
            set(flags, Word::Flags);
        }
        if let Some(rs2) = c.rs2 {
            set(rs2.v2, Word::V2);
        }
        if let Some(rd) = c.rd {
            set(rd.out, Word::Out);
        }
        if let Some(pointer) = c.pointer {
            set(pointer.vd, Word::Dest);
        }
        if let Some(k) = c.control {
            set(k.dt, Word::Dt);
            set(k.jump, Word::Jump);
        }
        if let Some(imm) = c.imm {
            set(imm, Word::Imm);
        }
        if let Some(ram) = c.ram {
            set(ram.address, Word::Address);
            set(ram.cell, Word::Cell(0));
            set(ram.new, Word::CellNew(0));
        }
        if let Some(block) = c.block {
            for k in 0..Hash::WORDS {
                set(block.words + k, Word::Cell(k as u8));
                set(block.left(k), Word::CellNew(k as u8));
            }
        }
        if let Some(bits) = c.flag_bits {
            set(bits, Word::FlagBit(0));
            set(bits + 1, Word::FlagBit(1));
        }
        if let Some(limbs) = c.limbs {
            for (i, &k) in Ext::OFFSET_LIMBS.iter().enumerate() {
                set(limbs.addresses + i, Word::LimbAddress(k as u8));
            }
        }
        for (col, number) in [
            (c.rs2.map(|r| r.a2), e.a2),
            (c.rd.map(|rd| rd.ad), e.ad),
            (c.pointer.map(|p| p.ad), e.ad),
        ] {
            if let Some(col) = col {
                out[col] = F64(u64::from(number));
            }
        }
        if let Some(k) = c.control {
            out[k.exit] = F64(u64::from(e.is_exit()));
        }
        if let (Some(limbs), Payload::Ext(ext)) = (c.limbs, r.payload) {
            for k in 0..Ext::LIMBS {
                out[limbs.limbs + k] = F64(ext.instance.limbs[k]);
            }
            for k in 0..3 {
                out[limbs.new + k] = F64(ext.c[k]);
            }
            out[limbs.base_position] = if e.flags & Ext::BASE != 0 {
                F64(row.position)
            } else {
                F64::ZERO
            };
        }
        out
    }

    /// The register cycle and memory accesses a row with these columns pulls from the logs.
    pub(crate) fn link_tuples(&self, row: &[F64]) -> Vec<Vec<F64>> {
        self.flushes().pull[2..]
            .iter()
            .map(|tuple| tuple.iter().map(|c| c.value(row)).collect())
            .collect()
    }

    /// The identities the table proves of every one of its rows, in local column indices: none for a class with a
    /// circuit, and for the extension-field product its three new limbs.
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
    /// product: degree 2, every coefficient one. A base-field `b`'s high limbs are zero, the padding producer's.
    ///
    /// A last identity defines `base_position = base position`, the memory positions a base-field `b` skips.
    pub(crate) fn identities(&self) -> Vec<BusForm> {
        let c = &self.cols;
        let (Some(limbs), Some(bits)) = (c.limbs, c.flag_bits) else {
            return Vec::new();
        };
        let (a, b, old) = (limbs.limbs, limbs.limbs + 3, limbs.limbs + 6);
        // `base_position = base position`, which skips a base-field `b`'s high limbs.
        let mut base_position = BusForm::new(self.n_committed_columns(), F192::ZERO);
        base_position.coeffs[limbs.base_position] = F192::ONE;
        base_position.prods.push((bits + 1, c.position, F192::ONE));
        let products = (0..3).map(|i| {
            let mut form = BusForm::new(self.n_committed_columns(), F192::ZERO);
            form.coeffs[limbs.new + i] = F192::ONE;
            form.prods.push((bits, old + i, F192::ONE));
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
        products.chain([base_position]).collect()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::colval::ColVal;

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
            for part in [Part::Class, Part::Operands] {
                for (_, column) in table.word_columns(part) {
                    assert!(column < width);
                }
            }
            // A row pushes its successor, and pulls its state, its entry, its register cycle and each memory access.
            let bus = table.flushes();
            assert_eq!(bus.push.len(), 1);
            assert_eq!(bus.pull.len(), 3 + table.id.spec().ram.accesses());
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
            // Invariant: on a row, the identities vanish exactly when the new limbs are the reference's.
            //
            // Mutation: one bit of one new limb, which only that limb's identity reads.
            let table = TableId::EXT.class_table();
            let (cols, bits) = (table.cols.limbs.unwrap(), table.cols.flag_bits.unwrap());
            let mut limbs = limbs;
            if flags & Ext::BASE != 0 {
                (limbs[4], limbs[5]) = (0, 0);
            }
            let mut row = vec![F64::ZERO; table.n_committed_columns()];
            row[cols.limbs..cols.limbs + 9].copy_from_slice(&limbs.map(F64));
            row[cols.new..cols.new + 3].copy_from_slice(&Ext { flags, pointers: [0; 3], limbs }.eval().map(F64));
            (row[bits], row[bits + 1]) = (F64(flags & 1), F64(flags >> 1));
            let values = |row: &[F64]| table.identities().iter().map(|form| <F64 as ColVal>::reduce(form.eval_unreduced(row, false))).collect::<Vec<_>>();
            proptest::prop_assert_eq!(values(&row), vec![F192::ZERO; 4]);
            row[cols.new + wrong].0 ^= 1 << bit;
            let values = values(&row);
            for (i, value) in values.into_iter().enumerate() {
                proptest::prop_assert_eq!(value == F192::ZERO, i != wrong);
            }
        }
    }
}
