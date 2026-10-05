//! One instruction table's circuit bindings and bus interactions.

use super::bus::{FlushBuilder, Separator};
use super::columns::Columns;
use super::{BAD_SLOT, ClassSpec, EXIT_SLOT, N_TABLES, Part, Word};
use crate::constraints::{BitColumns, BitField};
use crate::leaf::BusForm;
use crate::leaf::Coord::{self, Col, Const, Scaled};
use crate::rv::{Class, Ext, Hash, Reg, RegisterFile};
use primitives::field::{F64, F192, g_pow};
use std::sync::OnceLock;

/// Circuit bindings and bus interactions for one instruction class.
///
/// Column indices are local to this table, including its virtual circuit columns.
pub struct ClassTable {
    /// Table position in the protocol's fixed instruction-class order.
    pub(super) index: usize,

    /// Register accesses, memory shape, and circuit ports of this class.
    pub(super) spec: &'static ClassSpec,

    /// Local column layout, including aliases for unchanged memory values.
    pub(super) cols: Columns,

    /// Clock circuit ports in input-then-output order.
    clock_ports: Vec<Word>,
}

impl ClassTable {
    /// All instruction tables, built once in protocol order.
    pub fn all() -> &'static [Self; N_TABLES] {
        static TABLES: OnceLock<[ClassTable; N_TABLES]> = OnceLock::new();
        TABLES.get_or_init(|| std::array::from_fn(Self::new))
    }

    /// Protocol table index of an instruction class, if supported.
    pub fn index_of(class: Class) -> Option<usize> {
        ClassSpec::ALL.iter().position(|spec| spec.class == class)
    }

    /// Build the columns and clock ports of a validated class specification.
    pub(super) fn new(index: usize) -> Self {
        let spec = ClassSpec::ALL[index];
        spec.assert_valid();
        let cols = Columns::new(spec);
        let table = Self {
            index,
            spec,
            cols,
            clock_ports: spec.clock_ports(),
        };
        table.assert_x0_is_constant();
        table
    }

    /// Asserts that no access of the table can change register cell 0, `x0`.
    ///
    /// - A read pushes back the value it pulls.
    /// - A register access that changes its cell does so at the entry's destination, which the decoder keeps in `1..=32`.
    ///
    /// So `x0` keeps its zero seed, which a base-field extension operand's high limbs read.
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
            let read = matches!((&pull[3], &push[3]), (Col(old), Col(new)) if old == new);
            let at_destination = matches!((&push[1], destination), (Col(at), Col(ad)) if at == ad);
            assert!(
                memory || read || at_destination,
                "{} writes a register other than its destination",
                self.spec.name
            );
        }
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

    /// Number of columns, the virtual ones included.
    pub const fn n_committed_columns(&self) -> usize {
        self.cols.len()
    }

    /// The port words of one of the table's circuits.
    pub fn ports(&self, part: Part) -> &[Word] {
        match part {
            Part::Class => self.spec.ports,
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
    fn flush_state(&self, bus: &mut FlushBuilder) {
        let c = &self.cols;
        // Branches and jumps derive the successor as a degree-two bus form.
        let npc = match (c.control, c.rd) {
            (Some(control), Some(rd)) => control.next_pc(c.pc4, rd.out),
            _ => Col(c.pc4),
        };
        let exit = c
            .control
            .map_or(Const(F64::ZERO), |control| control.exit_marker(c.ts, c.step));
        bus.state(c.pc, c.ts, c.step, npc, exit);
    }

    /// The bytecode tuple's coordinate holding the cell the entry writes.
    pub(crate) const DESTINATION_SLOT: usize = 6;

    /// Read the public decoded entry, using constants for absent register and circuit ports.
    fn bytecode_tuple(&self) -> Vec<Coord> {
        let c = &self.cols;
        // A row without flags, an `rs2` read, an `rd` write or an immediate reads its constant off the entry.
        // Those constants are zero, `x0`, the sink, and zero.
        let mut entry = vec![
            Separator::Bytecode.coordinate(),
            Col(c.pc),
            Const(g_pow(self.index)),
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
        if let (Some(control), Some(_)) = (c.control, c.rd) {
            entry.extend([Col(control.dt), Col(control.link), Col(control.jalr)]);
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
        let mut accesses = bus.accesses(c.ts, c.prev, self.spec.slots());
        let vd = c.rd.map(|rd| {
            c.control
                .map_or(Col(rd.out), |control| control.destination(c.pc4, rd.out))
        });
        accesses.read(Separator::Registers.coordinate(), Col(c.a1), Col(c.v1));
        if let Some(r) = c.rs2 {
            accesses.read(Separator::Registers.coordinate(), Col(r.a2), Col(r.v2));
        }
        if let (Some(rd), Some(vd)) = (c.rd, vd) {
            accesses.write(Separator::Registers.coordinate(), Col(rd.ad), Col(rd.vd_old), vd);
        }
        // An address in `rd` is read and written back as found.
        if let Some(p) = c.pointer {
            accesses.read(Separator::Registers.coordinate(), Col(p.ad), Col(p.vd));
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
        // The hash's block: word `k` at `v1 ^ 8k`, which is `v1 + 8k` in the field.
        if let Some(block) = c.block {
            for k in 0..Hash::WORDS {
                let addr = Coord::Sum(vec![Col(c.v1), Const(F64(8 * k as u64))]);
                accesses.write(
                    Separator::Memory.coordinate(),
                    addr,
                    Col(block.words + k),
                    Col(block.left(k)),
                );
            }
        }
        // The limbs: each operand's first at its pointer, the others at the addresses the clock circuit computes.
        //
        // A base-field `b`'s high limbs are reads of `x0`, at the address zero the clock circuit gives them, under a
        // separator that is a form in the bit `base`, which picks the registers over memory:
        //
        //     separator   memory + base·(memory + registers)
        if let (Some(limbs), Some(r), Some(p), Some(bits)) = (c.limbs, c.rs2, c.pointer, c.flag_bits) {
            let pointers = [c.v1, r.v2, p.vd];
            let (memory, registers) = (Separator::Memory.value(), Separator::Registers.value());
            let base = bits + 1;
            for k in 0..Ext::LIMBS {
                let sep = if k / 3 == 1 && k % 3 > 0 {
                    Coord::Sum(vec![Const(memory), Scaled(memory + registers, base)])
                } else {
                    Separator::Memory.coordinate()
                };
                let addr = Col(limbs.address(k, pointers));
                accesses.write(sep, addr, Col(limbs.limbs + k), Col(limbs.left(k)));
            }
        }
        accesses.finish();
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
    /// product: degree 2, every coefficient one. A base-field `b`'s high limbs are zero, being reads of `x0`.
    pub(crate) fn identities(&self) -> Vec<BusForm> {
        let c = &self.cols;
        let (Some(limbs), Some(bits)) = (c.limbs, c.flag_bits) else {
            return Vec::new();
        };
        let (a, b, old) = (limbs.limbs, limbs.limbs + 3, limbs.limbs + 6);
        (0..3)
            .map(|i| {
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
            })
            .collect()
    }
}

#[cfg(test)]
mod tests {
    use super::super::Clock;
    use super::*;

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
        for table in ClassTable::all() {
            let width = table.n_committed_columns();
            let accesses = table.spec.n_accesses();
            let slots = table.spec.slots();
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
            // Invariant: on a row, the identities vanish exactly when the new limbs are the reference's.
            //
            // Mutation: one bit of one new limb, which only that limb's identity reads.
            let table = &ClassTable::all()[ClassTable::index_of(Class::Ext).unwrap()];
            let (cols, bits) = (table.cols.limbs.unwrap(), table.cols.flag_bits.unwrap());
            let mut limbs = limbs;
            if flags & Ext::BASE != 0 {
                (limbs[4], limbs[5]) = (0, 0);
            }
            let mut row = vec![F64::ZERO; table.n_committed_columns()];
            row[cols.limbs..cols.limbs + 9].copy_from_slice(&limbs.map(F64));
            row[cols.new..cols.new + 3].copy_from_slice(&Ext { flags, pointers: [0; 3], limbs }.eval().map(F64));
            (row[bits], row[bits + 1]) = (F64(flags & 1), F64(flags >> 1));
            let values = |row: &[F64]| table.identities().iter().map(|form| form.eval(row)).collect::<Vec<_>>();
            proptest::prop_assert_eq!(values(&row), vec![F192::ZERO; 3]);
            row[cols.new + wrong].0 ^= 1 << bit;
            let values = values(&row);
            for (i, value) in values.into_iter().enumerate() {
                proptest::prop_assert_eq!(value == F192::ZERO, i != wrong);
            }
        }
    }
}
