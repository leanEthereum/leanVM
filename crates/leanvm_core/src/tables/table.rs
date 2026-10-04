//! One instruction table's circuit bindings and bus interactions.

use super::bus::{FlushBuilder, Separator};
use super::columns::Columns;
use super::{BAD_SLOT, ClassSpec, EXIT_SLOT, N_TABLES, Part, Word};
use crate::leaf::Coord::{self, Col, Const};
use crate::rv::{Class, Ext, ExtResult, Hash, RegisterFile};
use primitives::field::{F64, g_pow};
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
        Self {
            index,
            spec,
            cols,
            clock_ports: spec.clock_ports(),
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
        // The limbs: each operand's first at its pointer, the others where the circuit says.
        //
        // A base-field `b`'s high limbs are reads of `x0`: the circuit's separator and address name it.
        if let (Some(limbs), Some(r), Some(p)) = (c.limbs, c.rs2, c.pointer) {
            let pointers = [c.v1, r.v2, p.vd];
            for k in 0..Ext::LIMBS {
                let sep = if ExtResult::SEPARATED_LIMBS.contains(&k) {
                    Col(limbs.separator)
                } else {
                    Separator::Memory.coordinate()
                };
                let addr = Col(limbs.address(k, pointers));
                accesses.write(sep, addr, Col(limbs.limbs + k), Col(limbs.left(k)));
            }
        }
        accesses.finish();
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
}
