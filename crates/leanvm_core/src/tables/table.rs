//! One instruction table's circuit bindings and bus interactions.

use super::bus::{FlushBuilder, Separator};
use super::columns::Columns;
use super::{Part, PerTable, TableId, Word};
use crate::bus::BusForm;
use crate::bus::Coord::{self, Col, Const};
use crate::constraints::{BitColumns, BitField};
use crate::rv::{Reg, RegisterFile};
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
        let cols = super::clean::table_columns(id.index());
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
                self.id.spec().name
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

    /// The ordered state, bytecode and access tuples generated from the proved Clean table source.
    pub(crate) fn flushes(&self) -> FlushBuilder {
        super::clean::table_flushes(self.id.index())
    }

    /// The bytecode tuple's coordinate holding the cell the entry writes.
    pub(crate) const DESTINATION_SLOT: usize = 6;

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
    /// product: degree 2, every coefficient one. These identities are generated from the proved Clean assertion in
    /// `LeanVMCircuits.ExtensionProduct`. A base-field `b`'s high limbs are zero, being reads of `x0`.
    pub(crate) fn identities(&self) -> Vec<BusForm> {
        let c = &self.cols;
        let (Some(limbs), Some(bits)) = (c.limbs, c.flag_bits) else {
            return Vec::new();
        };
        super::clean::extension_identities(self.n_committed_columns(), bits, limbs.limbs, limbs.new)
    }
    /// The generated plans together with the native slot lists and clock-port projection, for `checkflushes`.
    #[cfg(feature = "circuit-trace")]
    pub(crate) fn flush_dump() -> String {
        use crate::bus::Coord::Scaled;

        fn render(coordinate: &Coord) -> String {
            match coordinate {
                Col(index) => format!("c{index}"),
                Const(value) => format!("k{}", value.0),
                Coord::Sum(terms) => format!("(+ {})", terms.iter().map(render).collect::<Vec<_>>().join(" ")),
                Scaled(value, index) => format!("(* {} c{index})", value.0),
                other => format!("?{other:?}"),
            }
        }

        fn counted(items: impl ExactSizeIterator<Item = String>) -> String {
            std::iter::once(items.len().to_string())
                .chain(items)
                .collect::<Vec<_>>()
                .join(" ")
        }

        let mut lines = Vec::new();
        for (_, table) in Self::all().iter() {
            let spec = table.id.spec();
            let bus = table.flushes();
            let clock = table.ports(Part::Clock).iter();
            lines.push(format!("table {}", spec.name));
            lines.push(format!("columns {}", table.n_committed_columns()));
            lines.push(format!("slots {}", counted(spec.slots().iter().map(u32::to_string))));
            lines.push(format!(
                "clock {}",
                counted(clock.map(|&w| table.cols.column(w).map_or_else(|| "-".to_owned(), |c| c.to_string())))
            ));
            for (side, tuples) in [("push", &bus.push), ("pull", &bus.pull)] {
                for tuple in tuples {
                    lines.push(format!("{side} {}", counted(tuple.iter().map(render))));
                }
            }
        }
        lines.iter().map(|line| format!("{line}\n")).collect()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::rv::Ext;
    use primitives::field::{F64, F192};

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
            let values = |row: &[F64]| table.identities().iter().map(|form| form.eval_unreduced(row, false).reduce()).collect::<Vec<_>>();
            proptest::prop_assert_eq!(values(&row), vec![F192::ZERO; 3]);
            row[cols.new + wrong].0 ^= 1 << bit;
            let values = values(&row);
            for (i, value) in values.into_iter().enumerate() {
                proptest::prop_assert_eq!(value == F192::ZERO, i != wrong);
            }
        }
    }
}
