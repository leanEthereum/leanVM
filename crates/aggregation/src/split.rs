//! The program split by opcode, as the link reads it (`verifier::link::slot_weights`): the columns a child's
//! verification evaluates at its link point, and how the link's program side weighs them.

use super::guest::unified_guest;
use verifier::layout::{BYTECODE_SLOT_BITS, OPCODE_SLOT, Read, gpow, tables};
use verifier::{E, K};

/// A column of the split program, over the instructions `k`: `[op_k = op]` (`Count`), `[op_k = op]·BC_slot(k)`
/// (`Slot`), or `[op_k = op]·g^k·BC_slot(k)` (`Pc`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum Column {
    Count { op: usize },
    Slot { op: usize, slot: usize },
    Pc { op: usize, slot: usize },
}

/// What a term's factor is, past its constant: `η_bc·slot[arg]`, or `η_mm·γ_addr·μ[arg]`, or `η_mm·γ_word·μ[arg]`,
/// with `arg` a slot or a global access index.
pub(super) const KIND_BC: usize = 0;
pub(super) const KIND_ADDR: usize = 1;
pub(super) const KIND_WORD: usize = 2;

/// One term of the program side: `coef·factor(kind, arg)·column`, on `X_ω` or, `frame` set, on `P_fp`.
#[derive(Clone, Copy, Debug)]
pub(super) struct Term {
    pub(super) column: usize,
    pub(super) frame: bool,
    pub(super) kind: usize,
    pub(super) arg: usize,
    pub(super) coef: E,
}

/// The split columns pad to `2^SPLIT_LOG`.
pub(super) const SPLIT_LOG: usize = 6;

/// The columns and the terms over them, in `slot_weights`'s order: each opcode's count first, then its columns in
/// the order its links name them.
pub(super) fn split_terms() -> (Vec<Column>, Vec<Term>) {
    let tables = tables();
    let mut columns: Vec<Column> = (0..tables.len()).map(|op| Column::Count { op }).collect();
    let mut terms = Vec::new();
    let at = |columns: &mut Vec<Column>, c: Column| {
        columns.iter().position(|&x| x == c).unwrap_or_else(|| {
            columns.push(c);
            columns.len() - 1
        })
    };
    let mut access = 0;
    for (t, table) in tables.iter().enumerate() {
        let links = &table.links;
        let term = |column, frame, kind, arg, coef| Term {
            column,
            frame,
            kind,
            arg,
            coef,
        };
        terms.push(term(t, false, KIND_BC, OPCODE_SLOT, gpow(t as u64)));
        for (slots, _) in &links.bytecode_link().operands {
            for &s in slots {
                let c = at(&mut columns, Column::Slot { op: t, slot: s });
                terms.push(term(c, false, KIND_BC, slots[0], E::new(1, 0)));
            }
        }
        for a in &links.memory {
            if let Some((s, e)) = a.frame {
                let c = at(&mut columns, Column::Slot { op: t, slot: s });
                terms.push(term(c, true, KIND_ADDR, access, gpow(e)));
            }
            for read in &a.reads {
                let (column, frame, scale) = match *read {
                    Read::Word { .. } => continue,
                    Read::Slot { slot, scale } => (Column::Slot { op: t, slot }, false, scale),
                    Read::Frame { slot, scale } => (Column::Slot { op: t, slot }, true, scale),
                    Read::Pc { slot, scale } => (Column::Pc { op: t, slot }, false, scale),
                };
                let c = at(&mut columns, column);
                terms.push(term(c, frame, KIND_WORD, access, scale));
            }
            access += 1;
        }
    }
    assert!(columns.len() <= 1 << SPLIT_LOG, "the split columns fit SPLIT_LOG");
    (columns, terms)
}

/// The split columns at `point` over the instructions, by `Bytecode::split`.
pub(super) fn split_values(point: &[E]) -> Vec<E> {
    let (columns, _) = split_terms();
    let split = unified_guest()
        .bytecode()
        .split(point, &verifier::pc_slots(&tables()))
        .expect("a point over the instructions");
    columns
        .iter()
        .map(|&c| match c {
            Column::Count { op } => split.count[op],
            Column::Slot { op, slot } => split.slots[op][slot],
            Column::Pc { op, slot } => split.pc[op][slot],
        })
        .collect()
}

/// The split columns as one table, column `j` at rows `j·n..(j + 1)·n` for `n` instructions, `2^SPLIT_LOG` columns
/// with the missing ones zero: every entry lies in `K`.
pub(super) fn split_table() -> &'static [u64] {
    static TABLE: std::sync::OnceLock<Vec<u64>> = std::sync::OnceLock::new();
    TABLE.get_or_init(|| {
        let stacked = unified_guest().stacked_bytecode();
        let n = stacked.len() >> BYTECODE_SLOT_BITS;
        let (columns, _) = split_terms();
        let mut table = vec![0u64; n << SPLIT_LOG];
        for (j, &c) in columns.iter().enumerate() {
            let column = &mut table[j * n..(j + 1) * n];
            let mut g = K(1);
            for (k, entry) in column.iter_mut().enumerate() {
                let op = stacked[OPCODE_SLOT * n + k].trailing_zeros() as usize;
                let word = |s: usize| K(stacked[s * n + k]);
                *entry = match c {
                    Column::Count { op: o } => u64::from(op == o),
                    Column::Slot { op: o, slot } if op == o => word(slot).0,
                    Column::Pc { op: o, slot } if op == o => (g * word(slot)).0,
                    _ => 0,
                };
                g = g * K(2);
            }
        }
        table
    })
}

/// How many of the table's columns are live: the rest are zero.
pub(super) fn split_live() -> usize {
    split_terms().0.len()
}
