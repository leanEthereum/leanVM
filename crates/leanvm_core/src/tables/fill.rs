//! Sequential registration and parallel execution of column writers.

use super::{ClassTable, Clock};
use crate::cpu::{Row, Trace};
use crate::rv::RiscvProgram;
use parallel::SendPtr;
use primitives::field::F64;
use std::ops::Range;

/// Trace inputs and queued writers for one table's columns.
pub(crate) struct FillContext<'a> {
    /// Trace containing executed and padding rows for every table.
    trace: &'a Trace,

    /// Public decoded program supplying each row's bytecode fields.
    program: &'a RiscvProgram,

    /// Number of rows in every destination column.
    rows: usize,

    /// Columns with a registered writer, checked before any uninitialized window is read.
    written: Vec<bool>,

    /// Writers applied together while each block of trace rows is in cache.
    writers: Vec<ColumnWriter<'a>>,
}

impl<'a> FillContext<'a> {
    /// Start sequential registration for a table with fixed row and column counts.
    pub(crate) fn new(trace: &'a Trace, program: &'a RiscvProgram, rows: usize, n_cols: usize) -> Self {
        Self {
            trace,
            program,
            rows,
            written: vec![false; n_cols],
            writers: Vec::new(),
        }
    }

    /// Queue one column's values from the trace rows.
    fn column<R: Sync>(
        &mut self,
        out: &mut [ColumnOut],
        rows: &'a [R],
        at: usize,
        f: impl Fn(&R) -> F64 + Send + Sync + 'a,
    ) {
        self.columns(out, rows, at, move |r| [f(r)]);
    }

    /// Queue consecutive columns computed together from each row.
    fn columns<const N: usize, R: Sync>(
        &mut self,
        out: &mut [ColumnOut],
        rows: &'a [R],
        at: usize,
        f: impl Fn(&R) -> [F64; N] + Send + Sync + 'a,
    ) {
        self.columns_at(out, rows, std::array::from_fn(|k| at + k), f);
    }

    /// Queue selected columns computed together from each row.
    /// Each column accepts exactly one writer.
    fn columns_at<const N: usize, R: Sync>(
        &mut self,
        out: &mut [ColumnOut],
        rows: &'a [R],
        at: [usize; N],
        f: impl Fn(&R) -> [F64; N] + Send + Sync + 'a,
    ) {
        let n = self.rows;
        let dst: [SendPtr<F64>; N] = at.map(|c| {
            assert_eq!(out[c].len(), n, "column {c} has the wrong window length");
            assert!(
                !std::mem::replace(&mut self.written[c], true),
                "column {c} was registered twice"
            );
            SendPtr(out[c].as_mut_ptr())
        });
        // Padding is already in the trace, so every writer must cover the entire column.
        assert_eq!(rows.len(), n, "a table's rows must fill its cube");
        let writer = move |range: Range<usize>| {
            for i in range {
                let v = f(&rows[i]);
                for (k, p) in dst.iter().enumerate() {
                    // SAFETY: row blocks are disjoint and each column has exactly one writer.
                    // Every index is within the checked column height.
                    // Destination windows stay borrowed until the table's fill call joins every task.
                    unsafe { p.add(i).write(v[k]) };
                }
            }
        };
        self.writers.push(Box::new(writer));
    }

    /// Run every queued writer, in one parallel pass over the rows.
    fn finish(self) {
        let writers = self.writers;
        assert!(
            self.written.iter().all(|&written| written),
            "a table left one of its columns unwritten"
        );
        // One task per block of rows; every writer covers the block while its rows are in cache.
        parallel::for_each(self.rows.div_ceil(FILL_ROWS), |task| {
            let range = task * FILL_ROWS..((task + 1) * FILL_ROWS).min(self.rows);
            for writer in &writers {
                writer(range.clone());
            }
        });
    }
}

/// Writes some of a table's columns for a range of its rows.
type ColumnWriter<'a> = Box<dyn Fn(Range<usize>) + Send + Sync + 'a>;

/// Rows processed together to reuse the trace block across all column writers.
const FILL_ROWS: usize = 1 << 10;

/// Destination window for a committed or virtual column.
pub type ColumnOut<'a> = &'a mut [F64];

impl ClassTable {
    /// Fill every local column from the trace, including virtual circuit columns.
    ///
    /// Registration is sequential.
    /// Disjoint row blocks are written in parallel.
    ///
    /// # Panics
    ///
    /// Panics if a column is missing, registered twice, or has the wrong height.
    pub(crate) fn fill<'a>(&'a self, mut ctx: FillContext<'a>, out: &mut [ColumnOut]) {
        assert_eq!(
            out.len(),
            self.n_committed_columns(),
            "the table has the wrong number of windows"
        );
        assert_eq!(
            ctx.written.len(),
            out.len(),
            "the fill context has the wrong number of columns"
        );
        let c = &self.cols;
        let rows: &[Row] = &ctx.trace.rows[self.index];
        let p = ctx.program;
        let entry = move |r: &Row| &p.entries()[r.index as usize];
        ctx.columns(out, rows, c.pc, move |r| {
            let pc = p.pc_of(r.index as usize);
            [
                F64(pc),
                F64(r.ts),
                F64(entry(r).a1 as u64),
                F64(pc.wrapping_add(4)),
                F64(r.v1),
            ]
        });
        if let Some(flags) = c.flags {
            ctx.column(out, rows, flags, move |r| F64(entry(r).flags));
        }
        if let Some(rs2) = c.rs2 {
            ctx.columns_at(out, rows, [rs2.a2, rs2.v2], move |r| {
                [F64(entry(r).a2 as u64), F64(r.v2)]
            });
        }
        if let Some(rd) = c.rd {
            ctx.columns_at(out, rows, [rd.ad, rd.vd_old], move |r| {
                [F64(entry(r).ad as u64), F64(r.vd_old)]
            });
            // A doubleword load's result is its cell's column, written with the cell.
            if c.ram.is_none_or(|ram| ram.cell != rd.out) {
                ctx.column(out, rows, rd.out, move |r| F64(r.out));
            }
        }
        if let Some(p) = c.pointer {
            ctx.columns_at(out, rows, [p.ad, p.vd], move |r| {
                [F64(entry(r).ad as u64), F64(r.ext().instance.pointers[2])]
            });
        }
        if let Some(k) = c.control {
            ctx.columns_at(out, rows, [k.dt, k.link, k.jalr, k.taken, k.exit], move |r| {
                let e = entry(r);
                [
                    F64(p.dt_of(r.index as usize)),
                    F64(e.link as u64),
                    F64(e.jalr as u64),
                    F64(r.taken as u64),
                    F64((e.is_exit()) as u64),
                ]
            });
        }
        if let Some(imm) = c.imm {
            ctx.column(out, rows, imm, move |r| F64(entry(r).imm));
        }
        if let Some(ram) = c.ram {
            ctx.columns_at(out, rows, [ram.address, ram.cell], move |r| {
                [F64(r.ram.address), F64(r.ram.old)]
            });
            // A load leaves its cell, and a doubleword store's new cell is its `v2` column.
            if ram.new != ram.cell && c.rs2.is_none_or(|rs2| rs2.v2 != ram.new) {
                ctx.column(out, rows, ram.new, move |r| F64(r.ram.new));
            }
        }
        if let Some(block) = c.block {
            ctx.columns(out, rows, block.words, move |r| r.hash().block.map(F64));
            ctx.columns(out, rows, block.out, |r| r.hash().out.map(F64));
        }
        if let Some(limbs) = c.limbs {
            ctx.columns(out, rows, limbs.limbs, |r| r.ext().instance.limbs.map(F64));
            ctx.columns(out, rows, limbs.new, |r| r.ext().result.c.map(F64));
            ctx.columns(out, rows, limbs.addresses, |r| r.ext().result.addresses.map(F64));
            ctx.column(out, rows, limbs.separator, |r| F64(r.ext().result.separator));
        }
        if let Some(bad) = c.bad {
            ctx.column(out, rows, bad, move |_| F64::ZERO);
        }
        let n = self.spec.n_accesses();
        for i in 0..n {
            ctx.column(out, rows, c.prev + i, move |r| F64(r.prev()[i]));
        }
        let slots = self.spec.slots();
        ctx.column(out, rows, c.step, move |r| {
            F64(Clock { timestamp: r.ts }.step(&r.prev()[..n], &slots))
        });
        ctx.finish();
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::cpu::{Execution, Program};
    use crate::rv::Region;
    use crate::rv::asm::Asm;

    fn fixture() -> (Program, Execution) {
        // A real trace supplies the context.
        let text = Asm::new().exit().finish();
        let program = Program::new(&text, Region::TEXT.base(), vec![], 2, 0).expect("valid exit program");
        let execution = program.execute(&[]).expect("the program exits");
        (program, execution)
    }

    #[test]
    fn queued_writers_cover_noncontiguous_columns_and_the_last_row_block() {
        // A partial final block exercises the task boundary where most indexing mistakes occur.
        let (program, execution) = fixture();
        let rows: Vec<u64> = (0..FILL_ROWS as u64 + 7).collect();
        let mut context = FillContext::new(&execution.trace, program.rv(), rows.len(), 3);
        let mut columns: [Vec<F64>; 3] = std::array::from_fn(|_| vec![F64(u64::MAX); rows.len()]);
        let mut windows = columns.each_mut().map(Vec::as_mut_slice);
        context.columns_at(&mut windows, &rows, [2, 0], |&value| [F64(value + 2), F64(value)]);
        context.column(&mut windows, &rows, 1, |&value| F64(value + 1));
        context.finish();
        for (column, values) in columns.iter().enumerate() {
            for (row, value) in values.iter().enumerate() {
                assert_eq!(*value, F64((row + column) as u64));
            }
        }
    }

    #[test]
    #[should_panic(expected = "column 0 was registered twice")]
    fn duplicate_column_writers_are_refused() {
        // A second writer must not overwrite a column already owned by the first writer.
        let (program, execution) = fixture();
        let rows = [0u64];
        let mut context = FillContext::new(&execution.trace, program.rv(), 1, 1);
        let mut window = [F64::ZERO];
        let mut windows = [&mut window[..]];
        context.column(&mut windows, &rows, 0, |&value| F64(value));
        context.column(&mut windows, &rows, 0, |&value| F64(value));
    }

    #[test]
    #[should_panic(expected = "a table left one of its columns unwritten")]
    fn missing_column_writers_are_refused() {
        // Unregistered windows may contain uninitialized witness bytes.
        let (program, execution) = fixture();
        FillContext::new(&execution.trace, program.rv(), 1, 1).finish();
    }

    #[test]
    #[should_panic(expected = "column 0 has the wrong window length")]
    fn a_writer_cannot_target_a_short_window() {
        // Destination bounds are checked before any raw pointer is stored or used.
        let (program, execution) = fixture();
        let rows = [0u64, 1];
        let mut context = FillContext::new(&execution.trace, program.rv(), 2, 1);
        let mut window = [F64::ZERO];
        context.column(&mut [&mut window[..]], &rows, 0, |&value| F64(value));
    }
}
