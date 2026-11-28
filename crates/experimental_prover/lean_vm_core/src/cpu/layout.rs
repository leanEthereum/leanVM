//! The public structure of a run, which the verifier rebuilds from the program and the announced sizes: the stack's
//! placements over the verifier's column numbering ([`verifier::layout::stack_blocks`]) and the pointer width, and the
//! prover's witness (`build`).

use super::*;
use crate::witness::ColMut;
use std::mem::MaybeUninit;
use verifier::layout::{GLOBAL_COLUMN_BASES, KECCAK_OUT, OP_KECCAK, SizeSource, TABLE_WIDTHS, spare_local};

/// The Keccak reduction's committed states `q_keccak`, `2^(SLOT_LOG + τ)` words for `2^τ` steps: the one copy of the
/// `KECCAK` input lanes, whose columns are virtual ([`keccak_value`]).
pub use verifier::layout::QKECCAK;

/// Every column, the shared ones then each table's, at [`GLOBAL_COLUMN_BASES`].
pub const N_COLUMNS: usize = GLOBAL_COLUMN_BASES[tables::N_TABLES - 1] + TABLE_WIDTHS[tables::N_TABLES - 1];

/// A KECCAK column that `q_keccak` carries. Both kinds are virtual, with no placement of their own.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum KeccakLane {
    /// A column whose words are `q_keccak`'s slot `s`, so a claim on it is a claim on that slot: an input lane
    /// (slot = lane), or one of the columns riding the spare slots ([`verifier::layout::qkeccak_slot`]).
    Slot(usize),
    /// Output lane `l`, whose claim is the Keccak reduction's claim on the permutation's output.
    Output(usize),
}

/// What `q_keccak` holds for the global column `col`, if it holds anything: a value lane of the KECCAK table, or one of
/// its columns riding a spare slot.
pub fn keccak_value(col: usize) -> Option<KeccakLane> {
    if let Some(slot) = verifier::layout::qkeccak_slot(col) {
        return Some(KeccakLane::Slot(slot));
    }
    let lane = col.checked_sub(GLOBAL_COLUMN_BASES[OP_KECCAK] + KECCAK_OUT)?;
    (lane < primitives::hash::STATE_LANES).then_some(KeccakLane::Output(lane))
}
// `q_keccak`'s slots as the verifier counts them: the committed states', then a spare one per riding column.
const _: () = {
    use verifier::layout::{QKECCAK_SLOTS, QKECCAK_SPARE};
    assert!(crate::keccak::SLOTS == QKECCAK_SLOTS && 1 << crate::keccak::SLOT_LOG == QKECCAK_SLOTS + QKECCAK_SPARE);
};

/// The public proof structure: everything the verifier reconstructs from the
/// program, the announced sizes, and the public input, with no witness values.
pub struct Layout {
    /// Per-column placement (offset + n_vars) in the stacked witness; from the
    /// columns' log-sizes alone, so reconstructable by the verifier.
    pub placements: Vec<witness::Placement>,
    /// The stacked witness's shape: its announced `2^mu` size, plus how many lane
    /// blocks of it the prover actually commits (see [`witness::StackShape`]).
    pub shape: witness::StackShape,
    /// Public input: the first two memory cells `m[0], m[1]` (each a 128-bit
    /// word), bound to the committed memory at verification (§sec:e2e-pi).
    pub pi: [F128; 2],
    pub taus: [usize; tables::N_TABLES],
    /// Rows per table the program executed, at most `2^taus[t]`: the rest are padding
    /// rows (§sec:e2e-pad).
    pub rows: [usize; tables::N_TABLES],
    /// The bits of every Hotwire pointer ([`crate::link`]): enough for the cycles `0..=T`, the
    /// memory and the program.
    pub pointer_width: usize,
}

impl Layout {
    /// Where the stack holds the `2^n_vars` rows of the global column `col`: its own placement, or its slot's rows of
    /// `q_keccak` for a column riding there.
    pub fn rows_of(&self, col: usize, n_vars: usize) -> witness::Placement {
        match keccak_value(col) {
            Some(KeccakLane::Slot(slot)) => self.placements[QKECCAK].rows(slot << n_vars, n_vars),
            _ => self.placements[col],
        }
    }
}

/// The prover's witness: the stacked multilinear `q`, which holds every committed
/// column at its placed offset, plus the public [`Layout`] (and the sizes needed to
/// announce it).
pub(crate) struct Witness {
    pub(crate) q: Vec<F64>,
    /// The KECCAK output lanes' values as `(global column index, values)`. The links read
    /// them but they are not committed, so they are not in `q`.
    pub(crate) virt: Vec<(usize, Vec<F64>)>,
    pub(crate) layout: Layout,
    pub(crate) log_mem: usize,
    /// What the Keccak reduction needs beside `q`, which holds the states it rebuilds its witness from.
    pub(crate) keccak_reduction: crate::keccak::Reduction,
    /// Columns a test changes, written back to the stack at [`Witness::write_edits`].
    #[cfg(test)]
    edits: Vec<(usize, Vec<F64>)>,
}

impl Witness {
    /// One read-only view per column, in global column order: the column's rows in the
    /// stack for a committed column or a KECCAK input lane (its slot of `q_keccak`),
    /// the private buffer for an output lane.
    pub(crate) fn columns(&self) -> Vec<&[F64]> {
        let slots = keccak_slots(&self.q, &self.layout);
        let mut cols: Vec<&[F64]> = self
            .layout
            .placements
            .iter()
            .enumerate()
            .map(|(i, p)| match keccak_value(i) {
                Some(KeccakLane::Slot(slot)) => slots[slot],
                _ if p.is_virtual() => &[],
                _ => self.column(i),
            })
            .collect();
        for (i, buf) in &self.virt {
            cols[*i] = buf;
        }
        cols
    }

    /// A committed column's rows in the stack.
    pub(crate) fn column(&self, i: usize) -> &[F64] {
        self.layout.placements[i].view(&self.q)
    }

    /// A committed column's rows, to change: the change reaches the stack at [`Witness::write_edits`].
    #[cfg(test)]
    pub(crate) fn column_mut(&mut self, i: usize) -> &mut [F64] {
        if !self.edits.iter().any(|(c, _)| *c == i) {
            let rows = self
                .layout
                .rows_of(i, self.layout.taus[OP_KECCAK])
                .view(&self.q)
                .to_vec();
            self.edits.push((i, rows));
        }
        let (_, rows) = self.edits.iter_mut().find(|(c, _)| *c == i).expect("just added");
        rows
    }

    /// Write every column changed through [`Witness::column_mut`] back to the stack.
    #[cfg(test)]
    pub(crate) fn write_edits(&mut self) {
        for (i, rows) in std::mem::take(&mut self.edits) {
            let offset = self.layout.rows_of(i, self.layout.taus[OP_KECCAK]).offset;
            self.q[offset..][..rows.len()].copy_from_slice(&rows);
        }
    }

    /// Committed data before the zero-pad to `2^m`: the real witness size.
    pub(crate) fn committed_size(&self) -> usize {
        self.layout
            .placements
            .iter()
            .filter(|p| !p.is_virtual())
            .map(|p| 1usize << p.n_vars)
            .sum()
    }
}

/// `q_keccak`'s slots in the stack `q`, a run of words each, for a caller that has moved another part of the witness
/// out.
pub(crate) fn keccak_slots<'a>(q: &'a [F64], layout: &Layout) -> Vec<&'a [F64]> {
    let column = layout.placements[QKECCAK].view(q);
    let steps = 1 << layout.taus[OP_KECCAK];
    (0..column.len() / steps)
        .map(|slot| &column[slot * steps..(slot + 1) * steps])
        .collect()
}

/// Build the public [`Layout`] of a run of a `2^log_bytecode`-instruction program with `2^log_mem` cells of memory,
/// `rows` rows in each table and the public input `pi`. It needs no committed witness: both prover and verifier
/// reconstruct exactly the same structure.
pub(crate) fn layout_of(log_bytecode: usize, log_mem: usize, rows: [usize; tables::N_TABLES], pi: [F128; 2]) -> Layout {
    let taus = table_logs(rows);
    let mut kappas = vec![None; N_COLUMNS];
    for block in verifier::layout::stack_blocks() {
        let source = match block.source {
            SizeSource::Memory => log_mem,
            SizeSource::Table(t) => taus[t],
        };
        kappas[block.column] = Some(source + block.adj);
    }
    let (placements, shape) = witness::placements_of(&kappas);
    Layout {
        placements,
        shape,
        pi,
        taus,
        rows,
        pointer_width: verifier::pointer_width(log_mem, log_bytecode, rows.iter().sum::<usize>() as u64),
    }
}

/// Every table's log height (`verifier::layout::table_log_heights`).
pub(crate) fn table_logs(rows: [usize; tables::N_TABLES]) -> [usize; tables::N_TABLES] {
    let taus: [usize; tables::N_TABLES] = verifier::layout::table_log_heights(&rows.map(|r| r as u64))
        .try_into()
        .expect("a height per table");
    debug_assert_eq!(
        taus[OP_KECCAK],
        crate::keccak::n_steps_log(rows[OP_KECCAK]),
        "the KECCAK table is the Keccak reduction's batch"
    );
    taus
}

/// `keccak_blocks` is what [`crate::keccak::while_executing`] built behind `exec`'s run.
pub(crate) fn build(program: &Program, exec: &Execution, l: Layout, keccak_blocks: crate::keccak::Blocks) -> Witness {
    assert!(exec.mem.len().is_power_of_two());
    // The trace was emitted in the same walk as the memory image (no re-walk).
    let tr = &exec.trace;
    let cells = exec.mem.len();
    let bytecode_size = program.prog.len();
    let log_mem = crate::log2_strict_usize(cells);

    // g^0..g^{span-1}, so every pc/frame/operand fill is an O(1) lookup instead of an
    // O(log) power: a frame base or an operand is below the cells the run used.
    let span = exec.mem_used.max(bytecode_size);
    let gpow = primitives::field::g_powers(span);

    // `l`, the public layout (placements, taus, pointer width), is a pure
    // function of the program, the announced sizes and the public input, so the prover
    // and the verifier share it; it fixes each table's height `2^tau`, which lets every
    // column be allocated at its final length in one pass.

    // Every fill writes its column in place, once (`witness::split_stack`); `fill_table` checks each table wrote
    // every window it was given, and the shared columns below write theirs.
    let mut q = witness::alloc_stack(l.shape);
    // An output lane is neither in the stack nor in `q_keccak`, so its values need
    // storage of their own: the links read it. Every other column `q_keccak`
    // carries ([`Witness::columns`]) is filled through the slot window handed out below.
    let steps = 1 << l.taus[OP_KECCAK];
    let mut virt: Vec<(usize, Vec<MaybeUninit<F64>>)> = (0..N_COLUMNS)
        .filter(|&i| matches!(keccak_value(i), Some(KeccakLane::Output(_))))
        .map(|i| (i, primitives::uninit_vec::<F64>(steps)))
        .collect();
    let mut windows = witness::split_stack(&mut q, &l.placements);
    for (i, buf) in virt.iter_mut() {
        windows[*i] = ColMut::new(buf);
    }
    // q_keccak's window is the committed states and then the spare slots, a slot per
    // KECCAK column riding them: hand each its slot, so its fill writes it where it
    // lives and the stack never holds it twice.
    let mut slots = std::mem::replace(&mut windows[QKECCAK], ColMut::EMPTY).runs_of(steps);
    let spare = slots.split_off(crate::keccak::SLOTS);
    for (k, window) in spare.into_iter().enumerate() {
        windows[GLOBAL_COLUMN_BASES[OP_KECCAK] + spare_local(k)] = ColMut::new(window);
    }

    // Each table fills its own columns from the trace (local indices, offset
    // into its global block).
    let chunks = crate::link::pointer::Chunks::new(l.pointer_width);
    crate::stage!("Fill columns", || {
        for (t, table) in tables::tables().iter().enumerate() {
            let (base, n) = (GLOBAL_COLUMN_BASES[t], table.n_committed_columns());
            let ctx = FillCtx::new(
                tr,
                &exec.mem,
                &gpow,
                &program.prog,
                &chunks,
                1 << l.taus[t],
                table.padding(),
            );
            tables::fill_table(*table, &ctx, &mut windows[base..base + n]);
        }
        // Shared columns. The 128-bit memory image splits into two K-limbs.
        // These two plus `QKECCAK` below are every shared column, and each has to
        // be written: the stack is uninitialized, so one left out would be read
        // as indeterminate bytes rather than caught by a length mismatch.
        const _: () = assert!(NUM_GLOBAL_COLUMNS == 3, "a new shared column needs a fill here");
        // One pass over the image fills both of its columns, streamed out a
        // cache line of each at a time: nothing reads them before the commitment.
        const LINE: usize = 8;
        const BLOCK: usize = 1 << 10;
        let page_log = Memory::page_log();
        let image = [MEMORY_0, MEMORY_1].map(|c| {
            assert_eq!(windows[c].len(), cells, "a memory column spans the image");
            &windows[c]
        });
        // Cell `i`'s two limbs.
        let values = |page: Option<&[Cell]>, i: usize| {
            let cell = page.map_or(&Cell::UNWRITTEN, |p| &p[i & ((1 << page_log) - 1)]);
            cell.word.to_limbs().map(F64)
        };
        if cells < BLOCK {
            // A memory smaller than a block, cell by cell.
            let page = exec.mem.page(0);
            let stream = primitives::stream::Stream::new();
            for i in 0..cells {
                for (column, value) in image.iter().zip(values(page, i)) {
                    // SAFETY: `i` is below `cells`, every column's length.
                    unsafe { column.write(&stream, i, &[value]) };
                }
            }
        } else {
            parallel::for_each_chunk(cells / BLOCK, |first, end| {
                let stream = primitives::stream::Stream::new();
                for b in first..end {
                    let at = b * BLOCK;
                    let page = exec.mem.page(at >> page_log);
                    for line in (at..at + BLOCK).step_by(LINE) {
                        let mut buf = [[F64::ZERO; LINE]; 2];
                        for j in 0..LINE {
                            let [lo, hi] = values(page, line + j);
                            buf[0][j] = lo;
                            buf[1][j] = hi;
                        }
                        for (column, values) in image.iter().zip(&buf) {
                            // SAFETY: block `b` owns cells `b·BLOCK..(b+1)·BLOCK` of every
                            // column, in bounds as `cells` is a whole number of blocks.
                            unsafe { column.write(&stream, line, values) };
                        }
                    }
                }
            });
        }
    });
    // The committed Keccak states q_keccak, ALWAYS in this same stack: built from
    // the executed KECCAK rows in order (row j = step j).
    let keccak_reduction = crate::stage!("Build q_keccak", || keccak_blocks.place(tr.keccak.len(), slots));

    // (`execute` already asserts the run halts at the sentinel (pc, fp) =
    // (g^{B-1}, 0), exactly the boundary the public layout derives.)
    drop(windows); // release the borrow of `q` and of the output lanes' buffers
    // SAFETY: the windows tile `q` past the zeroed tail, and the output lanes' buffers are windows too: each table's
    // fill wrote every window it was given (`fill_table` checks), the shared columns and `q_keccak` theirs above.
    let (q, virt) = unsafe {
        (
            primitives::assume_init_vec(q),
            virt.into_iter()
                .map(|(i, v)| (i, primitives::assume_init_vec(v)))
                .collect(),
        )
    };
    Witness {
        q,
        virt,
        layout: l,
        log_mem,
        keccak_reduction,
        #[cfg(test)]
        edits: Vec::new(),
    }
}
