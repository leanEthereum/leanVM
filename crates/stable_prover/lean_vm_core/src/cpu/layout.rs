//! The public structure of a run, which the verifier rebuilds from the program, the announced sizes and the public
//! input: the bus blocks and the stack's placements, over the verifier's column numbering. And the prover's witness
//! build.

use super::*;
use std::sync::Arc;
use verifier::layout::{GLOBAL_COLUMN_BASES, TABLE_WIDTHS};

// The shared committed columns, `0..N_SHARED`, the verifier's global columns. The program is public: it rides the
// bytecode blocks as `Coord::Public`, and only its execution counts are committed.
/// The memory image's low limbs, a word a cell.
pub const MEM_LO: usize = verifier::layout::MEMORY_0;
/// The memory image's high limbs.
pub const MEM_HI: usize = verifier::layout::MEMORY_1;
/// Each cell's final access count, `g^{A[i]}`.
pub(crate) const MFCNT: usize = verifier::layout::MEMORY_FINAL_COUNTERS;
/// Each pc's execution count, `g^{A[pc]}`.
pub(crate) const BFCNT: usize = verifier::layout::BYTECODE_FINAL_COUNTERS;
/// The Keccak reduction's committed states `q_keccak`, `2^(SLOT_LOG + τ)` words for `2^τ` steps: the one copy of the
/// `KECCAK` input lanes, whose columns are virtual ([`keccak_value`]).
pub use verifier::layout::QKECCAK;
pub(crate) const N_SHARED: usize = verifier::layout::NUM_GLOBAL_COLUMNS;

/// Every column, the shared ones then each table's, at [`GLOBAL_COLUMN_BASES`].
pub(crate) const N_COLUMNS: usize = GLOBAL_COLUMN_BASES[tables::N_TABLES - 1] + TABLE_WIDTHS[tables::N_TABLES - 1];

/// A KECCAK column that `q_keccak` carries. Both kinds are virtual, with no placement of their own.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum KeccakLane {
    /// A column whose words are `q_keccak`'s slot `s`, so a claim on it is a claim on that slot: an input lane
    /// (slot = lane), or one of the columns riding the spare slots ([`verifier::layout::qkeccak_slot`]).
    Slot(usize),
    /// Output lane `l`, whose claim is the Keccak reduction's claim on the permutation's output.
    Output(usize),
}

/// What `q_keccak` holds for the global column `col`, if it holds anything: a value lane of
/// the KECCAK table, or one of its columns riding a spare slot.
pub fn keccak_value(col: usize) -> Option<KeccakLane> {
    if let Some(slot) = verifier::layout::qkeccak_slot(col) {
        return Some(KeccakLane::Slot(slot));
    }
    let lane = col.checked_sub(GLOBAL_COLUMN_BASES[tables::KECCAK_TABLE] + tables::keccakt::V_OUT)?;
    (lane < primitives::hash::STATE_LANES).then_some(KeccakLane::Output(lane))
}
// `q_keccak`'s slots as the verifier counts them: the committed states', then a spare one per riding column.
const _: () = {
    use verifier::layout::{QKECCAK_SLOTS, QKECCAK_SPARE};
    assert!(crate::keccak::SLOTS == QKECCAK_SLOTS && 1 << crate::keccak::SLOT_LOG == QKECCAK_SLOTS + QKECCAK_SPARE);
};

/// Offset a table's local flush coordinates to global column indices.
fn offset_coords(base: usize, coords: Vec<Coord>) -> Vec<Coord> {
    coords.into_iter().map(|c| offset_coord(base, c)).collect()
}

fn offset_coord(base: usize, c: Coord) -> Coord {
    match c {
        Coord::Col(i) => Coord::Col(base + i),
        Coord::GCol(i, k) => Coord::GCol(base + i, k),
        Coord::Prod(i, j, k) => Coord::Prod(base + i, base + j, k),
        Coord::Sum(cs) => Coord::Sum(offset_coords(base, cs)),
        other => other,
    }
}

/// The public proof structure: everything the verifier reconstructs from the program, the announced sizes, and the
/// public input, with no witness values. The flush blocks reference columns by index ([`crate::leaf::Coord`]).
pub struct Layout {
    pub push: Vec<Block>,
    pub pull: Vec<Block>,
    /// Count channel: read-count columns whose product must be nonzero (§sec:memchan).
    pub count: Vec<Block>,
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
}

impl Layout {
    /// Words of the committed columns, before the stack's pad to a power of two.
    pub(crate) fn committed_size(&self) -> usize {
        (self.placements.iter())
            .filter(|p| !p.is_virtual())
            .map(|p| 1usize << p.n_vars)
            .sum()
    }
}

/// The prover's witness: the stacked multilinear `q`, which holds every committed
/// column at its placed offset, plus the public [`Layout`] (and the sizes needed to
/// announce it).
pub(crate) struct Witness {
    pub(crate) q: Vec<F64>,
    /// The KECCAK output lanes' values as `(global column index, values)`. They carry
    /// data for the bus but are not committed, so they are not in `q`.
    pub(crate) virt: Vec<(usize, Vec<F64>)>,
    pub(crate) layout: Layout,
    /// What the Keccak reduction needs beside `q`, which holds the states it rebuilds its witness from.
    pub(crate) keccak_reduction: crate::keccak::Reduction,
}

impl Witness {
    /// One read-only view per column, in global column order: the window into the
    /// stack for a committed column or a KECCAK input lane (its slot of `q_keccak`),
    /// the private buffer for an output lane.
    pub(crate) fn columns(&self) -> Vec<&[F64]> {
        let q_keccak = self.layout.placements[QKECCAK].offset;
        let steps = 1 << self.layout.taus[tables::KECCAK_TABLE];
        let mut cols: Vec<&[F64]> = self
            .layout
            .placements
            .iter()
            .enumerate()
            .map(|(i, p)| match keccak_value(i) {
                Some(KeccakLane::Slot(slot)) => &self.q[q_keccak + slot * steps..][..steps],
                _ if p.is_virtual() => &[][..],
                _ => &self.q[p.offset..][..1 << p.n_vars],
            })
            .collect();
        for (i, buf) in &self.virt {
            cols[*i] = buf;
        }
        cols
    }
}

/// The committed columns' kappa sources, for the recursion guest's in-circuit certification of the stacked size
/// `m = max(log2_ceil(Σ 2^kappa), MIN_STACKED_LOG)`. Per committed column `Some((source, adj))`, with
/// `kappa = value(source) + adj`: source 0 is the constant 0 (the bytecode's count column takes
/// `adj = log_bytecode`), source 1 is `log_mem`, and source `2 + t` is `tau_t`. `None` marks a virtual column, never
/// committed. `col_kappas` is derived from this, so the two cannot drift apart.
pub fn col_kappa_sources(log_bytecode: usize) -> Vec<Option<(usize, usize)>> {
    let mut k = vec![Some((0usize, 0usize)); N_COLUMNS];
    k[MEM_LO] = Some((1, 0));
    k[MEM_HI] = Some((1, 0));
    k[MFCNT] = Some((1, 0));
    k[BFCNT] = Some((0, log_bytecode));
    // `q_keccak` is `2^(SLOT_LOG + n_steps_log)` words, and the KECCAK table is `2^n_steps_log` rows.
    k[QKECCAK] = Some((2 + tables::KECCAK_TABLE, crate::keccak::SLOT_LOG));
    for t in 0..tables::N_TABLES {
        let base = GLOBAL_COLUMN_BASES[t];
        k[base..base + TABLE_WIDTHS[t]].fill(Some((2 + t, 0)));
    }
    // The columns `q_keccak` carries are virtual: it holds the input lanes and the KECCAK columns riding its spare
    // slots, whose claims route to those slots (`slot_claim`), and the output lanes are the reduction's to prove.
    for (col, k) in k.iter_mut().enumerate() {
        if keccak_value(col).is_some() {
            *k = None;
        }
    }
    k
}

/// The bus blocks' kappa sources, as [`col_kappa_sources`] numbers them, flattened in side order (push, pull,
/// count) as [`layout_of`] builds the blocks: for the recursion guest's in-circuit pin of every hinted block kappa.
pub fn block_kappa_sources(log_bytecode: usize) -> Vec<(usize, usize)> {
    let mut push = vec![(0, 0), (1, 0), (0, log_bytecode)];
    let mut pull = vec![(0, 0), (1, 0), (0, log_bytecode)];
    let mut count = Vec::new();
    for (t, table) in tables::tables().iter().enumerate() {
        let mut fb = tables::FlushBuilder::new();
        table.flushes(&mut fb);
        push.extend(std::iter::repeat_n((2 + t, 0), fb.push.len()));
        pull.extend(std::iter::repeat_n((2 + t, 0), fb.pull.len()));
        count.extend(std::iter::repeat_n((2 + t, 0), table.count_columns().len()));
    }
    push.extend(pull);
    push.extend(count);
    push
}

/// Each column's log size (`kappa`): [`col_kappa_sources`] at the announced sizes, `None` for a virtual column.
/// Depends only on the public sizes, so the verifier can reconstruct the placements.
fn col_kappas(log_mem: usize, log_bytecode: usize, taus: [usize; tables::N_TABLES]) -> Vec<Option<usize>> {
    let mut values = vec![0usize, log_mem];
    values.extend(taus);
    col_kappa_sources(log_bytecode)
        .iter()
        .map(|s| s.map(|(source, adj)| values[source] + adj))
        .collect()
}

/// Operand slots of a bytecode tuple, after the opcode.
pub(crate) const BYTECODE_OPERANDS: usize = 12;

/// The public bytecode columns of a program.
pub type BytecodeColumns = [Arc<Vec<F64>>; 1 + BYTECODE_OPERANDS];

/// The public bytecode columns over the program cube, in bytecode-slot order: the opcode, then
/// the operand slots. The program is not committed, so these ride the seed/finalize blocks as
/// `Coord::Public` and stack into the polynomial [`bytecode_table`] returns.
pub(crate) fn bytecode_columns(prog: &[Op]) -> BytecodeColumns {
    let g_at = primitives::field::g_pow32_by_lookup;

    // The opcode, then the operand slots: offsets as g-powers, a `SET` immediate as its two
    // limbs, the `DEREF` store-mode flags and `KECCAK`'s layout and output flags as 0 or 1. Unused slots
    // are zero.
    let flag = |b: bool| F64(u64::from(b));
    let row = |op: &Op| -> [F64; 1 + BYTECODE_OPERANDS] {
        let mut row = [F64::ZERO; 1 + BYTECODE_OPERANDS];
        let (opcode, slots) = row.split_first_mut().expect("an opcode");
        let mut put = |values: &[F64]| slots[..values.len()].copy_from_slice(values);
        *opcode = match *op {
            Op::Xor { a, b, c } | Op::Mul { a, b, c } => {
                put(&[g_at(a), g_at(b), g_at(c)]);
                if matches!(op, Op::Xor { .. }) { OP_XOR } else { OP_MUL }
            }
            Op::Set { o, k } => {
                let [k0, k1] = [F64(k.c0), F64(k.c1)];
                put(&[g_at(o), k0, k1]);
                OP_SET
            }
            Op::Deref { o1, o2, o3, mode } => {
                put(&[
                    g_at(o1),
                    g_at(o2),
                    g_at(o3),
                    F64(u64::from(mode.f_pc())),
                    F64(u64::from(mode.f_fp())),
                ]);
                OP_DEREF
            }
            Op::Jump { oc, od, of } => {
                put(&[g_at(oc), g_at(od), g_at(of)]);
                OP_JUMP
            }
            Op::Keccak {
                m,
                tail,
                b8,
                cap,
                out,
                in_odd,
                out_odd,
                out_cells,
            } => {
                let [m0, m1, m2, m3] = m.map(g_at);
                let (out_two, out_all) = out_cells.flags();
                put(&[
                    m0,
                    m1,
                    m2,
                    m3,
                    g_at(tail),
                    g_at(b8),
                    g_at(cap),
                    g_at(out),
                    flag(in_odd),
                    flag(out_odd),
                    flag(out_two),
                    flag(out_all),
                ]);
                OP_KECCAK
            }
        };
        row
    };
    let mut columns: [Vec<F64>; 1 + BYTECODE_OPERANDS] = std::array::from_fn(|_| Vec::with_capacity(prog.len()));
    for op in prog {
        for (column, value) in columns.iter_mut().zip(row(op)) {
            column.push(value);
        }
    }
    columns.map(Arc::new)
}

/// The stacked bytecode polynomial: the thirteen columns at their bus tuple
/// coordinates, padded to sixteen selector slots, which is what makes the program's
/// whole share of a bus leaf one sum over the slots of this one multilinear, which a
/// short sumcheck reduces to one evaluation (§sec:e2e-bc).
///
/// This is the multilinear an outermost verifier is handed in place of a
/// structured program, and what the Fiat-Shamir IV hashes.
pub fn bytecode_table(prog: &[Op]) -> Vec<F64> {
    stack_columns(&bytecode_columns(prog))
}

/// [`bytecode_table`] of a program's columns.
pub(crate) fn stack_columns(columns: &BytecodeColumns) -> Vec<F64> {
    use crate::leaf::{BYTECODE_PUBLIC_SLOT, N_TUPLE_BITS};
    const { assert!(BYTECODE_PUBLIC_SLOT + 1 + BYTECODE_OPERANDS <= 1 << N_TUPLE_BITS) };
    let kbc = crate::log2_strict_usize(columns[0].len());
    let mut table = vec![F64::ZERO; 1 << (N_TUPLE_BITS + kbc)];
    for (i, column) in columns.iter().enumerate() {
        let slot = BYTECODE_PUBLIC_SLOT + i;
        table[slot << kbc..(slot + 1) << kbc].copy_from_slice(column);
    }
    table
}

/// The public [`Layout`] of a program's public columns `prog_cols`, the memory log-size `log_mem`, the instruction
/// tables' row counts `rows`, and the public input `pi`. The flush blocks reference columns only by index and the
/// program only through its public columns, so this needs no committed witness: prover and verifier reconstruct the
/// same structure.
pub fn layout_of(
    prog_cols: &BytecodeColumns,
    log_mem: usize,
    rows: [usize; tables::N_TABLES],
    pi: [F128; 2],
) -> Layout {
    let taus = table_logs(rows);
    let bytecode_size = prog_cols[0].len();
    let log_bytecode = crate::log2_strict_usize(bytecode_size);

    // Derived boundary: the run starts at (pc,fp) = (0,0) and, by convention, the
    // final pc is the bytecode's last cell g^{B-1} (the compiler emits a halt jump
    // there), with fp returned to 0. All public, no trace needed.
    let final_pc = (bytecode_size - 1) as u32;

    let one = F64::ONE;

    // ---- bus blocks ----
    use Coord::{Col, Const, Index, Public};

    let mut push: Vec<Block> = Vec::new();
    let mut pull: Vec<Block> = Vec::new();

    // Shared blocks (cross-instruction infra, not owned by any single table).
    // boundary state.
    push.push(Block::full(0, vec![Const(SEP_STATE), Const(one), Const(one)]));
    pull.push(Block::full(
        0,
        vec![Const(SEP_STATE), Const(g_pow(final_pc as usize)), Const(one)],
    ));
    // memory seed + finalize (every address real, no padding). The value is the
    // full two-limb 128-bit word.
    push.push(Block::full(
        log_mem,
        vec![Const(SEP_MEM), Index, Const(one), Col(MEM_LO), Col(MEM_HI)],
    ));
    pull.push(Block::full(
        log_mem,
        vec![Const(SEP_MEM), Index, Col(MFCNT), Col(MEM_LO), Col(MEM_HI)],
    ));
    // bytecode seed + finalize (program columns are public; padding entries
    // self-cancel at count 1, so the whole 2^log_bytecode is "real").
    let bytecode_block = |count: Coord| {
        Block::full(
            log_bytecode,
            [Const(SEP_BYTECODE), Index, count]
                .into_iter()
                .chain(prog_cols.iter().cloned().map(Public))
                .collect(),
        )
    };
    push.push(bytecode_block(Const(one)));
    pull.push(bytecode_block(Col(BFCNT)));

    // Per-table blocks: each table declares its flushes and read-count columns in
    // local indices; offset them to the table's global columns.
    let mut count_blocks: Vec<Block> = Vec::new();
    for (t, table) in tables::tables().iter().enumerate() {
        let base = GLOBAL_COLUMN_BASES[t];
        let padding = table.padding();
        let table_block = |coords: Vec<Coord>| Block {
            kappa: taus[t],
            rows: rows[t],
            padding: coords.iter().map(|c| crate::leaf::coord_at(c, &padding)).collect(),
            coords: offset_coords(base, coords),
            owner: Some(t),
        };
        let mut fb = FlushBuilder::new();
        table.flushes(&mut fb);
        push.extend(fb.push.into_iter().map(table_block));
        pull.extend(fb.pull.into_iter().map(table_block));
        count_blocks.extend(table.count_columns().map(|c| table_block(vec![Col(c)])));
    }

    let (placements, shape) = witness::placements_of(&col_kappas(log_mem, log_bytecode, taus));
    Layout {
        push,
        pull,
        count: count_blocks,
        placements,
        shape,
        pi,
        taus,
        rows,
    }
}

/// Every table's log height: the least that holds its rows, at least its floor.
pub(crate) fn table_logs(rows: [usize; tables::N_TABLES]) -> [usize; tables::N_TABLES] {
    let taus = std::array::from_fn(|t| crate::log2_ceil_usize(rows[t]).max(tables::TABLE_LOG_FLOORS[t]));
    debug_assert_eq!(
        taus[tables::KECCAK_TABLE],
        crate::keccak::n_steps_log(rows[tables::KECCAK_TABLE]),
        "the KECCAK table is the Keccak reduction's batch"
    );
    taus
}

impl Program {
    /// The witness of a run: every committed column written straight into its window of the stack, at the heights
    /// the layout `l` fixes.
    pub(crate) fn build(&self, exec: &Execution, l: Layout) -> Witness {
        let (tr, cells) = (&exec.trace, exec.mem.len());
        // Every pc, frame base, operand and access count a fill writes is a `g`-power below this.
        let gpow = primitives::field::g_powers(exec.mem_used.max(self.prog.len()).max(tr.counts));

        let mut q = parallel::filled(l.shape.committed_len(), F64::ZERO);
        let mut windows = witness::split_stack(&mut q, &l.placements);
        // An output lane is in neither the stack nor `q_keccak`, but the bus reads it: it has a buffer of its own.
        let steps = 1 << l.taus[tables::KECCAK_TABLE];
        let mut virt: Vec<(usize, Vec<F64>)> = (0..N_COLUMNS)
            .filter(|&i| matches!(keccak_value(i), Some(KeccakLane::Output(_))))
            .map(|i| (i, vec![F64::ZERO; steps]))
            .collect();
        for (i, buf) in virt.iter_mut() {
            windows[*i] = buf;
        }
        // `q_keccak`'s window is the committed states, then a spare slot per KECCAK column riding there.
        let (states, spare) = std::mem::take(&mut windows[QKECCAK]).split_at_mut(crate::keccak::SLOTS * steps);
        windows[QKECCAK] = states;
        for (k, window) in spare.chunks_exact_mut(steps).enumerate() {
            windows[GLOBAL_COLUMN_BASES[tables::KECCAK_TABLE] + verifier::layout::spare_local(k)] = window;
        }

        crate::stage!("Fill columns", || {
            for (t, table) in tables::tables().iter().enumerate() {
                let (base, n) = (GLOBAL_COLUMN_BASES[t], TABLE_WIDTHS[t]);
                let ctx = FillCtx::new(tr, &exec.mem, &gpow, &self.prog, 1 << l.taus[t], table.padding());
                table.fill(&ctx, &mut windows[base..base + n]);
            }
            // The shared columns: the memory image's two limbs and each cell's final count `g^{A[i]}`, a cell read
            // once for the three, and each pc's final count.
            const _: () = assert!(N_SHARED == 5, "a new shared column needs a fill here");
            const CHUNK: usize = 1 << 12;
            let [lo, hi, count] = windows.get_disjoint_mut([MEM_LO, MEM_HI, MFCNT]).unwrap();
            assert!(
                [&lo, &hi, &count].iter().all(|w| w.len() == cells),
                "a memory column spans the image"
            );
            parallel::map_reduce_chunks_mut(
                [&mut **lo, &mut **hi, &mut **count],
                [CHUNK; 3],
                || (),
                |_, task, [lo, hi, count]| {
                    for (j, ((lo, hi), count)) in lo.iter_mut().zip(hi.iter_mut()).zip(count.iter_mut()).enumerate() {
                        let cell = exec.mem.cell(task * CHUNK + j);
                        (*lo, *hi, *count) = (F64(cell.word.c0), F64(cell.word.c1), gpow[cell.count as usize]);
                    }
                },
                |_, _| (),
            );
            parallel::fill(windows[BFCNT], |i| gpow[tr.bytecode_count[i] as usize]);
        });
        // The committed Keccak states, step `j` the `j`-th KECCAK row, its input read back from the final memory
        // image, which is write-once.
        let keccak_reduction = crate::stage!("Build q_keccak", || {
            let inputs = parallel::map_collect(tr.keccak.len(), |i| {
                let row = &tr.keccak[i];
                let op = tables::KeccakOp::of(&self.prog[row.pc as usize]);
                crate::keccak::state_of_cells(op.in_odd, |c| exec.mem.word(op.cell(row.fp, c) as usize))
            });
            crate::keccak::place(&inputs, windows[QKECCAK])
        });
        drop(windows);
        Witness {
            q,
            virt,
            layout: l,
            keccak_reduction,
        }
    }
}
