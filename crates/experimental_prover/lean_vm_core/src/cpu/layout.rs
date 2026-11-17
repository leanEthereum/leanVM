//! The public column schema and bus layout: the committed-column indices, and
//! the flush/count blocks the verifier reconstructs from the program + announced
//! sizes and public input. Plus the prover-side witness build.

use super::*;

// ---- column schema -----------------------------------------------------------

// The program is public: it rides the bytecode blocks as `Coord::Public`, and only its execution counts are committed.
/// The Keccak reduction's committed states `q_keccak`, `2^(SLOT_LOG + τ)` words for `2^τ` steps: the one copy of the
/// `KECCAK` input lanes, whose columns are virtual ([`keccak_value`]).
pub use verifier::layout::QKECCAK;

/// Global column indexing: the shared columns occupy `0..NUM_GLOBAL_COLUMNS`, then each
/// table `t` (in [`tables::tables`] order) owns the contiguous block `[base[t],
/// base[t] + n_committed_columns_t)`. Both prover and verifier derive this identically
/// from the table set, so every column claim lines up.
pub struct Schema {
    pub base: [usize; tables::N_TABLES],
    pub n: usize,
}

/// The schema is a pure function of the fixed table set, so compute it once.
pub fn schema() -> &'static Schema {
    static SCHEMA: std::sync::OnceLock<Schema> = std::sync::OnceLock::new();
    SCHEMA.get_or_init(|| {
        let mut base = [0usize; tables::N_TABLES];
        let mut next = NUM_GLOBAL_COLUMNS;
        for (t, table) in tables::tables().iter().enumerate() {
            base[t] = next;
            next += table.n_committed_columns();
        }
        Schema { base, n: next }
    })
}

/// A KECCAK column that `q_keccak` carries. Both kinds are VIRTUAL, with no placement of
/// their own.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum KeccakLane {
    /// A column whose words ARE `q_keccak`'s slot `s`, so a claim on it is a claim on that
    /// slot: an input lane (slot = lane), or one of the columns riding the spare slots.
    Slot(usize),
    /// Output lane `l`, whose claim is the Keccak reduction's claim on the permutation's output.
    Output(usize),
}

/// Slots of `q_keccak` no committed state occupies: the lanes of the states a step commits,
/// `crate::keccak::SLOTS`, rounded up to the power of two the slot index needs. The reduction
/// weighs nothing there, so they carry the KECCAK table's own first columns instead of zeros,
/// which is `QKECCAK_SPARE` columns the stack does not have to hold twice.
pub const QKECCAK_SPARE: usize = (1 << crate::keccak::SLOT_LOG) - crate::keccak::SLOTS;

/// The local KECCAK column riding spare slot `k`: its committed columns in local order, which
/// are the ones before the value lanes, then the read counts after them.
const fn spare_local(k: usize) -> usize {
    if k < tables::keccakt::V_IN {
        k
    } else {
        tables::keccakt::R0 + (k - tables::keccakt::V_IN)
    }
}
const _: () = {
    let mut k = 0;
    while k < QKECCAK_SPARE {
        let local = spare_local(k);
        // Increasing, so distinct: two spare slots sharing a column would leave the other's
        // words unwritten. And never a value lane, which q_keccak already holds.
        assert!(
            k == 0 || spare_local(k - 1) < local,
            "the spare columns must be distinct"
        );
        assert!(
            local < tables::keccakt::V_IN || (local >= tables::keccakt::R0 && local < tables::keccakt::N),
            "the KECCAK table has fewer committed columns than q_keccak has spare slots"
        );
        k += 1;
    }
};

/// What `q_keccak` holds for the global column `col`, if it holds anything: a value lane of
/// the KECCAK table, or one of its columns riding a spare slot.
pub fn keccak_value(col: usize) -> Option<KeccakLane> {
    use primitives::hash::STATE_LANES;
    let local = col.checked_sub(schema().base[verifier::layout::OP_KECCAK])?;
    if local >= tables::keccakt::N {
        return None;
    }
    if let Some(k) = (0..QKECCAK_SPARE).find(|&k| spare_local(k) == local) {
        return Some(KeccakLane::Slot(crate::keccak::SLOTS + k));
    }
    let lane = local.checked_sub(tables::keccakt::V_IN)?;
    match lane {
        0..STATE_LANES => Some(KeccakLane::Slot(lane)),
        _ if lane < 2 * STATE_LANES => Some(KeccakLane::Output(lane - STATE_LANES)),
        _ => None,
    }
}

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

/// The public proof structure: everything the verifier reconstructs from the
/// program, the announced sizes, and the public input, with no witness values. The
/// flush blocks reference columns by INDEX (see [`crate::leaf::Coord`]), so they
/// are pure public structure.
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

/// The prover's witness: the stacked multilinear `q`, which holds every committed
/// column at its placed offset, plus the public [`Layout`] (and the sizes needed to
/// announce it).
pub(crate) struct Witness {
    pub(crate) q: Vec<F64>,
    /// The KECCAK output lanes' values as `(global column index, values)`. They carry
    /// data for the bus but are not committed, so they are not in `q`.
    pub(crate) virt: Vec<(usize, Vec<F64>)>,
    pub(crate) layout: Layout,
    pub(crate) log_mem: usize,
    /// What the Keccak reduction needs beside `q`, which holds the states it rebuilds its witness from.
    pub(crate) keccak_reduction: crate::keccak::Reduction,
}

impl Witness {
    /// One read-only view per column, in global column order: the window into the
    /// stack for a committed column or a KECCAK input lane (its slot of `q_keccak`),
    /// the private buffer for an output lane.
    pub(crate) fn columns(&self) -> Vec<&[F64]> {
        let q_keccak = self.layout.placements[QKECCAK].offset;
        let steps = 1 << self.layout.taus[verifier::layout::OP_KECCAK];
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

/// The committed columns' kappa SOURCES, for the recursion guest's
/// in-circuit certification of the stacked size m = max(log2_ceil(sum of
/// 2^kappa), MIN_STACKED_LOG). Per committed column: `Some((source, adj))` with
/// kappa = value(source) + adj, where source 0 is the constant 0 (kappa =
/// adj; used for the fixed-size columns and the program bytecode length,
/// which the caller passes as `log_bytecode`), source 1 is log_mem, and
/// source 2 + t is tau_t. `None` = virtual (never committed). `col_kappas`
/// is derived from this, so the two cannot drift apart.
pub fn col_kappa_sources(log_bytecode: usize) -> Vec<Option<(usize, usize)>> {
    let sch = schema();
    let mut k = vec![Some((0usize, 0usize)); sch.n];
    k[MEMORY_0] = Some((1, 0));
    k[MEMORY_1] = Some((1, 0));
    k[MEMORY_FINAL_COUNTERS] = Some((1, 0));
    k[BYTECODE_FINAL_COUNTERS] = Some((0, log_bytecode));
    // q_keccak is `2^(SLOT_LOG + n_steps_log)` F64 words, and tau_5 IS
    // n_steps_log (the announced-size certification uses the same floor), so this
    // reproduces `qkeccak_kappa`.
    k[QKECCAK] = Some((2 + verifier::layout::OP_KECCAK, crate::keccak::SLOT_LOG));
    for (t, table) in tables::tables().iter().enumerate() {
        let base = sch.base[t];
        k[base..base + table.n_committed_columns()].fill(Some((2 + t, 0)));
    }
    // The columns `q_keccak` carries are ALWAYS virtual: it already holds the input words at
    // fixed slots and the KECCAK columns riding its spare ones, and the output words are the
    // reduction's to prove. A slot column's bus claims route directly to the matching
    // `q_keccak` slot evaluation (`slot_claims`), the output lanes' to the reduction's output
    // claim, which binds both to the proven witness with no separate value-binding
    // sub-protocol.
    for (col, k) in k.iter_mut().enumerate() {
        if keccak_value(col).is_some() {
            *k = None;
        }
    }
    k
}

/// The bus flush blocks' kappa SOURCES, flattened in side order (push, pull,
/// count) exactly as the blocks are constructed below: per block
/// `(source, adj)` with kappa = value(source) + adj, source 0 = the constant
/// 0, 1 = log_mem, 2 + t = tau_t. For the recursion guest's in-circuit pin
/// of every hinted block kappa. Keep in lockstep with the block
/// construction in `layout_of`.
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

/// Column → log-size (`kappa`) map, derived from [`col_kappa_sources`] by
/// substituting the announced sizes: source 0 is the constant 0, source 1 is
/// `log_mem`, source `2 + t` is `tau_t`. `None` marks a **virtual**
/// (uncommitted) column. Depends only on the public sizes, so the verifier can
/// reconstruct the placements.
fn col_kappas(log_mem: usize, log_bytecode: usize, taus: [usize; tables::N_TABLES]) -> Vec<Option<usize>> {
    let mut values = vec![0usize, log_mem];
    values.extend(taus);
    col_kappa_sources(log_bytecode)
        .iter()
        .map(|s| s.map(|(source, adj)| values[source] + adj))
        .collect()
}

/// Build the public [`Layout`] of a run of a `2^log_bytecode`-instruction program with `2^log_mem` cells of memory,
/// `rows` rows in each table and the public input `pi`. The flush blocks reference columns only by INDEX and the
/// program only through its public columns ([`Coord::Public`]), so this needs no committed witness: both prover and
/// verifier reconstruct exactly the same structure.
pub(crate) fn layout_of(log_bytecode: usize, log_mem: usize, rows: [usize; tables::N_TABLES], pi: [F128; 2]) -> Layout {
    let taus = table_logs(rows);
    let bytecode_size = 1 << log_bytecode;

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
        vec![Const(SEP_MEM), Index, Const(one), Col(MEMORY_0), Col(MEMORY_1)],
    ));
    pull.push(Block::full(
        log_mem,
        vec![
            Const(SEP_MEM),
            Index,
            Col(MEMORY_FINAL_COUNTERS),
            Col(MEMORY_0),
            Col(MEMORY_1),
        ],
    ));
    // bytecode seed + finalize (program columns are public; padding entries
    // self-cancel at count 1, so the whole 2^log_bytecode is "real").
    let bytecode_block = |count: Coord| {
        // Each later slot is the stacked bytecode's column of that slot.
        let mut coords = vec![Const(SEP_BYTECODE), Index, count];
        coords.extend((coords.len()..1 << verifier::layout::BUS_BITS).map(Public));
        Block::full(log_bytecode, coords)
    };
    push.push(bytecode_block(Const(one)));
    pull.push(bytecode_block(Col(BYTECODE_FINAL_COUNTERS)));

    // Per-table blocks: each table declares its flushes and read-count columns in
    // local indices; offset them to the table's global columns.
    let sch = schema();
    let mut count_blocks: Vec<Block> = Vec::new();
    for (t, table) in tables::tables().iter().enumerate() {
        let base = sch.base[t];
        let table_block = |coords: Vec<Coord>| Block {
            kappa: taus[t],
            rows: rows[t],
            coords: offset_coords(base, coords),
        };
        let mut fb = FlushBuilder::new();
        table.flushes(&mut fb);
        push.extend(fb.push.into_iter().map(table_block));
        pull.extend(fb.pull.into_iter().map(table_block));
        count_blocks.extend(table.count_columns().iter().map(|&c| table_block(vec![Col(c)])));
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
        taus[verifier::layout::OP_KECCAK],
        crate::keccak::n_steps_log(rows[verifier::layout::OP_KECCAK]),
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

    let sch = schema();
    // g^0..g^{span-1}, so every pc/frame/operand/count fill is an O(1) lookup instead
    // of an O(log) power: a frame base or an operand is below the cells the run used.
    let span = exec.mem_used.max(bytecode_size).max(tr.counts);
    let gpow = primitives::field::g_powers(span);

    // `l`, the public layout (flush/count blocks, placements, boundary, taus), is a pure
    // function of the program, the announced sizes and the public input, so the prover
    // and the verifier share it; it fixes each table's height `2^tau`, which lets every
    // column be allocated at its final length in one pass.

    // The stacked witness is written exactly ONCE: allocate it, carve one window
    // per committed column, and have every fill write its column straight into
    // place. Copying columns in afterwards would move the whole witness a second
    // time for no gain: nothing folds the K-columns
    // in place, so the stack can be their only home.
    //
    // SAFETY: the allocation is uninitialized. `split_stack` zeroes the pad tail
    // and hands out windows tiling the rest; `fill_table` checks that each table
    // wrote every window it was given, and the shared columns below write theirs.
    let mut q = unsafe { witness::alloc_stack(l.shape) };
    // An output lane is neither in the stack nor in `q_keccak`, so its values need
    // storage of their own: it carries data for the bus. Every other column `q_keccak`
    // carries ([`Witness::columns`]) is filled through the slot window handed out below.
    let steps = 1 << l.taus[verifier::layout::OP_KECCAK];
    let mut virt: Vec<(usize, Vec<F64>)> = (0..sch.n)
        .filter(|&i| matches!(keccak_value(i), Some(KeccakLane::Output(_))))
        // SAFETY: `FillCtx::runs` writes every row of every window it is given, and
        // `fill_table` asserts each table wrote all of its windows.
        .map(|i| (i, unsafe { primitives::uninit_vec::<F64>(steps) }))
        .collect();
    let mut windows = witness::split_stack(&mut q, &l.placements);
    for (i, buf) in virt.iter_mut() {
        windows[*i] = buf;
    }
    // q_keccak's window is the committed states and then the spare slots, a slot per
    // KECCAK column riding them: hand each its slot, so its fill writes it where it
    // lives and the stack never holds it twice.
    let (states, spare) = std::mem::take(&mut windows[QKECCAK]).split_at_mut(crate::keccak::SLOTS * steps);
    windows[QKECCAK] = states;
    for (k, window) in spare.chunks_exact_mut(steps).enumerate() {
        windows[sch.base[verifier::layout::OP_KECCAK] + spare_local(k)] = window;
    }

    // Each table fills its own columns from the trace (local indices, offset
    // into its global block).
    crate::stage!("Fill columns", || {
        for (t, table) in tables::tables().iter().enumerate() {
            let (base, n) = (sch.base[t], table.n_committed_columns());
            let ctx = FillCtx::new(tr, &exec.mem, &gpow, &program.prog, 1 << l.taus[t], table.padding());
            tables::fill_table(*table, &ctx, &mut windows[base..base + n]);
        }
        // Shared columns. The 128-bit memory image splits into two K-limbs.
        // These four plus `QKECCAK` below are every shared column, and each has to
        // be written: the stack is uninitialized, so one left out would be read
        // as indeterminate bytes rather than caught by a length mismatch.
        const _: () = assert!(NUM_GLOBAL_COLUMNS == 5, "a new shared column needs a fill here");
        // One pass over the image fills all three of its columns, streamed out a
        // cache line of each at a time: nothing reads them before the commitment.
        const LINE: usize = 8;
        const BLOCK: usize = 1 << 10;
        let page_log = Memory::page_log();
        let image = [MEMORY_0, MEMORY_1, MEMORY_FINAL_COUNTERS].map(|c| {
            assert_eq!(windows[c].len(), cells, "a memory column spans the image");
            parallel::SendPtr(windows[c].as_mut_ptr())
        });
        // Cell `i`'s two limbs and its count, which ended at g^{A[i]}.
        let values = |page: Option<&[Cell]>, i: usize| {
            let cell = page.map_or(&Cell::UNWRITTEN, |p| &p[i & ((1 << page_log) - 1)]);
            let limbs = cell.word.to_limbs().map(F64);
            [limbs[0], limbs[1], gpow[cell.count as usize]]
        };
        if cells < BLOCK {
            // A memory smaller than a block, cell by cell.
            let page = exec.mem.page(0);
            for i in 0..cells {
                for (column, value) in image.iter().zip(values(page, i)) {
                    // SAFETY: `i` is below `cells`, every column's length.
                    unsafe { column.add(i).write(value) };
                }
            }
        } else {
            parallel::for_each_chunk(cells / BLOCK, |first, end| {
                let stream = primitives::stream::Stream::new();
                for b in first..end {
                    let at = b * BLOCK;
                    let page = exec.mem.page(at >> page_log);
                    for line in (at..at + BLOCK).step_by(LINE) {
                        let mut buf = [[F64::ZERO; LINE]; 3];
                        for j in 0..LINE {
                            let [lo, hi, count] = values(page, line + j);
                            buf[0][j] = lo;
                            buf[1][j] = hi;
                            buf[2][j] = count;
                        }
                        for (column, values) in image.iter().zip(&buf) {
                            // SAFETY: block `b` owns cells `b·BLOCK..(b+1)·BLOCK` of every
                            // column, in bounds as `cells` is a whole number of blocks.
                            unsafe { stream.copy_uninit(column.add(line), values) };
                        }
                    }
                }
            });
        }
        parallel::fill(windows[BYTECODE_FINAL_COUNTERS], |i| {
            gpow[tr.bytecode_count[i] as usize]
        }); // … at g^{A[pc]}
    });
    // The committed Keccak states q_keccak, ALWAYS in this same stack: built from
    // the executed KECCAK rows in order (row j = step j).
    let keccak_reduction = crate::stage!("Build q_keccak", || {
        keccak_blocks.place(tr.keccak.len(), windows[QKECCAK])
    });

    // (`execute` already asserts the run halts at the sentinel (pc, fp) =
    // (g^{B-1}, 0), exactly the boundary the public layout derives.)
    drop(windows); // release the borrow of `q` and of the output lanes' buffers
    Witness {
        q,
        virt,
        layout: l,
        log_mem,
        keccak_reduction,
    }
}
