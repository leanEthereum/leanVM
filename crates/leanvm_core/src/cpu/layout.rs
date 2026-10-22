//! The public column schema and bus layout: the committed-column indices, and
//! the flush/count blocks the verifier reconstructs from the program + announced
//! sizes and public input. Plus the prover-side witness build.

use super::*;

// ---- column schema -----------------------------------------------------------

// Shared committed columns (indices `0..N_SHARED`). The program (opcode +
// operands) is PUBLIC, not committed: it rides the bytecode seed/finalize blocks
// as `Coord::Public`; only the witness-dependent finalize counts are committed.
// The data-memory image, a 192-bit word per cell committed as three K-lane columns.
pub const MEM_LO: usize = 0;
pub const MEM_HI: usize = 1;
pub const MEM_TOP: usize = 2;
pub const MFCNT: usize = 3; // per-cell memory access count, g^{A[i]}
pub const BFCNT: usize = 4; // per-pc bytecode execution count, g^{A[pc]}
// flock's packed BLAKE2s witness `q_flock`, committed in the SAME stack as every
// other column (single PCS). Size `2^(K_LOG+n_log-6)` F64 words, always ≥ 1
// instance (a no-BLAKE2s program commits one full padding instance). It is the
// SOLE copy of the input/output words: the VM's BLAKE2s value columns are
// virtual and their memory-bus claims route to `q_flock` slots (§hash_flock), so
// nothing duplicates them. flock's R1CS validity is discharged by the single
// stacked WHIR opening over this commitment.
pub const QFLOCK: usize = 5;
pub const N_SHARED: usize = 6;

/// Global column indexing: the shared columns occupy `0..N_SHARED`, then each
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
        let mut next = N_SHARED;
        for (t, table) in tables::tables().iter().enumerate() {
            base[t] = next;
            next += table.n_committed_columns();
        }
        Schema { base, n: next }
    })
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
    /// Public input: the first two memory cells `m[0], m[1]` (each a 192-bit
    /// word), bound to the committed memory at verification (§sec:e2e-pi).
    pub pi: [F192; 2],
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
    /// The virtual columns' values as `(global column index, values)`. They carry
    /// data for the bus but are not committed, so they are not in `q`.
    pub(crate) virt: Vec<(usize, Vec<F64>)>,
    pub(crate) layout: Layout,
    pub(crate) log_mem: usize,
    /// Freed immediately after reduction, before the mixed PCS opening.
    pub(crate) flock_reduction: crate::hash_flock::PreparedReductionWitness,
}

impl Witness {
    /// One read-only view per column, in global column order: the window into the
    /// stack for a committed column, the private buffer for a virtual one.
    pub(crate) fn columns(&self) -> Vec<&[F64]> {
        let mut cols: Vec<&[F64]> = self
            .layout
            .placements
            .iter()
            .map(|p| {
                if p.is_virtual() {
                    &[][..]
                } else {
                    &self.q[p.offset..p.offset + (1 << p.n_vars)]
                }
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
/// 2^kappa), MIN_MU). Per committed column: `Some((source, adj))` with
/// kappa = value(source) + adj, where source 0 is the constant 0 (kappa =
/// adj; used for the fixed-size columns and the program bytecode length,
/// which the caller passes as `log_bytecode`), source 1 is log_mem, and
/// source 2 + t is tau_t. `None` = virtual (never committed). `col_kappas`
/// is derived from this, so the two cannot drift apart.
pub fn col_kappa_sources(log_bytecode: usize) -> Vec<Option<(usize, usize)>> {
    let sch = schema();
    let mut k = vec![Some((0usize, 0usize)); sch.n];
    k[MEM_LO] = Some((1, 0));
    k[MEM_HI] = Some((1, 0));
    k[MEM_TOP] = Some((1, 0));
    k[MFCNT] = Some((1, 0));
    k[BFCNT] = Some((0, log_bytecode));
    // q_flock is `2^(K_LOG + n_blocks_log - LOG_PACKING)` F64 words, always ≥ 1
    // instance (a no-BLAKE2s program commits one padding instance), and tau_5 IS
    // n_blocks_log, so this reproduces `qflock_kappa`.
    k[QFLOCK] = Some((2 + tables::BLAKE2S_TABLE, flock::hash::K_LOG - ::pcs::LOG_PACKING));
    for (t, table) in tables::tables().iter().enumerate() {
        let base = sch.base[t];
        k[base..base + table.n_committed_columns()].fill(Some((2 + t, 0)));
    }
    // The BLAKE2s value columns are ALWAYS virtual: `q_flock` already holds those
    // words at fixed packed slots, so committing them again is redundant. Their
    // memory-bus claims route directly to `q_flock` slot evaluations (`slot_claims`),
    // which both binds them to the proven witness AND removes the separate
    // value-binding sub-protocol.
    let b3 = sch.base[tables::BLAKE2S_TABLE];
    for &c in &tables::BLAKE2S_VALUE_COLS {
        k[b3 + c] = None;
    }
    k
}

/// The bus flush blocks' kappa SOURCES, flattened in side order (push, pull,
/// count) exactly as the blocks are constructed below: per block
/// `(source, adj)` with kappa = value(source) + adj, source 0 = the constant
/// 0, 1 = log_mem, 2 + t = tau_t. For the recursion guest's in-circuit pin
/// of every hinted block kappa. Keep in lockstep with the block
/// construction in [`fn@layout`].
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

/// `log2` of the stacked witness the announced sizes imply. The one part of
/// [`layout`] a size floor needs, and far cheaper than the rest of it.
pub(crate) fn committed_log(log_mem: usize, log_bytecode: usize, taus: [usize; tables::N_TABLES]) -> usize {
    crate::witness::placements_of(&col_kappas(log_mem, log_bytecode, taus))
        .1
        .mu
}

/// The eight PUBLIC bytecode columns over the program cube, in bytecode-slot
/// order: the opcode, then seven operand/immediate slots. The program is not
/// committed, so these ride the seed/finalize blocks as `Coord::Public` and
/// stack into the polynomial [`bytecode_table`] returns.
pub fn bytecode_columns(prog: &[Op]) -> [Vec<F64>; 8] {
    let max_op = prog
        .iter()
        .map(|op| match *op {
            Op::Xor { a, b, c } | Op::Mul { a, b, c } => a.max(b).max(c),
            Op::Set { o, .. } => o,
            Op::Deref { o1, o2, o3, .. } => o1.max(o2).max(o3),
            Op::Jump { oc, od, of } => oc.max(od).max(of),
            Op::Blake2s { ins, cv, out, md } => ins[0].max(ins[1]).max(ins[2]).max(ins[3]).max(cv).max(out).max(md),
        })
        .max()
        .unwrap_or(0) as usize;
    let gpow = primitives::field::g_powers((max_op + 1).max(2));
    let g_at = |i: u32| gpow[i as usize]; // operand g-power

    // The opcode, then seven operand slots: offsets as g-powers, the `SET` immediate's
    // limbs (c2 in the fpc slot), the `DEREF` store-mode flags, and `BLAKE2s`'s four
    // input words, chaining-value base, output base and metadata cell. Unused slots are zero.
    let row = |op: &Op| -> [F64; 8] {
        let z = F64::ZERO;
        match *op {
            Op::Xor { a, b, c } => [OP_XOR, g_at(a), g_at(b), g_at(c), z, z, z, z],
            Op::Mul { a, b, c } => [OP_MUL, g_at(a), g_at(b), g_at(c), z, z, z, z],
            Op::Set { o, k } => [OP_SET, g_at(o), F64(k.c0), F64(k.c1), F64(k.c2), z, z, z],
            Op::Deref { o1, o2, o3, mode } => [OP_DEREF, g_at(o1), g_at(o2), g_at(o3), mode.f_pc(), mode.f_fp(), z, z],
            Op::Jump { oc, od, of } => [OP_JUMP, g_at(oc), g_at(od), g_at(of), z, z, z, z],
            Op::Blake2s { ins, cv, out, md } => [
                OP_BLAKE2S,
                g_at(ins[0]),
                g_at(ins[1]),
                g_at(ins[2]),
                g_at(ins[3]),
                g_at(cv),
                g_at(out),
                g_at(md),
            ],
        }
    };
    // The program is PUBLIC (not committed): eight public columns over the program
    // cube, embedded in the bytecode seed/finalize blocks below, written in one pass.
    // SAFETY: the pass below writes every slot of every column.
    let mut columns: [Vec<F64>; 8] = std::array::from_fn(|_| unsafe { primitives::uninit_vec(prog.len()) });
    let dst = columns.each_mut().map(|c| parallel::SendPtr(c.as_mut_ptr()));
    parallel::for_each(prog.len(), |i| {
        for (column, value) in dst.iter().zip(row(&prog[i])) {
            // SAFETY: instruction `i` writes slot `i` of each column, in bounds and once.
            unsafe { column.add(i).write(value) };
        }
    });
    columns
}

/// The stacked bytecode polynomial: the eight columns at their bus tuple
/// coordinates, which is what makes the program's whole share of a bus leaf one
/// evaluation at `(ζ, α⃗)` (see [`crate::leaf::stacked_bytecode_table`]).
///
/// This is the multilinear an outermost verifier is handed in place of a
/// structured program, and what the transcript seed binds ([`super::fs_seed`]).
pub fn bytecode_table(prog: &[Op]) -> Vec<F64> {
    let coords = bytecode_columns(prog)
        .map(|c| Coord::Public(std::sync::Arc::new(c)))
        .into();
    let block = Block::full(crate::log2_strict_usize(prog.len()), coords);
    crate::leaf::stacked_bytecode_table(std::slice::from_ref(&block))
}

/// Build the public [`Layout`] from the program, the memory log-size `log_mem`, the
/// instruction tables' row counts `rows`, and the public input `pi`. The flush blocks
/// reference columns only by INDEX and the program only through its public columns, so
/// this needs no committed witness: both prover and verifier reconstruct exactly the
/// same structure.
pub fn layout(prog: &[Op], log_mem: usize, rows: [usize; tables::N_TABLES], pi: [F192; 2]) -> Layout {
    let taus = table_logs(rows);
    let bytecode_size = prog.len();
    let log_bytecode = crate::log2_strict_usize(bytecode_size);

    // Derived boundary: the run starts at (pc,fp) = (0,0) and, by convention, the
    // final pc is the bytecode's last cell g^{B-1} (the compiler emits a halt jump
    // there), with fp returned to 0. All public, no trace needed.
    let final_pc = (bytecode_size - 1) as u32;

    let one = F64::ONE;
    // The bytecode columns map operand *offsets* (small, ≤ frame size) to
    // g-powers (not memory addresses), so precompute only up to the largest
    // operand, an O(1) lookup each, rather than over the whole 2^log_mem memory.
    // Shared between the seed and finalize blocks: at kbc = 19 a copy is tens of
    // megabytes per column.
    let prog_cols: [std::sync::Arc<Vec<F64>>; 8] = bytecode_columns(prog).map(std::sync::Arc::new);

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
    // full three-limb 192-bit word.
    push.push(Block::full(
        log_mem,
        vec![
            Const(SEP_MEM),
            Index,
            Const(one),
            Col(MEM_LO),
            Col(MEM_HI),
            Col(MEM_TOP),
        ],
    ));
    pull.push(Block::full(
        log_mem,
        vec![
            Const(SEP_MEM),
            Index,
            Col(MFCNT),
            Col(MEM_LO),
            Col(MEM_HI),
            Col(MEM_TOP),
        ],
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
    let sch = schema();
    let mut count_blocks: Vec<Block> = Vec::new();
    for (t, table) in tables::tables().iter().enumerate() {
        let base = sch.base[t];
        let padding = table.padding();
        let table_block = |coords: Vec<Coord>| Block {
            kappa: taus[t],
            rows: rows[t],
            padding: coords.iter().map(|c| crate::leaf::coord_at(c, &padding)).collect(),
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

/// Every table's log height: the least that holds its rows.
pub(crate) fn table_logs(rows: [usize; tables::N_TABLES]) -> [usize; tables::N_TABLES] {
    let taus = rows.map(crate::log2_ceil_usize);
    debug_assert_eq!(
        taus[tables::BLAKE2S_TABLE],
        crate::hash_flock::n_blocks_log(rows[tables::BLAKE2S_TABLE].max(1)),
        "the BLAKE2s table is flock's batch"
    );
    taus
}

impl Program {
    pub(crate) fn build(&self, exec: &Execution) -> Witness {
        assert!(self.prog.len().is_power_of_two());
        assert!(exec.mem.len().is_power_of_two());
        // The trace was emitted in the same walk as the memory image (no re-walk).
        let tr = &exec.trace;
        let cells = exec.mem.len();
        let bytecode_size = self.prog.len();
        let log_mem = crate::log2_strict_usize(cells);

        let sch = schema();
        // g^0..g^{span-1}, so every pc/frame/operand/count fill is an O(1) lookup instead
        // of an O(log) power: a frame base or an operand is below the cells the run used.
        // The run's own table covers them unless a count outgrew it.
        let span = exec.mem_used.max(bytecode_size).max(tr.counts);
        let gpow = match exec.gpow.get(..span) {
            Some(gpow) => std::borrow::Cow::Borrowed(gpow),
            None => std::borrow::Cow::Owned(primitives::field::g_powers(span)),
        };

        // The public layout (flush/count blocks, placements, boundary, taus) is a pure
        // function of the program + announced sizes + public input, with no committed
        // witness; reconstruct it here so the prover and verifier share exactly the same
        // structure. It comes before the fill because it fixes each table's height
        // `2^tau`, which lets every column be allocated at its final length in one pass.
        let row_counts = exec.trace.row_counts();
        assert!(
            row_counts.iter().all(|&r| r <= 1 << MAX_LOG_ROWS),
            "a table exceeds 2^{MAX_LOG_ROWS} rows"
        );
        let pi = [exec.mem.word(0), exec.mem.word(1)];
        let l = layout(&self.prog, log_mem, row_counts, pi);

        // The stacked witness is written exactly ONCE: allocate it, carve one window
        // per committed column, and have every fill write its column straight into
        // place. Copying columns in afterwards would move the whole witness a second
        // time, a gigabyte at this scale, for no gain: nothing folds the K-columns
        // in place, so the stack can be their only home.
        //
        // SAFETY: the allocation is uninitialized. `split_stack` zeroes the pad tail
        // and hands out windows tiling the rest; `fill_table` checks that each table
        // wrote every window it was given, and the shared columns below write theirs.
        let mut q = unsafe { witness::alloc_stack(l.shape) };
        // A virtual column is not in the stack, so its values need storage of their
        // own: it carries data for the bus, and only its evaluation claims route
        // elsewhere (to `q_flock`).
        let mut virt: Vec<(usize, Vec<F64>)> = Vec::new();
        for (t, table) in tables::tables().iter().enumerate() {
            for c in 0..table.n_committed_columns() {
                let i = sch.base[t] + c;
                if l.placements[i].is_virtual() {
                    // SAFETY: a virtual window is a table column, `FillCtx::cols_at`
                    // writes every row of every window it is given, and `fill_table`
                    // asserts each table wrote all of its columns.
                    virt.push((i, unsafe { primitives::uninit_vec::<F64>(1 << l.taus[t]) }));
                }
            }
        }
        let mut windows = witness::split_stack(&mut q, &l.placements);
        for (i, buf) in virt.iter_mut() {
            windows[*i] = buf;
        }

        // Each table fills its own columns from the trace (local indices, offset
        // into its global block).
        crate::stage!("Fill columns", || {
            for (t, table) in tables::tables().iter().enumerate() {
                let (base, n) = (sch.base[t], table.n_committed_columns());
                let ctx = FillCtx::new(tr, &exec.mem, &gpow, &self.prog, 1 << l.taus[t], table.padding());
                tables::fill_table(*table, &ctx, &mut windows[base..base + n]);
            }
            // Shared columns. The 192-bit memory image splits into three K-limbs.
            // These five plus `QFLOCK` below are every shared column, and each has to
            // be written: the stack is uninitialized, so one left out would be read
            // as indeterminate bytes rather than caught by a length mismatch.
            const _: () = assert!(N_SHARED == 6, "a new shared column needs a fill here");
            // One pass over the image fills all four of its columns, streamed out a
            // cache line of each at a time: nothing reads them before the commitment.
            const LINE: usize = 8;
            const BLOCK: usize = 1 << 10;
            let page_log = Memory::page_log();
            let image = [MEM_LO, MEM_HI, MEM_TOP, MFCNT].map(|c| {
                assert_eq!(windows[c].len(), cells, "a memory column spans the image");
                parallel::SendPtr(windows[c].as_mut_ptr())
            });
            parallel::for_each_chunk(cells / BLOCK, |first, end| {
                let stream = primitives::stream::Stream::new();
                for b in first..end {
                    let at = b * BLOCK;
                    let page = exec.mem.page(at >> page_log);
                    for line in (at..at + BLOCK).step_by(LINE) {
                        let mut buf = [[F64::ZERO; LINE]; 4];
                        for j in 0..LINE {
                            let i = line + j;
                            let cell = page.map_or(&Cell::UNWRITTEN, |p| &p[i & ((1 << page_log) - 1)]);
                            // counts ended at g^{A[i]}
                            let values = [cell.word.c0, cell.word.c1, cell.word.c2].map(F64);
                            buf[0][j] = values[0];
                            buf[1][j] = values[1];
                            buf[2][j] = values[2];
                            buf[3][j] = gpow[cell.count as usize];
                        }
                        for (column, values) in image.iter().zip(&buf) {
                            // SAFETY: block `b` owns cells `b·BLOCK..(b+1)·BLOCK` of every
                            // column, in bounds as `cells` is a whole number of blocks.
                            unsafe { stream.copy_uninit(column.add(line), values) };
                        }
                    }
                }
            });
            parallel::fill(windows[BFCNT], |i| gpow[tr.bytecode_count[i] as usize]); // … at g^{A[pc]}
        });
        // flock's packed BLAKE2s witness q_flock, ALWAYS committed in this same stack:
        // built from the executed BLAKE2s rows in order (row j = flock instance j),
        // padded to `2^n_blocks_log(max(count,1))` instances with flock's padding
        // instance, which is what the table's padding rows hold.
        let flock_reduction = crate::stage!("Build q_flock", || {
            // The rows carry only their access counts; the compression's input
            // words are the nine cells they read, in the finished (write-once)
            // memory image.
            let blocks: Vec<_> = parallel::map_collect(tr.blake2s.len(), |i| {
                let r = tr.blake2s.get(i);
                let a = tables::blake2s_addresses(&self.prog, r);
                let chunk = |c0: u32, c1: u32| {
                    let (w0, w1) = (exec.mem.word(c0 as usize), exec.mem.word(c1 as usize));
                    [F64(w0.c0), F64(w0.c1), F64(w1.c0), F64(w1.c1)]
                };
                crate::hash_flock::compression(
                    chunk(a[0], a[1]),
                    chunk(a[2], a[3]),
                    chunk(a[4], a[4] + 1),
                    exec.mem.word(a[6] as usize),
                )
            });
            crate::hash_flock::build_qflock_prepared(&blocks, windows[QFLOCK])
        });

        // (`execute` already asserts the run halts at the sentinel (pc, fp) =
        // (g^{B-1}, 0), exactly the boundary the public layout derives.)
        drop(windows); // release the borrow of `q` and of the virtual buffers
        Witness {
            q,
            virt,
            layout: l,
            log_mem,
            flock_reduction,
        }
    }
}
