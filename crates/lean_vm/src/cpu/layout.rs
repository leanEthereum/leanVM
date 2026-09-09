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
}

/// The prover's witness: the stacked multilinear `q`, which holds every committed
/// column at its placed offset, plus the public [`Layout`] (and the sizes needed to
/// announce it).
pub(crate) struct Witness {
    pub(crate) q: zk_alloc::ArenaVec<F64>,
    /// The virtual columns' values as `(global column index, values)`. They carry
    /// data for the bus but are not committed, so they are not in `q`.
    pub(crate) virt: Vec<(usize, zk_alloc::ArenaVec<F64>)>,
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
    // n_blocks_log (the announced-size certification uses the same floor), so this
    // reproduces `qflock_kappa`.
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

/// Build the public [`Layout`] from the program, the memory log-size `log_mem`, the
/// instruction tables' log heights `taus`, and the public input `pi`. The flush blocks
/// reference columns only by INDEX and the program only through its public columns, so
/// this needs no committed witness: both prover and verifier reconstruct exactly the same
/// structure.
///
/// A table's height is its row count: the fill blocks bring every count up to a power of
/// two (`cpu::filler`), so `2^taus[t]` rows were all executed and no flush has padding
/// tuples to divide back out of the bus.
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

    let opcode = |op: &Op| match op {
        Op::Xor { .. } => OP_XOR,
        Op::Mul { .. } => OP_MUL,
        Op::Set { .. } => OP_SET,
        Op::Deref { .. } => OP_DEREF,
        Op::Jump { .. } => OP_JUMP,
        Op::Blake2s { .. } => OP_BLAKE2S,
    };
    let operands = |op: &Op| -> (F64, F64, F64) {
        match *op {
            Op::Xor { a, b, c } | Op::Mul { a, b, c } => (g_at(a), g_at(b), g_at(c)),
            // The immediate's first two K-limbs ride operand slots o2/o3; c2
            // rides the fpc slot below.
            Op::Set { o, k } => (g_at(o), F64(k.c0), F64(k.c1)),
            Op::Deref { o1, o2, o3, .. } => (g_at(o1), g_at(o2), g_at(o3)),
            Op::Jump { oc, od, of } => (g_at(oc), g_at(od), g_at(of)),
            // BLAKE2s's first three input-word offsets; the last two ride the
            // fpc/ffp bytecode slots below.
            Op::Blake2s { ins, .. } => (g_at(ins[0]), g_at(ins[1]), g_at(ins[2])),
        }
    };
    // The 4th/5th bytecode operand slots: the two DEREF store-mode flags, or
    // BLAKE2s's remaining input word / chaining-value base (0 elsewhere).
    let fpc = |op: &Op| match op {
        Op::Deref { mode, .. } => mode.f_pc(),
        Op::Blake2s { ins, .. } => g_at(ins[3]),
        Op::Set { k, .. } => F64(k.c2),
        _ => F64::ZERO,
    };
    let ffp = |op: &Op| match op {
        Op::Deref { mode, .. } => mode.f_fp(),
        Op::Blake2s { cv, .. } => g_at(*cv),
        _ => F64::ZERO,
    };
    // The 6th/7th bytecode operand slots: BLAKE2s's output base and its metadata
    // cell (0 elsewhere).
    let extra0 = |op: &Op| match op {
        Op::Blake2s { out, .. } => g_at(*out),
        _ => F64::ZERO,
    };
    let extra1 = |op: &Op| match op {
        Op::Blake2s { md, .. } => g_at(*md),
        _ => F64::ZERO,
    };
    // The program is PUBLIC (not committed): eight public columns over the
    // program cube, embedded in the bytecode seed/finalize blocks below.
    let column = |f: &(dyn Fn(&Op) -> F64 + Sync)| parallel::map_collect(prog.len(), |i| f(&prog[i]));
    let prog_op: Vec<F64> = column(&opcode);
    let prog_o1: Vec<F64> = column(&|o| operands(o).0);
    let prog_o2: Vec<F64> = column(&|o| operands(o).1);
    let prog_o3: Vec<F64> = column(&|o| operands(o).2);
    let prog_fpc: Vec<F64> = column(&fpc);
    let prog_ffp: Vec<F64> = column(&ffp);
    let prog_extra0: Vec<F64> = column(&extra0);
    let prog_extra1: Vec<F64> = column(&extra1);
    [
        prog_op,
        prog_o1,
        prog_o2,
        prog_o3,
        prog_fpc,
        prog_ffp,
        prog_extra0,
        prog_extra1,
    ]
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
    let block = Block {
        kappa: crate::log2_strict_usize(prog.len()),
        coords,
    };
    crate::leaf::stacked_bytecode_table(std::slice::from_ref(&block))
}

pub fn layout(prog: &[Op], log_mem: usize, taus: [usize; tables::N_TABLES], pi: [F192; 2]) -> Layout {
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
    let blk = |kappa: usize, coords: Vec<Coord>| Block { kappa, coords };

    let mut push: Vec<Block> = Vec::new();
    let mut pull: Vec<Block> = Vec::new();

    // Shared blocks (cross-instruction infra, not owned by any single table).
    // boundary state.
    push.push(blk(0, vec![Const(SEP_STATE), Const(one), Const(one)]));
    pull.push(blk(
        0,
        vec![Const(SEP_STATE), Const(g_pow(final_pc as usize)), Const(one)],
    ));
    // memory seed + finalize (every address real, no padding). The value is the
    // full three-limb 192-bit word.
    push.push(blk(
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
    pull.push(blk(
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
        blk(
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
        let kappa = taus[t];
        let mut fb = FlushBuilder::new();
        table.flushes(&mut fb);
        for coords in fb.push {
            push.push(blk(kappa, offset_coords(base, coords)));
        }
        for coords in fb.pull {
            pull.push(blk(kappa, offset_coords(base, coords)));
        }
        for &c in table.count_columns() {
            count_blocks.push(blk(kappa, vec![Col(base + c)]));
        }
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
    }
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
        // Precompute g^0..g^{span-1} once so every address/pc/operand fill is an
        // O(1) lookup instead of an O(log) power.
        let span = cells.max(bytecode_size);
        let gpow = primitives::field::g_powers(span);

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
        // Every table's rows are real rows, so its height IS its row count: the fill
        // blocks ran each count up to a power of two, and BLAKE2s up to flock's instance
        // floor as well (`cpu::filler`).
        let taus = row_counts.map(|r| {
            assert!(
                r.is_power_of_two(),
                "a table has {r} rows, not a power of two: the fill blocks did not fill \
                 it (cpu::filler)"
            );
            crate::log2_strict_usize(r)
        });
        assert_eq!(
            taus[tables::BLAKE2S_TABLE],
            crate::hash_flock::n_blocks_log(row_counts[tables::BLAKE2S_TABLE]),
            "the BLAKE2s table must be filled to flock's instance floor"
        );
        let pi = [exec.mem[0], exec.mem[1]];
        let l = layout(&self.prog, log_mem, taus, pi);

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
        let mut virt: Vec<(usize, zk_alloc::ArenaVec<F64>)> = Vec::new();
        for (t, table) in tables::tables().iter().enumerate() {
            for c in 0..table.n_committed_columns() {
                let i = sch.base[t] + c;
                if l.placements[i].is_virtual() {
                    // SAFETY: a virtual window is a table column, `FillCtx::cols_at`
                    // writes every row of every window it is given, and `fill_table`
                    // asserts each table wrote all of its columns.
                    virt.push((i, unsafe { zk_alloc::ArenaVec::<F64>::uninitialized(1 << l.taus[t]) }));
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
                let ctx = FillCtx::new(tr, &exec.mem, &gpow, &self.prog, 1 << l.taus[t]);
                tables::fill_table(*table, &ctx, &mut windows[base..base + n]);
            }
            // Shared columns. The 192-bit memory image splits into three K-limbs.
            // These five plus `QFLOCK` below are every shared column, and each has to
            // be written: the stack is uninitialized, so one left out would be read
            // as indeterminate bytes rather than caught by a length mismatch.
            const _: () = assert!(N_SHARED == 6, "a new shared column needs a fill here");
            parallel::fill(windows[MEM_LO], |i| F64(exec.mem[i].c0));
            parallel::fill(windows[MEM_HI], |i| F64(exec.mem[i].c1));
            parallel::fill(windows[MEM_TOP], |i| F64(exec.mem[i].c2));
            parallel::fill(windows[MFCNT], |i| tr.mem_count[i]); // counts ended at g^{A[i]}
            parallel::fill(windows[BFCNT], |i| tr.bytecode_count[i]); // … at g^{A[pc]}
        });
        // flock's packed BLAKE2s witness q_flock, ALWAYS committed in this same stack:
        // built from the executed BLAKE2s rows in order (row j = flock instance j),
        // padded to `2^n_blocks_log(max(count,1))` all-padding instances, so a
        // program with no BLAKE2s still carries a single padding instance.
        let flock_reduction = crate::stage!("Build q_flock", || {
            // The rows carry only their access counts; the compression's input
            // words are the nine cells they read, in the finished (write-once)
            // memory image.
            let blocks: Vec<_> = parallel::map_collect(tr.blake2s.len(), |i| {
                let r = &tr.blake2s[i];
                let a = tables::blake2s_addresses(&self.prog, r);
                let chunk = |c0: u32, c1: u32| {
                    let (w0, w1) = (exec.mem[c0 as usize], exec.mem[c1 as usize]);
                    [F64(w0.c0), F64(w0.c1), F64(w1.c0), F64(w1.c1)]
                };
                crate::hash_flock::compression(
                    chunk(a[0], a[1]),
                    chunk(a[2], a[3]),
                    chunk(a[4], a[4] + 1),
                    exec.mem[a[6] as usize],
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
