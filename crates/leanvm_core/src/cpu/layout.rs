//! The public column schema and layout: the committed-column indices, and the
//! bus blocks and reads the verifier reconstructs from the program + announced
//! sizes and public input. Plus the prover-side witness build.

use super::*;
use crate::shout::{self, MAX_READS, N_CHUNKS};

// ---- column schema -----------------------------------------------------------

// Shared committed columns (indices `0..N_SHARED`). The program (opcode +
// operands) is PUBLIC, not committed: the bytecode reads look it up directly.
// The data-memory image, a 192-bit word per cell committed as three K-lane columns.
pub const MEM_LO: usize = 0;
pub const MEM_HI: usize = 1;
pub const MEM_TOP: usize = 2;
// flock's packed BLAKE2s witness `q_flock`, committed in the SAME stack as every
// other column (single PCS). Size `2^(K_LOG+n_log-6)` F64 words, always ≥ 1
// instance (a no-BLAKE2s program commits one full padding instance). It is the
// SOLE copy of the input/output words: the VM's BLAKE2s value columns are
// virtual and their claims route to `q_flock` slots (§hash_flock), so
// nothing duplicates them. flock's R1CS validity is discharged by the single
// stacked WHIR opening over this commitment.
pub const QFLOCK: usize = 3;
// Table `t`'s one-hot address bits, packed (`crate::shout`): column `HOT + t`.
pub const HOT: usize = 4;
pub const N_SHARED: usize = HOT + tables::N_TABLES;

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
    /// The memory and bytecode lookups (§sec:shout).
    pub shout: shout::Shape,
    /// The stacked bytecode polynomial ([`bytecode_table`]), which the bytecode
    /// reads look up.
    pub bytecode: Vec<F64>,
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
    pub(crate) q: Vec<F64>,
    /// The virtual columns' values as `(global column index, values)`. They carry
    /// data for the table sumcheck but are not committed, so they are not in `q`.
    pub(crate) virt: Vec<(usize, Vec<F64>)>,
    /// `addrs[t][row][read]`: the entry each read of each row looks up.
    pub(crate) addrs: [Vec<[u32; MAX_READS]>; tables::N_TABLES],
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
/// adj; used for the fixed-size columns), source 1 is log_mem, source 2 + t is
/// tau_t, and source 2 + N_TABLES + t is tau_t + chunk_bits - LOG_PACKING, the
/// packed log-size of one chunk table of table t. `None` = virtual (never
/// committed). `col_kappas` is derived from this, so the two cannot drift apart.
pub fn col_kappa_sources() -> Vec<Option<(usize, usize)>> {
    let sch = schema();
    let mut k = vec![Some((0usize, 0usize)); sch.n];
    k[MEM_LO] = Some((1, 0));
    k[MEM_HI] = Some((1, 0));
    k[MEM_TOP] = Some((1, 0));
    // q_flock is `2^(K_LOG + n_blocks_log - LOG_PACKING)` F64 words, always ≥ 1
    // instance (a no-BLAKE2s program commits one padding instance), and tau_5 IS
    // n_blocks_log (the announced-size certification uses the same floor), so this
    // reproduces `qflock_kappa`.
    k[QFLOCK] = Some((2 + tables::BLAKE2S_TABLE, flock::hash::K_LOG - ::pcs::LOG_PACKING));
    for (t, reads) in tables::reads().iter().enumerate() {
        let slabs = crate::log2_ceil_usize(N_CHUNKS * reads.len());
        k[HOT + t] = Some((2 + tables::N_TABLES + t, slabs));
    }
    for (t, table) in tables::tables().iter().enumerate() {
        let base = sch.base[t];
        k[base..base + table.n_committed_columns()].fill(Some((2 + t, 0)));
    }
    // The BLAKE2s value columns are ALWAYS virtual: `q_flock` already holds those
    // words at fixed packed slots, so committing them again is redundant. Their
    // claims route directly to `q_flock` slot evaluations (`slot_claims`),
    // which both binds them to the proven witness AND removes the separate
    // value-binding sub-protocol.
    let b3 = sch.base[tables::BLAKE2S_TABLE];
    for &c in &tables::BLAKE2S_VALUE_COLS {
        k[b3 + c] = None;
    }
    k
}

/// The bus blocks' kappa SOURCES, flattened in side order (push, pull) exactly as
/// the blocks are constructed below: per block `(source, adj)` with kappa =
/// value(source) + adj, source 0 = the constant 0, 2 + t = tau_t. For the
/// recursion guest's in-circuit pin of every block kappa. Keep in lockstep with
/// the block construction in [`fn@layout`].
pub fn block_kappa_sources() -> Vec<(usize, usize)> {
    let side = std::iter::once((0, 0)).chain((0..tables::N_TABLES).map(|t| (2 + t, 0)));
    side.clone().chain(side).collect()
}

/// The chunk width the prover announces: the narrowest whose [`N_CHUNKS`] chunks
/// cover both arrays' addresses.
pub fn chunk_bits(log_mem: usize, log_bytecode: usize) -> usize {
    log_mem.max(log_bytecode).div_ceil(N_CHUNKS).max(1)
}

/// Column → log-size (`kappa`) map, derived from [`col_kappa_sources`] by
/// substituting the announced sizes. `None` marks a **virtual** (uncommitted)
/// column. Depends only on the public sizes, so the verifier can reconstruct the
/// placements.
fn col_kappas(log_mem: usize, taus: [usize; tables::N_TABLES], chunk_bits: usize) -> Vec<Option<usize>> {
    let mut values = vec![0usize, log_mem];
    values.extend(taus);
    values.extend(taus.map(|tau| tau + chunk_bits - shout::LOG_PACKING));
    col_kappa_sources()
        .iter()
        .map(|s| s.map(|(source, adj)| values[source] + adj))
        .collect()
}

/// `log2` of the stacked witness the announced sizes imply. The one part of
/// [`layout`] a size floor needs, and far cheaper than the rest of it.
pub(crate) fn committed_log(log_mem: usize, log_bytecode: usize, taus: [usize; tables::N_TABLES]) -> usize {
    crate::witness::placements_of(&col_kappas(log_mem, taus, chunk_bits(log_mem, log_bytecode)))
        .1
        .mu
}

/// The eight PUBLIC bytecode columns over the program cube, in bytecode-slot
/// order: the opcode, then seven operand/immediate slots. The program is not
/// committed: these stack into the polynomial [`bytecode_table`] returns.
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
    // program cube.
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

/// The stacked bytecode polynomial: the eight columns at their tuple
/// coordinates, which is what makes a bytecode read's whole entry one
/// evaluation at `(r, α⃗)` (see [`crate::shout::stacked_bytecode_table`]).
///
/// This is the multilinear an outermost verifier is handed in place of a
/// structured program, and what the transcript seed binds ([`super::fs_seed`]).
pub fn bytecode_table(prog: &[Op]) -> Vec<F64> {
    shout::stacked_bytecode_table(&bytecode_columns(prog))
}

/// Build the public [`Layout`] from the program, the memory log-size `log_mem`, the
/// instruction tables' log heights `taus`, the chunk width `chunk_bits` and the public
/// input `pi`. The blocks and reads reference columns only by INDEX and the program only
/// through its public polynomial, so this needs no committed witness: both prover and
/// verifier reconstruct exactly the same structure.
///
/// A table's height is its row count: the fill blocks bring every count up to a power of
/// two (`cpu::filler`), so `2^taus[t]` rows were all executed and no flush has padding
/// tuples to divide back out of the bus.
pub fn layout(
    prog: &[Op],
    log_mem: usize,
    taus: [usize; tables::N_TABLES],
    chunk_bits: usize,
    pi: [F192; 2],
) -> Layout {
    let bytecode_size = prog.len();
    let log_bytecode = crate::log2_strict_usize(bytecode_size);

    // Derived boundary: the run starts at (pc,fp) = (0,0) and, by convention, the
    // final pc is the bytecode's last cell g^{B-1} (the compiler emits a halt jump
    // there), with fp returned to 0. All public, no trace needed.
    let final_pc = bytecode_size - 1;

    use Coord::Const;
    let blk = |kappa: usize, coords: Vec<Coord>| Block { kappa, coords };
    let mut push = vec![blk(0, vec![Const(F64::ONE), Const(F64::ONE)])];
    let mut pull = vec![blk(0, vec![Const(g_pow(final_pc)), Const(F64::ONE)])];

    // Per-table blocks and reads: each table declares them in local indices;
    // offset them to the table's global columns.
    let sch = schema();
    let mut reads: [Vec<tables::Read>; tables::N_TABLES] = Default::default();
    for (t, table) in tables::tables().iter().enumerate() {
        let base = sch.base[t];
        let mut fb = FlushBuilder::new();
        table.flushes(&mut fb);
        for coords in fb.push {
            push.push(blk(taus[t], offset_coords(base, coords)));
        }
        for coords in fb.pull {
            pull.push(blk(taus[t], offset_coords(base, coords)));
        }
        reads[t] = fb
            .reads
            .into_iter()
            .map(|read| tables::Read {
                array: read.array,
                tuple: offset_coords(base, read.tuple),
            })
            .collect();
    }

    let (placements, shape) = witness::placements_of(&col_kappas(log_mem, taus, chunk_bits));
    let shout = shout::Shape {
        log_size: [log_mem, log_bytecode],
        chunk_bits,
        taus,
        reads,
        spans: std::array::from_fn(|t| (sch.base[t], tables::tables()[t].n_committed_columns())),
        hot_offsets: std::array::from_fn(|t| placements[HOT + t].offset),
    };
    Layout {
        push,
        pull,
        shout,
        bytecode: bytecode_table(prog),
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

        // The public layout (blocks, reads, placements, boundary, taus) is a pure
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
        let log_bytecode = crate::log2_strict_usize(bytecode_size);
        let l = layout(&self.prog, log_mem, taus, chunk_bits(log_mem, log_bytecode), pi);

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
        // own: it carries data for the table sumcheck, and only its evaluation claims
        // route elsewhere (to `q_flock`).
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
        let mut addrs: [Vec<[u32; MAX_READS]>; tables::N_TABLES] = Default::default();
        crate::stage!("Fill columns", || {
            for (t, table) in tables::tables().iter().enumerate() {
                let (base, n) = (sch.base[t], table.n_committed_columns());
                let ctx = FillCtx::new(tr, &exec.mem, &gpow, &self.prog, 1 << l.taus[t]);
                tables::fill_table(*table, &ctx, &mut windows[base..base + n]);
                let n_reads = l.shout.reads[t].len();
                addrs[t] = parallel::map_collect(1 << l.taus[t], |row| {
                    let mut out = [0u32; MAX_READS];
                    table.read_addrs(&ctx, row, &mut out[..n_reads]);
                    out
                });
            }
            // Shared columns. The 192-bit memory image splits into three K-limbs.
            // These, `QFLOCK` and the one-hot columns below are every shared column,
            // and each has to be written: the stack is uninitialized, so one left out
            // would be read as indeterminate bytes rather than caught by a length
            // mismatch.
            const _: () = assert!(
                N_SHARED == 4 + tables::N_TABLES,
                "a new shared column needs a fill here"
            );
            parallel::fill(windows[MEM_LO], |i| F64(exec.mem[i].c0));
            parallel::fill(windows[MEM_HI], |i| F64(exec.mem[i].c1));
            parallel::fill(windows[MEM_TOP], |i| F64(exec.mem[i].c2));
        });
        // The one-hot address bits: chunk table `c` of a table is one slab, in which
        // word `u + 2^m·y` holds, for the 64 rows `x = 64·y + b`, bit `b` set where row
        // `x` reads position `u`. A slab past the table's chunk tables is the padding
        // of their count to a power of two.
        crate::stage!("Fill one-hot", || {
            for (t, rows) in addrs.iter().enumerate() {
                let n_chunk_tables = N_CHUNKS * l.shout.reads[t].len();
                let m = l.shout.chunk_bits;
                let slab = 1usize << (l.taus[t] - shout::LOG_PACKING + m);
                parallel::chunks_mut(windows[HOT + t], slab, |c, words| {
                    words.fill(F64::ZERO);
                    if c < n_chunk_tables {
                        for (x, row) in rows.iter().enumerate() {
                            let u = l.shout.chunk(row[c / N_CHUNKS], c % N_CHUNKS);
                            words[((x >> shout::LOG_PACKING) << m) + u].0 |= 1 << (x % 64);
                        }
                    }
                });
            }
        });
        // flock's packed BLAKE2s witness q_flock, ALWAYS committed in this same stack:
        // built from the executed BLAKE2s rows in order (row j = flock instance j),
        // padded to `2^n_blocks_log(max(count,1))` all-padding instances, so a
        // program with no BLAKE2s still carries a single padding instance.
        let flock_reduction = crate::stage!("Build q_flock", || {
            // The compression's input words are the nine cells a row reads, in the
            // finished (write-once) memory image.
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
            addrs,
            layout: l,
            log_mem,
            flock_reduction,
        }
    }
}
