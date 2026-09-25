//! The public column schema and bus layout: the committed-column indices, and
//! the flush/count blocks the verifier reconstructs from the program and the
//! announced sizes. Plus the prover-side witness build.

use super::*;
use crate::leaf::SparseColumn;
use crate::rv::{ADVICE_BASE, INPUT_WORDS, LOG_REGS, RAM_BASE, TEXT_BASE};

// ---- column schema -----------------------------------------------------------

// Shared committed columns (indices `0..N_SHARED`). The program is PUBLIC, not
// committed: it rides the bytecode seed/finalize blocks as `Coord::Public`; only the
// witness-dependent finalize counts are committed. So are the registers and RAM before
// the run, zero and the program's image: what is committed is what they hold after it,
// and each cell's last timestamp (§sec:memchan). The advice is the one array whose
// initial words are committed as well: they are the prover's.
pub const REG_FIN: usize = 0;
pub const REG_FTS: usize = 1; // per-register final timestamp g^y, g^0 if never accessed
pub const MEM_FIN: usize = 2;
pub const MFTS: usize = 3;
pub const ADV_INIT: usize = 4;
pub const ADV_FIN: usize = 5;
pub const ADV_FTS: usize = 6;
pub const BFCNT: usize = 7; // per-pc bytecode execution count, g^{A[pc]}
// Per-entry read counts of the two range arrays (§sec:rangecheck).
pub const RLO_CNT: usize = 8;
pub const RHI_CNT: usize = 9;
/// Then one packed flock witness per table, committed in the SAME stack as every
/// other column (single PCS): `2^(k_log + tau - 6)` words, the SOLE copy of the
/// table's circuit words, whose columns are virtual and route their claims here
/// (§class_flock).
pub const Q_BASE: usize = 10;
pub const N_SHARED: usize = Q_BASE + tables::N_TABLES;

/// The committed column holding table `t`'s packed witness.
pub(crate) const fn q_column(t: usize) -> usize {
    Q_BASE + t
}

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
/// program and the announced sizes, with no witness values. The flush blocks
/// reference columns by INDEX (see [`crate::leaf::Coord`]), so they are pure public
/// structure.
pub struct Layout {
    pub push: Vec<Block>,
    pub pull: Vec<Block>,
    /// Count channel: the lookups' read-count columns, whose product must be nonzero (§sec:lookup).
    pub count: Vec<Block>,
    /// Per-column placement (offset + n_vars) in the stacked witness; from the
    /// columns' log-sizes alone, so reconstructable by the verifier.
    pub placements: Vec<witness::Placement>,
    /// The stacked witness's shape: its announced `2^mu` size, plus how many lane
    /// blocks of it the prover actually commits (see [`witness::StackShape`]).
    pub shape: witness::StackShape,
    pub taus: [usize; tables::N_TABLES],
}

/// The prover's witness: the stacked multilinear `q`, which holds every committed
/// column at its placed offset, plus the public [`Layout`].
pub(crate) struct Witness {
    pub(crate) q: zk_alloc::ArenaVec<F64>,
    /// The virtual columns' values as `(global column index, values)`. They carry
    /// data for the bus but are not committed, so they are not in `q`.
    pub(crate) virt: Vec<(usize, zk_alloc::ArenaVec<F64>)>,
    pub(crate) layout: Layout,
    /// The clock the run ended on, which the prover announces.
    pub(crate) ts_final: F64,
    /// Each table's flock batch, freed right after its reduction.
    pub(crate) reductions: Vec<crate::class_flock::Prepared>,
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

/// The program's sizes the layout depends on: `log2` of its entries, of RAM's words,
/// and of the advice's.
#[derive(Clone, Copy)]
pub struct Sizes {
    pub log_bytecode: usize,
    pub log_ram: usize,
    pub log_advice: usize,
}

impl Sizes {
    pub fn of(p: &rv::Program) -> Self {
        Self {
            log_bytecode: crate::log2_strict_usize(p.entries.len()),
            log_ram: p.log_ram,
            log_advice: p.log_advice,
        }
    }
}

/// The committed columns' kappa SOURCES. Per committed column: `Some((source, adj))` with
/// kappa = value(source) + adj, where source 0 is the constant 0 (kappa = adj; used for
/// the fixed-size columns and the program's sizes, which the caller passes), and
/// source 1 + t is tau_t. `None` = virtual (never committed). `col_kappas` is derived
/// from this, so the two cannot drift apart.
pub fn col_kappa_sources(sizes: Sizes) -> Vec<Option<(usize, usize)>> {
    let sch = schema();
    let mut k = vec![Some((0usize, 0usize)); sch.n];
    k[REG_FIN] = Some((0, LOG_REGS));
    k[REG_FTS] = Some((0, LOG_REGS));
    k[MEM_FIN] = Some((0, sizes.log_ram));
    k[MFTS] = Some((0, sizes.log_ram));
    k[ADV_INIT] = Some((0, sizes.log_advice));
    k[ADV_FIN] = Some((0, sizes.log_advice));
    k[ADV_FTS] = Some((0, sizes.log_advice));
    k[BFCNT] = Some((0, sizes.log_bytecode));
    k[RLO_CNT] = Some((0, tables::RANGE_LOG));
    k[RHI_CNT] = Some((0, tables::RANGE_LOG));
    for (t, table) in tables::tables().iter().enumerate() {
        let base = sch.base[t];
        k[base..base + table.n_committed_columns()].fill(Some((1 + t, 0)));
        // The circuit's words are ALWAYS virtual: the class's packed witness already
        // holds them at fixed packed slots, so committing them again is redundant.
        // Their bus claims route directly to slot evaluations of it (`slot_claims`),
        // which is the whole binding.
        k[q_column(t)] = Some((1 + t, crate::class_flock::stride_log(tables::CLASSES[t])));
        for (_, c) in tables::word_columns(t) {
            k[base + c] = None;
        }
    }
    k
}

/// The framework blocks a side starts with, as `(source, adj)`: the state boundary, the
/// registers, RAM, the advice, the bytecode, the two range arrays.
fn framework_kappa_sources(sizes: Sizes) -> Vec<(usize, usize)> {
    vec![
        (0, 0),
        (0, LOG_REGS),
        (0, sizes.log_ram),
        (0, sizes.log_advice),
        (0, sizes.log_bytecode),
        (0, tables::RANGE_LOG),
        (0, tables::RANGE_LOG),
    ]
}

/// The bus flush blocks' kappa SOURCES, flattened in side order (push, pull,
/// count) exactly as the blocks are constructed below: per block
/// `(source, adj)` with kappa = value(source) + adj, source 0 = the constant
/// 0, 1 + t = tau_t. Keep in lockstep with the block construction in [`fn@layout`].
pub fn block_kappa_sources(sizes: Sizes) -> Vec<(usize, usize)> {
    let mut push = framework_kappa_sources(sizes);
    let mut pull = push.clone();
    let mut count = Vec::new();
    for (t, table) in tables::tables().iter().enumerate() {
        let mut fb = tables::FlushBuilder::new();
        table.flushes(&mut fb);
        push.extend(std::iter::repeat_n((1 + t, 0), fb.push.len()));
        pull.extend(std::iter::repeat_n((1 + t, 0), fb.pull.len()));
        count.extend(std::iter::repeat_n((1 + t, 0), table.count_columns().len()));
    }
    push.extend(pull);
    push.extend(count);
    push
}

/// Column → log-size (`kappa`) map, derived from [`col_kappa_sources`] by
/// substituting the announced sizes. `None` marks a **virtual** (uncommitted) column.
/// Depends only on the public sizes, so the verifier can reconstruct the placements.
fn col_kappas(sizes: Sizes, taus: [usize; tables::N_TABLES]) -> Vec<Option<usize>> {
    let mut values = vec![0usize];
    values.extend(taus);
    col_kappa_sources(sizes)
        .iter()
        .map(|s| s.map(|(source, adj)| values[source] + adj))
        .collect()
}

/// How many PUBLIC columns a bytecode entry is: the class tag, then `flags, a1, a2,
/// ad, imm, pc4, dt, link, jalr` (§sec:e2e-bc).
pub const N_BYTECODE_COLUMNS: usize = 10;

/// The public bytecode columns over the program cube, in bytecode-slot order. The
/// program is not committed, so these ride the seed/finalize blocks as
/// `Coord::Public` and stack into the polynomial [`bytecode_table`] returns.
pub fn bytecode_columns(p: &rv::Program) -> [Vec<F64>; N_BYTECODE_COLUMNS] {
    let column = |f: &(dyn Fn(usize, &rv::Entry) -> u64 + Sync)| {
        parallel::map_collect(p.entries.len(), |i| F64(f(i, &p.entries[i])))
    };
    [
        // An illegal entry's tag is zero, which is no table's: nothing can read it.
        parallel::map_collect(p.entries.len(), |i| {
            tables::table_of(p.entries[i].class).map_or(F64::ZERO, primitives::field::g_pow)
        }),
        column(&|_, e| e.flags),
        column(&|_, e| e.a1 as u64),
        column(&|_, e| e.a2 as u64),
        column(&|_, e| e.ad as u64),
        column(&|_, e| e.imm),
        column(&|i, _| p.pc_of(i).wrapping_add(4)),
        column(&|i, _| p.dt_of(i)),
        column(&|_, e| e.link as u64),
        column(&|_, e| e.jalr as u64),
    ]
}

/// The stacked bytecode polynomial: the columns at their bus tuple coordinates,
/// which is what makes the program's whole share of a bus leaf one evaluation at
/// `(ζ, α⃗)` (see [`crate::leaf::stacked_bytecode_table`]).
///
/// This is the multilinear an outermost verifier is handed in place of a
/// structured program, and what the program digest binds ([`Program::new`]).
pub fn bytecode_table(p: &rv::Program) -> Vec<F64> {
    let coords = bytecode_columns(p)
        .map(|c| Coord::Public(std::sync::Arc::new(c)))
        .into();
    let block = Block {
        kappa: crate::log2_strict_usize(p.entries.len()),
        coords,
    };
    crate::leaf::stacked_bytecode_table(std::slice::from_ref(&block))
}

/// Build the public [`Layout`] from the program, the run's public input, the tables' log
/// heights `taus` and the clock the prover says the run ended on. The flush blocks reference columns only
/// by INDEX and the program only through its public columns, so this needs no
/// committed witness: both prover and verifier reconstruct exactly the same structure.
///
/// A table's height is its row count: the fill blocks bring every count up to a power of
/// two (`cpu::filler`), so `2^taus[t]` rows were all executed and no flush has padding
/// tuples to divide back out of the bus.
pub fn layout(p: &rv::Program, input: &[u64; INPUT_WORDS], taus: [usize; tables::N_TABLES], ts_final: F64) -> Layout {
    let sizes = Sizes::of(p);
    let log_bytecode = sizes.log_bytecode;
    let one = F64::ONE;
    // Shared between the seed and finalize blocks: a copy is tens of megabytes per
    // column at production sizes.
    let prog_cols: [std::sync::Arc<Vec<F64>>; N_BYTECODE_COLUMNS] = bytecode_columns(p).map(std::sync::Arc::new);

    // ---- bus blocks ----
    use Coord::{Col, Const, IntIndex, Powers, Public, Sparse};
    let blk = |kappa: usize, coords: Vec<Coord>| Block { kappa, coords };

    let mut push: Vec<Block> = Vec::new();
    let mut pull: Vec<Block> = Vec::new();

    // Shared blocks (cross-instruction infra, not owned by any single table). The
    // boundary: the run starts at the entry point at cycle 1 and ends on the halt
    // slot, at whatever clock the prover announced (`ts_final`), which nothing has to
    // check: a wrong one unbalances the bus.
    push.push(blk(
        0,
        vec![Const(SEP_STATE), Const(F64(p.entry_pc)), Const(tables::CLOCK_START)],
    ));
    pull.push(blk(0, vec![Const(SEP_STATE), Const(F64(p.halt_pc())), Const(ts_final)]));
    // Register seed + finalize: every register starts at timestamp g^0 holding zero,
    // and ends at its last timestamp holding its final word (§sec:memchan).
    let cell = IntIndex {
        base: F64::ZERO,
        shift: 0,
    };
    push.push(blk(LOG_REGS, vec![Const(tables::SEP_REG), cell.clone(), Const(one)]));
    pull.push(blk(
        LOG_REGS,
        vec![Const(tables::SEP_REG), cell, Col(REG_FTS), Col(REG_FIN)],
    ));
    // RAM the same way, cell `z` at its byte address `RAM_BASE + 8z`. What it holds
    // before the run is public: the input, the program's image, zeros.
    let word = IntIndex {
        base: F64(RAM_BASE),
        shift: 3,
    };
    let ram = SparseColumn::new(p.log_ram, &[(0, input), (INPUT_WORDS, &p.image)]);
    push.push(blk(
        p.log_ram,
        vec![
            Const(tables::SEP_MEM),
            word.clone(),
            Const(one),
            Sparse(std::sync::Arc::new(ram)),
        ],
    ));
    pull.push(blk(
        p.log_ram,
        vec![Const(tables::SEP_MEM), word, Col(MFTS), Col(MEM_FIN)],
    ));
    // The advice, the one array seeded from a committed column: the prover's words.
    let word = IntIndex {
        base: F64(ADVICE_BASE),
        shift: 3,
    };
    push.push(blk(
        p.log_advice,
        vec![Const(tables::SEP_MEM), word.clone(), Const(one), Col(ADV_INIT)],
    ));
    pull.push(blk(
        p.log_advice,
        vec![Const(tables::SEP_MEM), word, Col(ADV_FTS), Col(ADV_FIN)],
    ));
    // Bytecode seed + finalize, entry `i` at its `pc` (the program columns are public).
    let bytecode_block = |count: Coord| {
        let pc = IntIndex {
            base: F64(TEXT_BASE),
            shift: 2,
        };
        blk(
            log_bytecode,
            [Const(SEP_BYTECODE), pc, count]
                .into_iter()
                .chain(prog_cols.iter().cloned().map(Public))
                .collect(),
        )
    };
    push.push(bytecode_block(Const(one)));
    pull.push(bytecode_block(Col(BFCNT)));
    // The two range arrays (§sec:rangecheck): entries with no value, so a read is a
    // range check on its address. Neither is committed: their addresses are
    // geometric, `g^{j+1}` and `g^{-2^16·j}`.
    for (sep, first, ratio, count) in [
        (tables::SEP_RANGE_LO, tables::range_lo_first(), F64::G, RLO_CNT),
        (tables::SEP_RANGE_HI, one, tables::range_hi_ratio(), RHI_CNT),
    ] {
        let addresses = Powers { first, ratio };
        push.push(blk(tables::RANGE_LOG, vec![Const(sep), addresses.clone(), Const(one)]));
        pull.push(blk(tables::RANGE_LOG, vec![Const(sep), addresses, Col(count)]));
    }
    debug_assert_eq!(push.len(), framework_kappa_sources(sizes).len());

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

    let (placements, shape) = witness::placements_of(&col_kappas(sizes, taus));
    Layout {
        push,
        pull,
        count: count_blocks,
        placements,
        shape,
        taus,
    }
}

impl Program {
    /// `log2` of the stacked witness a run of these row counts commits: what one proof
    /// can hold is capped ([`pcs::MAX_MU`]), so a run is checked before it is built.
    pub(crate) fn stack_log(&self, row_counts: [usize; tables::N_TABLES]) -> usize {
        let taus = row_counts.map(|rows| crate::log2_ceil_usize(rows.max(1)));
        witness::placements_of(&col_kappas(Sizes::of(&self.rv), taus)).1.mu
    }

    pub(crate) fn build(&self, exec: &Execution, input: &[u64; INPUT_WORDS]) -> Witness {
        let p = &self.rv;
        // The trace was emitted in the same walk as the run (no re-walk).
        let tr = &exec.trace;
        let sch = schema();

        // The public layout (flush/count blocks, placements, boundary, taus) is a pure
        // function of the program and the announced sizes, with no committed witness;
        // reconstruct it here so the prover and verifier share exactly the same
        // structure. It comes before the fill because it fixes each table's height
        // `2^tau`, which lets every column be allocated at its final length in one pass.
        let row_counts = tr.row_counts();
        assert!(
            row_counts.iter().all(|&r| r <= 1 << MAX_LOG_ROWS),
            "a table exceeds 2^{MAX_LOG_ROWS} rows"
        );
        // Every table's rows are real rows, so its height IS its row count: the fill
        // blocks ran each count up to a power of two, and up to flock's instance floor
        // as well (`cpu::filler`).
        let taus: [usize; tables::N_TABLES] = std::array::from_fn(|t| {
            let r = row_counts[t];
            assert!(
                r.is_power_of_two(),
                "a table has {r} rows, not a power of two: the fill blocks did not fill it (cpu::filler)"
            );
            let tau = crate::log2_strict_usize(r);
            assert_eq!(
                tau,
                crate::class_flock::n_blocks_log(tables::CLASSES[t], r),
                "the {} table must be filled to flock's instance floor",
                tables::CLASSES[t].name
            );
            tau
        });
        let l = layout(p, input, taus, tr.ts_final);
        // The range arrays' addresses, to turn a gap's chunks into column values.
        let range_lo = primitives::field::geometric(tables::range_lo_first(), F64::G, 1 << tables::RANGE_LOG);
        let range_hi = primitives::field::geometric(F64::ONE, tables::range_hi_ratio(), 1 << tables::RANGE_LOG);

        // The stacked witness is written exactly ONCE: allocate it, carve one window
        // per committed column, and have every fill write its column straight into
        // place. Copying columns in afterwards would move the whole witness a second
        // time for no gain: nothing folds the K-columns in place, so the stack can be
        // their only home.
        //
        // SAFETY: the allocation is uninitialized. `split_stack` zeroes the pad tail
        // and hands out windows tiling the rest; `fill_table` checks that each table
        // wrote every window it was given, and the shared columns below write theirs.
        let mut q = unsafe { witness::alloc_stack(l.shape) };
        // A virtual column is not in the stack, so its values need storage of their
        // own: it carries data for the bus, and only its evaluation claims route
        // elsewhere (to its class's packed witness).
        let mut virt: Vec<(usize, zk_alloc::ArenaVec<F64>)> = Vec::new();
        for (t, table) in tables::tables().iter().enumerate() {
            for c in 0..table.n_committed_columns() {
                let i = sch.base[t] + c;
                if l.placements[i].is_virtual() {
                    // SAFETY: a virtual window is a table column, `FillCtx::cols`
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
                let ctx = FillCtx::new(tr, &range_lo, &range_hi, p, 1 << l.taus[t], n);
                tables::fill_table(*table, &ctx, &mut windows[base..base + n]);
            }
            // Shared columns. These ten plus the flock witnesses below are every
            // shared column, and each has to be written: the stack is uninitialized, so
            // one left out would be read as indeterminate bytes rather than caught by
            // a length mismatch.
            const _: () = assert!(Q_BASE == 10, "a new shared column needs a fill here");
            windows[REG_FIN].copy_from_slice(&tr.reg_fin);
            windows[REG_FTS].copy_from_slice(&tr.reg_ts);
            windows[MEM_FIN].copy_from_slice(&tr.ram_fin);
            windows[MFTS].copy_from_slice(&tr.ram_ts);
            windows[ADV_INIT].copy_from_slice(&tr.adv_init);
            windows[ADV_FIN].copy_from_slice(&tr.adv_fin);
            windows[ADV_FTS].copy_from_slice(&tr.adv_ts);
            windows[BFCNT].copy_from_slice(&tr.bytecode_count); // counts ended at g^{A[pc]}
            windows[RLO_CNT].copy_from_slice(&tr.range_lo_count);
            windows[RHI_CNT].copy_from_slice(&tr.range_hi_count);
        });
        // The classes' packed witnesses, one instance per row of their table.
        let reductions = crate::stage!("Build flock witnesses", || {
            (0..tables::N_TABLES)
                .map(|t| crate::class_flock::Prepared::build(t, &tr.rows[t], &p.entries, windows[q_column(t)]))
                .collect()
        });

        drop(windows); // release the borrow of `q` and of the virtual buffers
        Witness {
            q,
            virt,
            layout: l,
            ts_final: tr.ts_final,
            reductions,
        }
    }
}
