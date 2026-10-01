//! The public column schema and bus layout: the committed-column indices, and
//! the flush blocks the verifier reconstructs from the program and the
//! announced sizes. Plus the prover-side witness build.

use super::*;
use crate::leaf::SparseColumn;
use crate::rv::{ADVICE_BASE, LOG_REGS, RAM_BASE, TEXT_BASE};
use crate::witness::{Placement, Source};

/// The bus blocks no single table owns, which each side starts with, in this order.
///
/// Each has a push block, which seeds an array (or starts the run).
/// A read-write array also has a pull block of the same height, which finalizes it (or ends the run) with committed columns.
/// The bytecode, which is read-only, has none: its push carries each entry as often as it is read.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Framework {
    /// The run's boundary: it starts at the entry point at cycle 1 and ends on the halt slot.
    State,
    Registers,
    Ram,
    Advice,
    Bytecode,
}

pub const FRAMEWORK: [Framework; 5] = [
    Framework::State,
    Framework::Registers,
    Framework::Ram,
    Framework::Advice,
    Framework::Bytecode,
];

impl Framework {
    /// `log2` of the block's rows: one per cell of the array.
    pub fn log_rows(self, sizes: Sizes) -> usize {
        match self {
            Framework::State => 0,
            Framework::Registers => LOG_REGS,
            Framework::Ram => sizes.log_ram,
            Framework::Advice => sizes.log_advice,
            Framework::Bytecode => sizes.log_bytecode,
        }
    }
}

/// The committed columns no table owns, which come first in the global column order.
///
/// The program is PUBLIC, not committed: it rides the bytecode block as `Coord::Public`,
/// and only the witness-dependent read counts are committed. So are the registers and RAM
/// before the run, zero and the program's image: what is committed is what they hold
/// after it, and each cell's last timestamp (§sec:memchan). The advice is the one array
/// whose initial words are committed as well: they are the prover's.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Shared {
    RegFin,
    /// Each register's final timestamp, the seed's if never accessed.
    RegTs,
    RamFin,
    RamTs,
    AdvInit,
    AdvFin,
    AdvTs,
    /// How many rows read each bytecode entry, an integer below `2^COUNT_BITS`.
    BytecodeReads,
}

pub const SHARED: [Shared; 8] = [
    Shared::RegFin,
    Shared::RegTs,
    Shared::RamFin,
    Shared::RamTs,
    Shared::AdvInit,
    Shared::AdvFin,
    Shared::AdvTs,
    Shared::BytecodeReads,
];

impl Shared {
    /// The column's global index.
    pub const fn col(self) -> usize {
        self as usize
    }

    /// The block whose rows the column has.
    fn block(self) -> Framework {
        match self {
            Shared::RegFin | Shared::RegTs => Framework::Registers,
            Shared::RamFin | Shared::RamTs => Framework::Ram,
            Shared::AdvInit | Shared::AdvFin | Shared::AdvTs => Framework::Advice,
            Shared::BytecodeReads => Framework::Bytecode,
        }
    }

    /// The column's values, from the run.
    fn values(self, tr: &Trace) -> &[F64] {
        match self {
            Shared::RegFin => &tr.reg_fin,
            Shared::RegTs => &tr.reg_ts,
            Shared::RamFin => &tr.ram_fin,
            Shared::RamTs => &tr.ram_ts,
            Shared::AdvInit => &tr.adv_init,
            Shared::AdvFin => &tr.adv_fin,
            Shared::AdvTs => &tr.adv_ts,
            Shared::BytecodeReads => &tr.bytecode_reads,
        }
    }
}

/// Then two packed flock witnesses per table, every class circuit's in table order,
/// then every clock circuit's, committed in the SAME stack as every other column
/// (single PCS): `2^(k_log + tau - 6)` words, the SOLE copy of the circuit's words,
/// whose columns are ports of it (§class_flock).
pub const Q_BASE: usize = SHARED.len();
pub const N_SHARED: usize = Q_BASE + crate::class_flock::N_FLOCKS;

/// The committed column holding packed witness `f`, every class circuit's then every clock circuit's.
pub(crate) const fn q_column(f: usize) -> usize {
    Q_BASE + f
}

/// Global column indexing: the shared columns occupy `0..N_SHARED`, then each
/// table `t` (in [`tables::tables`] order) owns the contiguous span `(base, width)`.
/// Both prover and verifier derive this identically from the table set, so every
/// column claim lines up.
pub struct Schema {
    pub spans: [(usize, usize); tables::N_TABLES],
    pub n: usize,
}

/// The schema is a pure function of the fixed table set, so compute it once.
pub fn schema() -> &'static Schema {
    static SCHEMA: std::sync::OnceLock<Schema> = std::sync::OnceLock::new();
    SCHEMA.get_or_init(|| {
        let mut next = N_SHARED;
        let spans = tables::tables().each_ref().map(|table| {
            let span = (next, table.n_committed_columns());
            next += span.1;
            span
        });
        Schema { spans, n: next }
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
        Coord::Prod(i, j) => Coord::Prod(base + i, base + j),
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
    /// Where each column sits in the stacked witness; from the columns' log-sizes
    /// alone, so reconstructable by the verifier.
    pub placements: Vec<Placement>,
    /// The stacked witness's shape: its announced `2^mu` size, plus how many lane
    /// blocks of it the prover actually commits (see [`witness::StackShape`]).
    pub shape: witness::StackShape,
    pub taus: [usize; tables::N_TABLES],
}

impl Layout {
    /// Packed witness `f`'s window in the stack.
    pub(crate) fn witness_window(&self, f: usize) -> witness::Window {
        self.window(q_column(f))
    }

    /// Committed column `col`'s window in the stack.
    pub(crate) fn window(&self, col: usize) -> witness::Window {
        self.placements[col].window().expect("the column is committed")
    }
}

/// The prover's witness: the stacked multilinear `q`, which holds every committed
/// column at its placed offset, plus the public [`Layout`].
pub(crate) struct Witness {
    pub(crate) q: zk_alloc::ArenaVec<F64>,
    /// The ports' values as `(global column index, values)`. They carry data for the
    /// bus but are not committed, so they are not in `q`.
    pub(crate) virt: Vec<(usize, zk_alloc::ArenaVec<F64>)>,
    pub(crate) layout: Layout,
    /// The clock the run ended on, which the prover announces.
    pub(crate) ts_final: u64,
    /// Each circuit's flock batch, freed right after its reduction.
    pub(crate) reductions: Vec<crate::class_flock::Prepared>,
}

impl Witness {
    /// One read-only view per column, in global column order: the window into the
    /// stack for a committed column, the private buffer for a port.
    pub(crate) fn columns(&self) -> Vec<&[F64]> {
        let mut cols: Vec<&[F64]> = self
            .layout
            .placements
            .iter()
            .map(|p| {
                p.window()
                    .map_or(&[][..], |w| &self.q[w.offset..w.offset + (1 << w.n_vars)])
            })
            .collect();
        for (i, buf) in &self.virt {
            cols[*i] = buf;
        }
        cols
    }

    /// Committed data before the zero-pad to `2^m`: the real witness size.
    pub(crate) fn committed_size(&self) -> usize {
        committed_size(&self.layout.placements)
    }
}

/// The committed columns' total length.
fn committed_size(placements: &[Placement]) -> usize {
    placements
        .iter()
        .filter_map(Placement::window)
        .map(|w| 1usize << w.n_vars)
        .sum()
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

/// Every column's source, in global order: the shared columns at their arrays' sizes,
/// the packed witnesses, then each table's columns at its height. A circuit word is
/// a port of its class's packed witness, which already holds it, so it is never
/// committed again: its bus claims settle against that witness, which is the whole
/// binding.
fn column_sources(sizes: Sizes, taus: [usize; tables::N_TABLES]) -> Vec<Source> {
    use crate::class_flock::{N_FLOCKS, flock, flock_index, stride_log};
    let mut sources: Vec<Source> = SHARED
        .iter()
        .map(|c| Source::Committed(c.block().log_rows(sizes)))
        .collect();
    sources.extend((0..N_FLOCKS).map(|f| {
        let (t, part) = flock(f);
        Source::Committed(taus[t] + stride_log(tables::CLASSES[t], part))
    }));
    for (t, table) in tables::tables().iter().enumerate() {
        let base = sources.len();
        sources.resize(base + table.n_committed_columns(), Source::Committed(taus[t]));
        for part in [tables::Part::Class, tables::Part::Clock] {
            for (port, c) in table.word_columns(part) {
                sources[base + c] = Source::Port {
                    column: q_column(flock_index(t, part)),
                    port,
                    stride_log: stride_log(tables::CLASSES[t], part),
                };
            }
        }
    }
    debug_assert_eq!(sources.len(), schema().n);
    sources
}

/// How many PUBLIC columns a bytecode entry is: the class tag, then `flags, a1, a2,
/// ad, imm, pc4, dt, link, jalr`, a zero verdict, and the exit selector (§sec:e2e-bc).
pub const N_BYTECODE_COLUMNS: usize = tables::EXIT_SLOT - 1;

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
        column(&|_, _| 0),
        column(&|_, e| (e.target == rv::Target::Halt) as u64),
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
    let block = Block::framework(crate::log2_strict_usize(p.entries.len()), coords);
    crate::leaf::stacked_bytecode_table(std::slice::from_ref(&block))
}

/// Build the public [`Layout`] from the program, the tables' log heights `taus` and the
/// clock the prover says the run ended on. The flush blocks reference columns only
/// by INDEX and the program only through its public columns, so this needs no
/// committed witness: both prover and verifier reconstruct exactly the same structure.
///
/// A table's height is its row count: the fill blocks bring every count up to a power of
/// two (`cpu::filler`), so `2^taus[t]` rows were all executed and no flush has padding
/// tuples to divide back out of the bus.
pub fn layout(p: &rv::Program, taus: [usize; tables::N_TABLES], ts_final: u64) -> Layout {
    let sizes = Sizes::of(p);
    // Shared between the seed and finalize blocks: a copy is tens of megabytes per
    // column at production sizes.
    let prog_cols: [std::sync::Arc<Vec<F64>>; N_BYTECODE_COLUMNS] = bytecode_columns(p).map(std::sync::Arc::new);

    let mut push: Vec<Block> = Vec::new();
    let mut pull: Vec<Block> = Vec::new();
    for block in FRAMEWORK {
        let (seed, finalize) = framework_blocks(block, sizes, p, &prog_cols, ts_final);
        push.push(seed);
        pull.extend(finalize);
    }

    // Per-table blocks: each table declares its flushes in local indices; offset them
    // to the table's global columns.
    let sch = schema();
    for (t, table) in tables::tables().iter().enumerate() {
        let (base, kappa) = (sch.spans[t].0, taus[t]);
        let fb = table.flushes();
        push.extend(
            fb.push
                .into_iter()
                .map(|c| Block::table(t, kappa, offset_coords(base, c))),
        );
        pull.extend(
            fb.pull
                .into_iter()
                .map(|c| Block::table(t, kappa, offset_coords(base, c))),
        );
    }

    let (placements, shape) = witness::placements_of(&column_sources(sizes, taus));
    Layout {
        push,
        pull,
        placements,
        shape,
        taus,
    }
}

/// A framework block's push, and its pull if it has one.
fn framework_blocks(
    block: Framework,
    sizes: Sizes,
    p: &rv::Program,
    prog_cols: &[std::sync::Arc<Vec<F64>>; N_BYTECODE_COLUMNS],
    ts_final: u64,
) -> (Block, Option<Block>) {
    use Coord::{Col, Const, IntIndex, Public, Sparse};
    let kappa = block.log_rows(sizes);
    let pair =
        |(push, pull): (Vec<Coord>, Vec<Coord>)| (Block::framework(kappa, push), Some(Block::framework(kappa, pull)));
    // A read-write array: every cell starts at the seed's timestamp holding `init`, and ends at
    // its last timestamp holding its final word (§sec:memchan).
    let array = |sep: F64, cell: Coord, init: Option<Coord>, ts: Shared, fin: Shared| {
        let seed = [Const(sep), cell.clone(), Const(F64(tables::SEED_CLOCK))]
            .into_iter()
            .chain(init)
            .collect();
        (seed, vec![Const(sep), cell, Col(ts.col()), Col(fin.col())])
    };
    let word = |base: u64| IntIndex {
        base: F64(base),
        shift: 3,
    };
    match block {
        // An incorrect clock leaves the terminal tuple unmatched.
        Framework::State => pair((
            vec![
                Const(SEP_STATE),
                Const(F64(p.entry_pc)),
                Const(F64(tables::CLOCK_START)),
                Const(F64::ZERO),
            ],
            vec![
                Const(SEP_STATE),
                Const(F64(p.halt_pc())),
                Const(F64(ts_final)),
                Const(F64(ts_final)),
            ],
        )),
        Framework::Registers => {
            let cell = IntIndex {
                base: F64::ZERO,
                shift: 0,
            };
            pair(array(tables::SEP_REG, cell, None, Shared::RegTs, Shared::RegFin))
        }
        // Cell `z` at its byte address `RAM_BASE + 8z`. What RAM holds before the run is
        // public: the program's image, then zeros.
        Framework::Ram => {
            let image = Sparse(std::sync::Arc::new(SparseColumn::new(p.log_ram, &[(0, &p.image)])));
            pair(array(
                tables::SEP_MEM,
                word(RAM_BASE),
                Some(image),
                Shared::RamTs,
                Shared::RamFin,
            ))
        }
        // The one array seeded from a committed column: the prover's words.
        Framework::Advice => pair(array(
            tables::SEP_MEM,
            word(ADVICE_BASE),
            Some(Col(Shared::AdvInit.col())),
            Shared::AdvTs,
            Shared::AdvFin,
        )),
        // Entry `i` at its `pc`, pushed once per read; the program columns are public.
        Framework::Bytecode => {
            let pc = IntIndex {
                base: F64(TEXT_BASE),
                shift: 2,
            };
            let tuple = [Const(SEP_BYTECODE), pc]
                .into_iter()
                .chain(prog_cols.iter().cloned().map(Public))
                .collect();
            (Block::lookup(kappa, tuple, Shared::BytecodeReads.col()), None)
        }
    }
}

impl Program {
    /// `log2` of the stacked witness a run of these row counts commits: what one proof
    /// can hold is capped ([`pcs::MAX_MU`]), so a run is checked before it is built.
    pub(crate) fn stack_log(&self, row_counts: [usize; tables::N_TABLES]) -> usize {
        self.stack_sizes(row_counts).0
    }

    /// The stack's `log2` and the committed size, before the pad, for these row counts.
    ///
    /// The layout is a function of the program and the row counts alone, so no witness is built.
    pub(crate) fn stack_sizes(&self, row_counts: [usize; tables::N_TABLES]) -> (usize, usize) {
        let taus = row_counts.map(|rows| crate::log2_ceil_usize(rows.max(1)));
        let (placements, shape) = witness::placements_of(&column_sources(Sizes::of(&self.rv), taus));
        (shape.mu, committed_size(&placements))
    }

    pub(crate) fn build(&self, exec: &Execution) -> Witness {
        let p = &self.rv;
        // The trace was emitted in the same walk as the run (no re-walk).
        let tr = &exec.trace;
        let sch = schema();

        // The public layout (flush blocks, placements, boundary, taus) is a pure
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
        let l = layout(p, taus, tr.ts_final);

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
        // A port is not in the stack, so its values need storage of their own: it
        // carries data for the bus, and only its evaluation claims route elsewhere (to
        // its class's packed witness).
        let mut virt: Vec<(usize, zk_alloc::ArenaVec<F64>)> = Vec::new();
        for (t, &(base, width)) in sch.spans.iter().enumerate() {
            for i in base..base + width {
                if l.placements[i].window().is_none() {
                    // SAFETY: a port is a table column, `FillCtx::cols` writes every
                    // row of every window it is given, and `fill_table` asserts each
                    // table wrote all of its columns.
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
                let (base, n) = sch.spans[t];
                let ctx = FillCtx::new(tr, p, 1 << l.taus[t], n);
                tables::fill_table(table, &ctx, &mut windows[base..base + n]);
            }
            // Every shared column has to be written: the stack is uninitialized, so one
            // left out would be read as indeterminate bytes rather than caught by a
            // length mismatch.
            for c in SHARED {
                windows[c.col()].copy_from_slice(c.values(tr));
            }
        });
        // The packed witnesses, one instance per row of their table.
        let reductions = crate::stage!("Build flock witnesses", || {
            (0..crate::class_flock::N_FLOCKS)
                .map(|f| {
                    let rows = &tr.rows[crate::class_flock::flock(f).0];
                    crate::class_flock::Prepared::build(f, rows, &p.entries, windows[q_column(f)])
                })
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
