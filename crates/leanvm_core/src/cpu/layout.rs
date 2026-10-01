//! The public column schema and bus layout: the committed-column indices, and
//! the flush blocks and producers the verifier reconstructs from the program and
//! the announced sizes. Plus the prover-side witness build.

use super::*;
use crate::leaf::SparseColumn;
use crate::rv::{ADVICE_BASE, RAM_BASE, RegisterFile, TEXT_BASE};
use crate::witness::{Placement, Source};

/// The bus blocks no single table owns, which each side starts with, in this order.
///
/// Each has a push and a pull block of the same height: the push seeds an array (or
/// starts the run), the pull finalizes it (or ends the run) with committed columns.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Framework {
    /// The run's boundary: it starts at the entry point at cycle 1 and ends on the halt slot.
    State,
    Registers,
    Ram,
    Advice,
}

pub const FRAMEWORK: [Framework; 4] = [
    Framework::State,
    Framework::Registers,
    Framework::Ram,
    Framework::Advice,
];

impl Framework {
    /// `log2` of the block's rows: one per cell of the array.
    pub const fn log_rows(self, sizes: Sizes) -> usize {
        match self {
            Self::State => 0,
            Self::Registers => RegisterFile::LOG_CELLS,
            Self::Ram => sizes.log_ram,
            Self::Advice => sizes.log_advice,
        }
    }
}

/// The read-only arrays (§sec:lookup), whose table side is a producer rather than a
/// pair of framework blocks, in this order: it pushes every entry as often as it is
/// read, which a committed multiplicity column says.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Lookup {
    Bytecode,
}

pub const LOOKUPS: [Lookup; 1] = [Lookup::Bytecode];

impl Lookup {
    /// `log2` of the array's entries.
    pub const fn log_rows(self, sizes: Sizes) -> usize {
        match self {
            Self::Bytecode => sizes.log_bytecode,
        }
    }

    /// The committed column of how often each entry is read.
    pub const fn multiplicity(self) -> Shared {
        match self {
            Self::Bytecode => Shared::BytecodeMult,
        }
    }
}

/// The committed columns no table owns, which come first in the global column order.
///
/// The program is PUBLIC, not committed: it rides the bytecode producer as `Coord::Public`,
/// and only the witness-dependent multiplicities are committed. So are the registers and RAM
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
    /// How often each bytecode entry is read (§sec:lookup). Entry `x`'s word is the
    /// integer `m_x`, and its bits are the producer's one-bit columns, opened by ring
    /// switching.
    BytecodeMult,
}

pub const SHARED: [Shared; 8] = [
    Shared::RegFin,
    Shared::RegTs,
    Shared::RamFin,
    Shared::RamTs,
    Shared::AdvInit,
    Shared::AdvFin,
    Shared::AdvTs,
    Shared::BytecodeMult,
];

impl Shared {
    /// The column's global index.
    pub const fn col(self) -> usize {
        self as usize
    }

    /// `log2` of the column's rows: one per cell or entry of its array.
    const fn log_rows(self, sizes: Sizes) -> usize {
        match self {
            Self::RegFin | Self::RegTs => Framework::Registers.log_rows(sizes),
            Self::RamFin | Self::RamTs => Framework::Ram.log_rows(sizes),
            Self::AdvInit | Self::AdvFin | Self::AdvTs => Framework::Advice.log_rows(sizes),
            Self::BytecodeMult => Lookup::Bytecode.log_rows(sizes),
        }
    }

    /// The column's values, as the run left them: none for a multiplicity column, which
    /// [`count_reads`] counts from the rows.
    fn values(self, tr: &Trace) -> Option<&[F64]> {
        Some(match self {
            Self::RegFin => &tr.reg_fin,
            Self::RegTs => &tr.reg_ts,
            Self::RamFin => &tr.ram_fin,
            Self::RamTs => &tr.ram_ts,
            Self::AdvInit => &tr.adv_init,
            Self::AdvFin => &tr.adv_fin,
            Self::AdvTs => &tr.adv_ts,
            Self::BytecodeMult => return None,
        })
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
    /// The three lookup arrays' table sides, in [`LOOKUPS`] order (§sec:lookup).
    pub producers: Vec<Producer>,
    /// Where each column sits in the stacked witness; from the columns' log-sizes
    /// alone, so reconstructable by the verifier.
    pub placements: Vec<Placement>,
    /// The stacked witness's shape: its announced `2^mu` size, plus how many lane
    /// blocks of it the prover actually commits (see [`witness::StackShape`]).
    pub shape: witness::StackShape,
    pub taus: [usize; tables::N_TABLES],
    /// Sparse RAM metadata bound before the shared commitment.
    pub(crate) sparse: Option<sparse::Boundary>,
    /// Instruction spans followed by the sparse boundary span when present.
    pub(crate) spans: Vec<(usize, usize)>,
}

impl Layout {
    /// Packed witness `f`'s window in the stack.
    pub(crate) fn witness_window(&self, f: usize) -> witness::Window {
        self.placements[q_column(f)]
            .window()
            .expect("a packed witness is committed")
    }

    /// A producer's multiplicity column's window in the stack.
    pub(crate) fn multiplicity_window(&self, p: &Producer) -> witness::Window {
        self.placements[p.col]
            .window()
            .expect("a multiplicity column is committed")
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
    /// The sparse boundary shares the machine commitment and opening.
    pub(crate) sparse_reduction: Option<sparse::Prepared>,
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
pub(crate) fn committed_size(placements: &[Placement]) -> usize {
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
            log_bytecode: crate::log2_strict_usize(p.entries().len()),
            log_ram: p.log_ram(),
            log_advice: p.log_advice(),
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
    let mut sources: Vec<Source> = SHARED.iter().map(|c| Source::Committed(c.log_rows(sizes))).collect();
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
pub const N_BYTECODE_COLUMNS: usize = tables::EXIT_SLOT + 1 - crate::leaf::BYTECODE_PUBLIC_SLOT;

/// The public bytecode columns over the program cube, in bytecode-slot order. The
/// program is not committed, so these ride the bytecode producer as `Coord::Public` and
/// stack into the polynomial [`bytecode_table`] returns.
pub fn bytecode_columns(p: &rv::Program) -> [Vec<F64>; N_BYTECODE_COLUMNS] {
    let column = |f: &(dyn Fn(usize, &rv::Entry) -> u64 + Sync)| {
        parallel::map_collect(p.entries().len(), |i| F64(f(i, &p.entries()[i])))
    };
    [
        // An illegal entry's tag is zero, which is no table's: nothing can read it.
        parallel::map_collect(p.entries().len(), |i| {
            tables::table_of(p.entries()[i].class).map_or(F64::ZERO, primitives::field::g_pow)
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
        column(&|_, e| (e.is_exit()) as u64),
    ]
}

/// The bytecode's entries as the bus carries them: the separator, entry `i`'s address
/// `TEXT_BASE + 4i`, then the program's public columns.
fn bytecode_tuple(p: &rv::Program) -> Vec<Coord> {
    let pc = Coord::IntIndex {
        base: F64(TEXT_BASE),
        shift: 2,
    };
    [Coord::Const(SEP_BYTECODE), pc]
        .into_iter()
        .chain(bytecode_columns(p).map(|c| Coord::Public(std::sync::Arc::new(c))))
        .collect()
}

/// The stacked bytecode polynomial: the columns at their bus tuple coordinates,
/// which is what makes the program's whole share of a bus leaf one evaluation at
/// `(ζ, α⃗)` (see [`crate::leaf::stacked_bytecode_table`]).
///
/// This is the multilinear an outermost verifier is handed in place of a
/// structured program, and what the program digest binds ([`Program::new`]).
pub fn bytecode_table(p: &rv::Program) -> Vec<F64> {
    crate::leaf::stacked_bytecode_table(crate::log2_strict_usize(p.entries().len()), &bytecode_tuple(p))
}

/// How many bits of its multiplicities each lookup array's producer puts on the bus, in
/// [`LOOKUPS`] order: enough for the most reads the tables of these heights can make of
/// it, every row reading the bytecode once. Completeness only: no read count is too
/// large for soundness.
pub fn multiplicity_bits(taus: [usize; tables::N_TABLES]) -> [usize; LOOKUPS.len()] {
    let rows: u64 = taus.iter().map(|&tau| 1u64 << tau).sum();
    LOOKUPS.map(|lookup| match lookup {
        Lookup::Bytecode => (u64::BITS - rows.leading_zeros()) as usize,
    })
}

/// Build the public [`Layout`] from the program, the tables' log heights `taus` and the
/// clock the prover says the run ended on. The flush blocks reference columns only
/// by INDEX and the program only through its public columns, so this needs no
/// committed witness: both prover and verifier reconstruct exactly the same structure.
///
/// A table's height is its row count: the fill blocks bring every count up to a power of
/// two (`cpu::filler`), so `2^taus[t]` rows were all executed and no flush has padding
/// tuples to divide back out of the bus.
///
/// With a sparse RAM boundary, the dense RAM block shrinks to the image's and the touched cells form a table of their own.
pub(crate) fn layout(
    p: &rv::Program,
    taus: [usize; tables::N_TABLES],
    ts_final: u64,
    sparse: Option<sparse::Boundary>,
) -> Layout {
    let mut sizes = Sizes::of(p);
    if sparse.is_some() {
        sizes.log_ram = sparse::image_log(p);
    }
    let mut push: Vec<Block> = Vec::new();
    let mut pull: Vec<Block> = Vec::new();
    for block in FRAMEWORK {
        let kappa = block.log_rows(sizes);
        let (seed, finalize) = framework_tuples(block, p, ts_final, sizes.log_ram);
        push.push(Block::framework(kappa, seed));
        pull.push(Block::framework(kappa, finalize));
    }

    let mut spans = schema().spans.to_vec();
    let mut sources = column_sources(sizes, taus);
    if let Some(boundary) = sparse {
        let base = schema().n + 1;
        let sep = Coord::Const(sparse::SEP_ORDER);
        // The endpoints force one ascending chain containing every live sparse row.
        push.push(Block::framework(
            0,
            vec![sep.clone(), Coord::Const(F64(sparse::start(p)))],
        ));
        pull.push(Block::framework(0, vec![sep.clone(), Coord::Const(F64(boundary.end))]));
        spans.push((base, sparse::WIDTH));
        sources.push(Source::Committed(boundary.tau + sparse::STRIDE_LOG));
        sources.extend((0..sparse::WIDTH).map(|port| Source::Port {
            column: schema().n,
            port,
            stride_log: sparse::STRIDE_LOG,
        }));
        let col = |port| Coord::Col(base + port);
        // A live cell is seeded with zero at the seed clock, and a padding row at clock zero.
        push.push(Block::table(
            tables::N_TABLES,
            boundary.tau,
            vec![Coord::Const(tables::SEP_MEM), col(1), col(4), Coord::Const(F64::ZERO)],
        ));
        pull.push(Block::table(
            tables::N_TABLES,
            boundary.tau,
            vec![Coord::Const(tables::SEP_MEM), col(1), col(2), col(3)],
        ));
        push.push(Block::table(
            tables::N_TABLES,
            boundary.tau,
            vec![sep.clone(), col(1), col(5)],
        ));
        pull.push(Block::table(
            tables::N_TABLES,
            boundary.tau,
            vec![sep, col(0), Coord::Const(F64::ZERO)],
        ));
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

    let bits = multiplicity_bits(taus);
    let producers = LOOKUPS
        .into_iter()
        .zip(bits)
        .map(|(lookup, bits)| Producer {
            kappa: lookup.log_rows(sizes),
            coords: lookup_tuple(lookup, p),
            col: lookup.multiplicity().col(),
            bits,
        })
        .collect();

    let (placements, shape) = witness::placements_of(&sources);
    Layout {
        push,
        pull,
        producers,
        placements,
        shape,
        taus,
        sparse,
        spans,
    }
}

/// A framework block's two tuples, the push's and the pull's.
fn framework_tuples(block: Framework, p: &rv::Program, ts_final: u64, log_ram: usize) -> (Vec<Coord>, Vec<Coord>) {
    use Coord::{Col, Const, IntIndex, Sparse};
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
        Framework::State => (
            vec![
                Const(SEP_STATE),
                Const(F64(p.entry_pc())),
                Const(F64(tables::CLOCK_START)),
                Const(F64::ZERO),
            ],
            vec![
                Const(SEP_STATE),
                Const(F64(p.halt_pc())),
                Const(F64(ts_final)),
                Const(F64(ts_final)),
            ],
        ),
        Framework::Registers => {
            let cell = IntIndex {
                base: F64::ZERO,
                shift: 0,
            };
            array(tables::SEP_REG, cell, None, Shared::RegTs, Shared::RegFin)
        }
        // Cell `z` at its byte address `RAM_BASE + 8z`. What RAM holds before the run is
        // public: the program's image, then zeros.
        Framework::Ram => {
            let image = Sparse(std::sync::Arc::new(SparseColumn::new(log_ram, &[(0, p.image())])));
            array(
                tables::SEP_MEM,
                word(RAM_BASE),
                Some(image),
                Shared::RamTs,
                Shared::RamFin,
            )
        }
        // The one array seeded from a committed column: the prover's words.
        Framework::Advice => array(
            tables::SEP_MEM,
            word(ADVICE_BASE),
            Some(Col(Shared::AdvInit.col())),
            Shared::AdvTs,
            Shared::AdvFin,
        ),
    }
}

/// A lookup array's entries, the tuple its producer pushes (§sec:lookup), none of it
/// committed.
fn lookup_tuple(lookup: Lookup, p: &rv::Program) -> Vec<Coord> {
    match lookup {
        // Entry `i` at its `pc`; the program columns are public.
        Lookup::Bytecode => bytecode_tuple(p),
    }
}

impl Program {
    /// The layout a proof of this run commits to, known without building its witness.
    pub(crate) fn run_layout(&self, exec: &Execution) -> Layout {
        let taus = exec.trace.row_counts().map(|rows| crate::log2_ceil_usize(rows.max(1)));
        layout(
            &self.rv,
            taus,
            exec.trace.ts_final,
            sparse::boundary(&self.rv, &exec.trace),
        )
    }

    pub(crate) fn build(&self, exec: &Execution) -> Witness {
        let p = &self.rv;
        // The trace was emitted in the same walk as the run (no re-walk).
        let tr = &exec.trace;
        let sch = schema();

        // The public layout (flush blocks, producers, placements, boundary, taus) is a pure
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
        let l = layout(p, taus, tr.ts_final, sparse::boundary(p, tr));

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
        if let Some(boundary) = l.sparse {
            for i in schema().n + 1..schema().n + 1 + sparse::WIDTH {
                // SAFETY: every port buffer is filled from the packed circuit witness below.
                virt.push((i, unsafe {
                    zk_alloc::ArenaVec::<F64>::uninitialized(1 << boundary.tau)
                }));
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
            // length mismatch. What the run did not leave, the multiplicities, is
            // counted from its rows.
            for c in SHARED {
                if let Some(values) = c.values(tr) {
                    let window = &mut windows[c.col()];
                    window.copy_from_slice(&values[..window.len()]);
                }
            }
            count_reads(tr, windows[Lookup::Bytecode.multiplicity().col()]);
        });
        // The packed witnesses, one instance per row of their table.
        let reductions = crate::stage!("Build flock witnesses", || {
            (0..crate::class_flock::N_FLOCKS)
                .map(|f| {
                    let rows = &tr.rows[crate::class_flock::flock(f).0];
                    crate::class_flock::Prepared::build(f, rows, p.entries(), windows[q_column(f)])
                })
                .collect()
        });

        let sparse_reduction = l.sparse.map(|boundary| {
            let prepared = crate::stage!("Build RAM boundary witness", || {
                sparse::Prepared::build(p, tr, boundary, windows[schema().n])
            });
            let stride = 1 << sparse::STRIDE_LOG;
            let base = schema().n + 1;
            for row in 0..1 << boundary.tau {
                for port in 0..sparse::WIDTH {
                    windows[base + port][row] = windows[schema().n][row * stride + port];
                }
            }
            prepared
        });

        drop(windows); // release the borrow of `q` and of the virtual buffers
        Witness {
            q,
            virt,
            layout: l,
            ts_final: tr.ts_final,
            reductions,
            sparse_reduction,
        }
    }
}

/// How often each bytecode entry is read, once by every row: each entry's word is that
/// count as an integer.
fn count_reads(tr: &Trace, bc: &mut [F64]) {
    bc.fill(F64::ZERO);
    for r in tr.rows.iter().flatten() {
        bc[r.index as usize].0 += 1;
    }
}
