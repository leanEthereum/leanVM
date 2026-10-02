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
    /// Where each column sits in the committed stack; from the columns' sizes
    /// alone, so reconstructable by the verifier.
    pub placements: Vec<Placement>,
    /// The committed stack's shape: its announced `2^mu` size, plus how many lane
    /// blocks of it the prover actually commits (see [`witness::StackShape`]).
    pub shape: witness::StackShape,
    /// Each table's announced height, its live rows (§sec:jagged).
    pub heights: [usize; tables::N_TABLES],
    /// Each table's `log2` row count as proven, its height padded.
    pub taus: [usize; tables::N_TABLES],
}

impl Layout {
    /// Packed witness `f`'s column in the stack.
    pub(crate) fn witness_column(&self, f: usize) -> &witness::Column {
        self.placements[q_column(f)]
            .column()
            .expect("a packed witness is committed")
    }

    /// A producer's multiplicity column in the stack.
    pub(crate) fn multiplicity_column(&self, p: &Producer) -> &witness::Column {
        self.placements[p.col]
            .column()
            .expect("a multiplicity column is committed")
    }

    /// Whether table `t` has padding rows: rows past its height, which repeat the
    /// row at its height and which the bus leaves out.
    pub(crate) const fn padded(&self, t: usize) -> bool {
        self.heights[t] < 1 << self.taus[t]
    }
}

/// A table's `log2` row count as proven: its height padded to a power of two, and to
/// flock's instance floor.
pub fn tau_of(t: usize, height: usize) -> usize {
    crate::class_flock::n_blocks_log(tables::CLASSES[t], height)
}

/// The rows a table's columns commit: its live rows, then the first padding row, which
/// every later one repeats (§sec:jagged).
pub const fn committed_rows(height: usize, tau: usize) -> usize {
    if height < 1 << tau { height + 1 } else { 1 << tau }
}

/// The prover's witness: the committed stack `q`, the live stack of the columns that
/// commit only some of their rows (which the bus and the table sumcheck read, the
/// others being read in `q`), and the public [`Layout`].
pub(crate) struct Witness {
    pub(crate) q: zk_alloc::ArenaVec<F64>,
    pub(crate) live: zk_alloc::ArenaVec<F64>,
    /// Each column's window in `live`.
    pub(crate) windows: Vec<Option<witness::Window>>,
    /// The ports' values as `(global column index, values)`. They carry data for the
    /// bus but are not committed, so they are not in `q`.
    pub(crate) virt: Vec<(usize, zk_alloc::ArenaVec<F64>)>,
    pub(crate) layout: Layout,
    /// The clock the run ended on, which the prover announces.
    pub(crate) ts_final: u64,
    /// Every circuit's flock batch, freed right after the batched reduction.
    pub(crate) reductions: Vec<crate::class_flock::Prepared>,
}

impl Witness {
    /// One read-only view per column, in global column order: a table's column at its
    /// [`committed_rows`], every later row repeating the last (its window in the live
    /// stack, its piece of the committed stack when it is committed whole, or the
    /// private buffer of a port), a shared column whole. A packed witness's is empty,
    /// its flock batch holding its words.
    pub(crate) fn columns(&self) -> Vec<&[F64]> {
        let mut cols: Vec<&[F64]> = (self.windows.iter().zip(&self.layout.placements))
            .map(|(w, p)| match (w, p.column()) {
                (Some(w), _) => &self.live[w.offset..w.offset + w.len],
                (None, Some(c)) if c.stride_log == 0 => {
                    debug_assert_eq!(c.pieces.len(), 1, "a column without a window is committed whole");
                    &self.q[c.pieces[0].offset..c.pieces[0].offset + (1 << c.row_vars)]
                }
                (None, _) => &[],
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
        .filter_map(Placement::column)
        .map(witness::Column::committed_len)
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
/// the packed witnesses, then each table's columns at its height. A table's columns and
/// packed witnesses commit [`committed_rows`] of their rows (§sec:jagged). A circuit
/// word is a port of its class's packed witness, which already holds it, so it is
/// never committed again: its bus claims settle against that witness, which is the
/// whole binding.
fn column_sources(sizes: Sizes, heights: [usize; tables::N_TABLES]) -> Vec<Source> {
    use crate::class_flock::{N_FLOCKS, flock, flock_index, stride_log};
    let taus: [usize; tables::N_TABLES] = std::array::from_fn(|t| tau_of(t, heights[t]));
    let jagged = |t: usize, stride_log: usize| Source::Committed {
        row_vars: taus[t],
        stride_log,
        rows: committed_rows(heights[t], taus[t]),
    };
    let mut sources: Vec<Source> = SHARED.iter().map(|c| Source::full(c.log_rows(sizes))).collect();
    sources.extend((0..N_FLOCKS).map(|f| {
        let (t, part) = flock(f);
        jagged(t, stride_log(tables::CLASSES[t], part))
    }));
    for (t, table) in tables::tables().iter().enumerate() {
        let base = sources.len();
        sources.resize(base + table.n_committed_columns(), jagged(t, 0));
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

/// Build the public [`Layout`] from the program, the tables' announced heights and the
/// clock the prover says the run ended on. The flush blocks reference columns only
/// by INDEX and the program only through its public columns, so this needs no
/// committed witness: both prover and verifier reconstruct exactly the same structure.
///
/// A table's rows past its height are padding (§sec:jagged): they repeat the row at its
/// height, and its bus blocks take the identity there, so the bus is over its live rows.
pub fn layout(p: &rv::Program, heights: [usize; tables::N_TABLES], ts_final: u64) -> Layout {
    let sizes = Sizes::of(p);
    let taus: [usize; tables::N_TABLES] = std::array::from_fn(|t| tau_of(t, heights[t]));
    let mut push: Vec<Block> = Vec::new();
    let mut pull: Vec<Block> = Vec::new();
    for block in FRAMEWORK {
        let kappa = block.log_rows(sizes);
        let (seed, finalize) = framework_tuples(block, p, ts_final);
        push.push(Block::framework(kappa, seed));
        pull.push(Block::framework(kappa, finalize));
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

    let (placements, shape) = witness::placements_of(&column_sources(sizes, heights));
    Layout {
        push,
        pull,
        producers,
        placements,
        shape,
        heights,
        taus,
    }
}

/// A framework block's two tuples, the push's and the pull's.
fn framework_tuples(block: Framework, p: &rv::Program, ts_final: u64) -> (Vec<Coord>, Vec<Coord>) {
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
            let image = Sparse(std::sync::Arc::new(SparseColumn::new(p.log_ram(), &[(0, p.image())])));
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
    /// `log2` of the stacked witness a run of these table heights commits: what one
    /// proof can hold is capped ([`pcs::MAX_MU`]), so a run is checked before it is built.
    pub(crate) fn stack_log(&self, heights: [usize; tables::N_TABLES]) -> usize {
        self.stack_sizes(heights).0
    }

    /// The stack's `log2` and the committed size, before the pad, for these heights.
    ///
    /// The layout is a function of the program and the heights alone, so no witness is built.
    pub(crate) fn stack_sizes(&self, heights: [usize; tables::N_TABLES]) -> (usize, usize) {
        let (placements, shape) = witness::placements_of(&column_sources(Sizes::of(&self.rv), heights));
        (shape.mu, committed_size(&placements))
    }

    pub(crate) fn build(&self, exec: &Execution) -> Witness {
        let p = &self.rv;
        // The trace was emitted in the same walk as the run (no re-walk).
        let tr = &exec.trace;
        let sch = schema();

        // The public layout (flush blocks, producers, placements, boundary, taus) is a pure
        // function of the program and the announced sizes, with no committed witness;
        // reconstruct it here so the prover and verifier share exactly the same
        // structure. It comes before the fill because it fixes each table's committed
        // rows, which lets every column be allocated at its final length in one pass.
        assert!(
            tr.heights.iter().all(|&h| h <= 1 << MAX_LOG_ROWS),
            "a table exceeds 2^{MAX_LOG_ROWS} rows"
        );
        let l = layout(p, tr.heights, tr.ts_final);
        // The executor wrote each table's live rows, then the padding row every later
        // row repeats (`cpu::padding`): its committed rows.
        let rows: [usize; tables::N_TABLES] = std::array::from_fn(|t| committed_rows(tr.heights[t], l.taus[t]));
        for (t, table_rows) in tr.rows.iter().enumerate() {
            assert_eq!(
                table_rows.len(),
                rows[t],
                "the {} table is not its committed rows",
                tables::CLASSES[t].name
            );
        }

        // The committed stack and the live stack are each written exactly ONCE:
        // allocate them, carve out every piece and every window, and have every fill
        // write straight into place. A column that commits only some of its rows is
        // written at those rows, and each copied into its piece while it is in cache;
        // one committed whole is written into its piece alone.
        //
        // SAFETY: both allocations are uninitialized. `split_pieces` hands out pieces
        // tiling `q` but its zeroed tail, `split_stack` windows tiling all of `live`;
        // `fill_table` checks that each table wrote every column it was given, the
        // shared columns below write theirs, and each flock batch its pieces.
        let (live_windows, live_len) = witness::live_windows(&column_sources(Sizes::of(p), tr.heights));
        let mut live = unsafe { witness::alloc_live(live_len) };
        let mut q = unsafe { zk_alloc::ArenaVec::<F64>::uninitialized(l.shape.committed_len()) };
        // A port is not in the stack, so its values need storage of their own: it
        // carries data for the bus, and only its evaluation claims route elsewhere (to
        // its class's packed witness).
        let mut virt: Vec<(usize, zk_alloc::ArenaVec<F64>)> = Vec::new();
        for (t, &(base, width)) in sch.spans.iter().enumerate() {
            for i in base..base + width {
                if l.placements[i].column().is_none() {
                    // SAFETY: a port is a table column, `FillCtx::cols` writes every
                    // row of every window it is given, and `fill_table` asserts each
                    // table wrote all of its columns.
                    virt.push((i, unsafe { zk_alloc::ArenaVec::<F64>::uninitialized(rows[t]) }));
                }
            }
        }
        let (pieces, tail) = witness::split_pieces(&mut q, &l.placements);
        parallel::chunks_mut(tail, 1 << 16, |_, chunk| chunk.fill(F64::ZERO));
        // Each column's pieces as `(first row, piece)`.
        let mut pieces: Vec<Vec<(usize, &mut [F64])>> = (pieces.into_iter().zip(&l.placements))
            .map(|(pieces, p)| {
                p.column()
                    .map_or_else(Vec::new, |c| c.pieces.iter().map(|p| p.first_row).zip(pieces).collect())
            })
            .collect();
        let flocks: Vec<Vec<(usize, &mut [F64])>> = (0..crate::class_flock::N_FLOCKS)
            .map(|f| std::mem::take(&mut pieces[q_column(f)]))
            .collect();
        let mut windows = witness::split_stack(&mut live, &live_windows);
        let mut outs: Vec<tables::ColumnOut<'_>> = (windows.iter_mut().zip(pieces))
            .map(|(window, mut pieces)| {
                if window.is_empty() && pieces.len() == 1 {
                    // Committed whole: its one piece is the column.
                    tables::ColumnOut {
                        rows: pieces.pop().expect("one piece").1,
                        pieces,
                    }
                } else {
                    tables::ColumnOut {
                        rows: std::mem::take(window),
                        pieces,
                    }
                }
            })
            .collect();
        for (i, buf) in virt.iter_mut() {
            outs[*i].rows = buf;
        }

        // Each table fills its own columns from the trace (local indices, offset
        // into its global block).
        crate::stage!("Fill columns", || {
            for (t, table) in tables::tables().iter().enumerate() {
                let (base, n) = sch.spans[t];
                let ctx = FillCtx::new(tr, p, rows[t], n);
                tables::fill_table(table, &ctx, &mut outs[base..base + n]);
            }
            // Every shared column has to be written: the stack is uninitialized, so one
            // left out would be read as indeterminate bytes rather than caught by a
            // length mismatch. What the run did not leave, the multiplicities, is
            // counted from its rows.
            for c in SHARED {
                if let Some(values) = c.values(tr) {
                    outs[c.col()].rows.copy_from_slice(values);
                }
            }
            count_reads(tr, outs[Lookup::Bytecode.multiplicity().col()].rows);
        });
        drop(outs); // release the borrows of the stacks and of the virtual buffers
        // The packed witnesses, one instance per committed row of their table, each
        // writing its committed pieces in place.
        let reductions: Vec<crate::class_flock::Prepared> = crate::stage!("Build flock witnesses", || {
            (flocks.into_iter().enumerate())
                .map(|(f, pieces)| {
                    let t = crate::class_flock::flock(f).0;
                    crate::class_flock::Prepared::build(f, l.taus[t], &tr.rows[t], p.entries(), pieces)
                })
                .collect()
        });
        Witness {
            q,
            live,
            windows: live_windows,
            virt,
            layout: l,
            ts_final: tr.ts_final,
            reductions,
        }
    }
}

/// How often each bytecode entry is read by a live row: each entry's word is that count
/// as an integer. A padding row is not on the bus, so it reads nothing.
fn count_reads(tr: &Trace, bc: &mut [F64]) {
    bc.fill(F64::ZERO);
    for (rows, &height) in tr.rows.iter().zip(&tr.heights) {
        for r in &rows[..height] {
            bc[r.index as usize].0 += 1;
        }
    }
}
