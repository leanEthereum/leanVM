//! The public proof structure: the global column order, the bus blocks, the producers, the memory logs, and where every
//! claim lands.
//!
//! The verifier rebuilds it from the program and the prover's announced sizes, with no witness value.
//!
//! Each enum's declaration order is protocol order: reordering a variant changes the proof layout.

use super::error::CpuError;
use super::execute::{Trace, padding_row};
use super::filler::FillBlocks;
use super::{MAX_LOG_ROWS, UNGROUND_LOG_BYTECODE};
use crate::class_flock::FlockId;
use crate::constraints::{BitColumns, Claims};
use crate::leaf::{Block, ColumnClaim, Coord, Producer, PublicColumn};
use crate::memory::{CHUNK_BITS, Kind, LogOpening, LogShape, Regions, Slot};
use crate::pcs::{Rate, RingSwitch, SliceClaim, StackClaim};
use crate::rv::{Entry, Reg, Region, RiscvProgram};
use crate::tables::{ClassTable, N_TABLES, PerTable, Separator, TableId};
use crate::witness::{Placement, Source, StackShape, Window};
use crate::{class_flock, witness};
use Coord::{Const, Public};
use fiat_shamir::MAX_GRINDING_BITS;
use fiat_shamir::transcript::{ProverState, Receiver, Transmitter, VerifierState};
use primitives::field::{F64, F192, g_pow};
use std::sync::{Arc, OnceLock};

// The largest text grinds within the proof of work's window.
const _: () = assert!(Region::TEXT.max_log_words() - UNGROUND_LOG_BYTECODE <= MAX_GRINDING_BITS as usize);

/// The bus blocks no table owns: the run's boundary, a push block and a pull block of one row.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Framework {
    /// The run starts at the entry point at positions one, and ends on the halt slot at the announced positions.
    State,
}

impl Framework {
    /// Every framework block, in bus order.
    pub const ALL: [Self; 1] = [Self::State];

    /// The final state's slots holding the announced positions: the register log's `g^C`, then the memory log's `g^M`.
    pub(crate) const FINAL_POSITIONS: [usize; 2] = [2, 3];

    /// The block's two tuples: the push side's start, then the pull side's end.
    ///
    /// The end's positions are zero here: the verifier adds the announced ones' share itself.
    fn tuples(self, p: &RiscvProgram) -> (Vec<Coord>, Vec<Coord>) {
        let state = Separator::State.coordinate();
        let [zero, one] = [F64::ZERO, F64::ONE].map(Const);
        match self {
            Self::State => (
                vec![
                    state.clone(),
                    Const(F64(p.entry_pc())),
                    one.clone(),
                    one.clone(),
                    zero.clone(),
                ],
                vec![state, Const(F64(p.halt_pc())), zero.clone(), zero, one],
            ),
        }
    }
}

/// The memory logs, in bus order (§sec:memchan).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Log {
    /// The register file: a row per cycle, its two reads and its write.
    Registers,
    /// RAM and the advice: a row per access.
    Memory,
}

impl Log {
    /// Every log, in bus order.
    pub const ALL: [Self; 2] = [Self::Registers, Self::Memory];

    /// The fewest rows a log has: its packed flags fill a word.
    pub const MIN_LOG_ROWS: usize = CHUNK_BITS;

    /// The height of a log of `live` rows.
    pub const fn log_rows(live: usize) -> usize {
        let log = live.next_power_of_two().trailing_zeros() as usize;
        if log > Self::MIN_LOG_ROWS {
            log
        } else {
            Self::MIN_LOG_ROWS
        }
    }

    /// The log's shape at `2^log_rows` rows.
    ///
    /// A table's row pulls the register cycle `(sep, a1, time, a2, ad, v1, v2, vd)`, a memory access `(sep, address, position
    /// g^k, old, new)`: the logs push the same tuples.
    pub(crate) fn shape(self, regions: &Regions, log_rows: usize) -> LogShape {
        let (slots, kind) = match self {
            Self::Registers => (
                vec![
                    Slot::Flagged {
                        base: Separator::Registers.value(),
                        delta: Separator::Registers.value() + Separator::Pointer.value(),
                    },
                    Slot::Address(0),
                    Slot::Time,
                    Slot::Address(1),
                    Slot::Address(2),
                    Slot::Read(0),
                    Slot::Read(1),
                    Slot::Written(2),
                ],
                Kind::Registers {
                    outputs: std::iter::once(&Reg::SYSCALL)
                        .chain(&Reg::OUTPUTS)
                        .map(|r| r.index())
                        .collect(),
                },
            ),
            Self::Memory => (
                vec![
                    Separator::Memory.coordinate_value(),
                    Slot::Address(0),
                    Slot::Time,
                    Slot::Read(0),
                    Slot::Written(0),
                ],
                Kind::Memory(regions.clone()),
            ),
        };
        LogShape { log_rows, slots, kind }
    }

    /// The log's committed column: each group's chunks' one-hot words, then the increments, `2^log_rows` words each.
    pub const fn column(self) -> Shared {
        match self {
            Self::Registers => Shared::RegisterLog,
            Self::Memory => Shared::MemoryLog,
        }
    }
}

impl Separator {
    /// The separator as a log's constant slot.
    const fn coordinate_value(self) -> Slot {
        Slot::Const(self.value())
    }
}

/// RAM and the advice as the memory log's cells.
pub(crate) fn regions(p: &RiscvProgram) -> Regions {
    let bases = [Region::RAM.base(), Region::ADVICE.base()];
    Regions::new(bases, p.log_ram(), p.log_advice(), p.image())
}

/// The read-only arrays (§sec:lookup).
///
/// Their table side is a producer, which pushes every entry as often as its committed multiplicity says.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Lookup {
    /// The program: one entry per instruction slot.
    Bytecode,
    /// The tuples padding rows pull from the logs: they are at position zero, which no log row has.
    Padding,
}

impl Lookup {
    /// Every lookup array, in producer order.
    pub const ALL: [Self; 2] = [Self::Bytecode, Self::Padding];

    /// The base-two logarithm of the array's entries.
    pub const fn log_rows(self, sizes: Sizes) -> usize {
        match self {
            Self::Bytecode => sizes.log_bytecode,
            Self::Padding => sizes.log_padding,
        }
    }

    /// The committed column of how often each entry is read.
    pub const fn multiplicity(self) -> Shared {
        match self {
            Self::Bytecode => Shared::BytecodeMult,
            Self::Padding => Shared::PaddingMult,
        }
    }

    /// The proof-of-work bits the bus grinds for this array: one per bit of entries past the most the field alone covers.
    pub const fn grinding_bits(self, sizes: Sizes) -> u32 {
        match self {
            Self::Bytecode => sizes.log_bytecode.saturating_sub(UNGROUND_LOG_BYTECODE) as u32,
            Self::Padding => 0,
        }
    }

    /// How many bits of its multiplicities the array's producer puts on the bus.
    ///
    /// Enough for the most reads tables of these heights can make of it; completeness only.
    pub fn multiplicity_bits(self, taus: &PerTable<usize>) -> usize {
        // Every row reads the bytecode once, and pulls at most sixteen padding tuples.
        let rows: u64 = taus.values().map(|&tau| 1u64 << tau).sum();
        let reads = match self {
            Self::Bytecode => rows,
            Self::Padding => 16 * rows,
        };
        (u64::BITS - reads.leading_zeros()) as usize
    }

    /// The tuple the array's producer pushes for each entry, none of it committed.
    pub fn tuple(self, p: &ProgramView<'_>) -> Vec<Coord> {
        let column = |c: Vec<F64>| Public(PublicColumn::new(Arc::new(c)));
        match self {
            // Entry `i` at its byte address, four bytes after the preceding one, then the program's public columns.
            Self::Bytecode => {
                let pc = Coord::IntIndex {
                    base: F64(Region::TEXT.base()),
                    shift: 2,
                };
                [Separator::Bytecode.coordinate(), pc]
                    .into_iter()
                    .chain(self.columns(p).into_iter().map(column))
                    .collect()
            }
            // Each slot's column, the position zero.
            Self::Padding => {
                let columns = self.columns(p);
                columns
                    .into_iter()
                    .enumerate()
                    .map(|(slot, c)| if slot == 2 { Const(F64::ZERO) } else { column(c) })
                    .collect()
            }
        }
    }

    /// The array's stacked polynomial: the bytecode's columns at their bus tuple coordinates.
    ///
    /// It is what an outer verifier is handed in place of a structured program, and what the program digest binds.
    pub fn table(self, p: &ProgramView<'_>) -> Vec<F64> {
        let log_rows = crate::log2_strict_usize(p.rv.entries().len());
        crate::leaf::stacked_bytecode_table(log_rows, &self.tuple(p))
    }

    /// The array's public columns over its entries, in tuple order after the address.
    pub fn columns(self, p: &ProgramView<'_>) -> Vec<Vec<F64>> {
        match self {
            // The program's columns, in bytecode slot order.
            Self::Bytecode => {
                let rv = p.rv;
                let entries = rv.entries();
                let column = |f: &(dyn Fn(usize, &Entry) -> u64 + Sync)| {
                    parallel::map_collect(entries.len(), |i| F64(f(i, &entries[i])))
                };
                vec![
                    // An illegal entry's tag is zero, which is no table's: nothing can read it.
                    parallel::map_collect(entries.len(), |i| {
                        TableId::of(entries[i].class).map_or(F64::ZERO, |t| g_pow(t.index()))
                    }),
                    column(&|_, e| e.flags),
                    column(&|_, e| e.a1 as u64),
                    column(&|_, e| e.a2 as u64),
                    column(&|_, e| e.ad as u64),
                    column(&|_, e| e.imm),
                    column(&|i, _| rv.pc_of(i).wrapping_add(4)),
                    column(&|i, _| rv.dt_of(i)),
                    column(&|_, _| 0),
                    column(&|_, e| e.is_exit() as u64),
                ]
            }
            // One entry per distinct tuple, by slot.
            Self::Padding => {
                let entries = padding_tuples(p);
                let width = entries.iter().map(Vec::len).max().unwrap_or(0);
                let rows = entries.len().next_power_of_two();
                (0..width)
                    .map(|slot| {
                        (0..rows)
                            .map(|e| entries.get(e).and_then(|t| t.get(slot)).copied().unwrap_or(F64::ZERO))
                            .collect()
                    })
                    .collect()
            }
        }
    }
}

/// The distinct tuples the padding rows pull from the logs, and a base-field extension operand's two absent limbs.
pub(crate) fn padding_tuples(p: &ProgramView<'_>) -> Vec<Vec<F64>> {
    let mut tuples: Vec<Vec<F64>> = p
        .fill
        .entries()
        .flat_map(|index| {
            let padding = padding_row(p.rv, index);
            let table = TableId::of(p.rv.entries()[index].class).expect("a fill block's class has a table");
            let table = table.class_table();
            table.link_tuples(&table.row_columns(p.rv, padding.view()))
        })
        .chain([ABSENT_LIMB.to_vec()])
        .collect();
    tuples.sort_unstable_by_key(|t| t.iter().map(|w| w.0).collect::<Vec<_>>());
    tuples.dedup();
    tuples
}

/// How often each padding tuple is pulled, as integer words: by the padding rows, and by the absent limbs.
pub(crate) fn padding_multiplicities(p: &ProgramView<'_>, trace: &Trace) -> Vec<F64> {
    let tuples = padding_tuples(p);
    let key = |t: &[F64]| t.iter().map(|w| w.0).collect::<Vec<_>>();
    let entry = |t: &[F64]| {
        tuples
            .binary_search_by_key(&key(t), |e| key(e))
            .expect("a padding tuple")
    };
    let mut counts = vec![F64::ZERO; tuples.len().next_power_of_two()];
    // A fill entry's padding rows pull the same tuples, so they are counted per entry first.
    let mut rows = std::collections::BTreeMap::new();
    for row in trace.rows.values().flatten().filter(|r| r.time == 0) {
        *rows.entry(row.index as usize).or_insert(0u64) += 1;
    }
    for (index, n) in rows {
        let padding = padding_row(p.rv, index);
        let table = TableId::of(p.rv.entries()[index].class).expect("a fill block's class has a table");
        let table = table.class_table();
        for tuple in table.link_tuples(&table.row_columns(p.rv, padding.view())) {
            counts[entry(&tuple)].0 += n;
        }
    }
    // A live base-field extension row's two high limbs pull the absent limb.
    let base = (trace.rows[TableId::EXT].iter().zip(&trace.ext))
        .filter(|(row, ext)| row.time != 0 && ext.instance.flags & crate::rv::Ext::BASE != 0)
        .count() as u64;
    counts[entry(&ABSENT_LIMB)].0 += 2 * base;
    counts
}

/// The tuple a base-field extension operand's absent high limb pulls: the memory separator, then zeros.
const ABSENT_LIMB: [F64; 5] = [Separator::Memory.value(), F64::ZERO, F64::ZERO, F64::ZERO, F64::ZERO];

/// The committed columns no table owns, first in the global column order.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Shared {
    /// Each advice word's initial value, the prover's.
    AdvInit,
    /// How often each bytecode entry is read (§sec:lookup): entry `x`'s word is the integer `m_x`.
    BytecodeMult,
    /// How often each padding tuple is pulled.
    PaddingMult,
    /// The register log: each read's and the write's one-hot cell, then the increments.
    RegisterLog,
    /// The register log's flags, 64 rows a word.
    RegisterFlags,
    /// The memory log: each chunk's one-hot value, then the increments.
    MemoryLog,
}

impl Shared {
    /// Every shared column, in global column order.
    pub const ALL: [Self; 6] = [
        Self::AdvInit,
        Self::BytecodeMult,
        Self::PaddingMult,
        Self::RegisterLog,
        Self::RegisterFlags,
        Self::MemoryLog,
    ];

    /// The column's global index: its position in the declaration.
    pub const fn col(self) -> usize {
        self as usize
    }

    /// The base-two logarithm of the column's rows.
    pub const fn log_rows(self, sizes: Sizes) -> usize {
        match self {
            Self::AdvInit => sizes.log_advice,
            Self::BytecodeMult => Lookup::Bytecode.log_rows(sizes),
            Self::PaddingMult => Lookup::Padding.log_rows(sizes),
            Self::RegisterLog => sizes.logs[0] + 2,
            Self::RegisterFlags => sizes.logs[0] - CHUNK_BITS,
            Self::MemoryLog => sizes.logs[1] + (sizes.chunks + 1).next_power_of_two().trailing_zeros() as usize,
        }
    }
}

// Invariant: `Shared::ALL` lists the variants in declaration order.
//
// A column's index is its discriminant, and the stack is built in the order of `ALL`.
const _: () = {
    let mut i = 0;
    while i < Shared::ALL.len() {
        assert!(Shared::ALL[i] as usize == i);
        i += 1;
    }
};

/// The index of the first packed flock witness, right after the shared columns: table `t`'s is `Q_BASE + t`.
pub const Q_BASE: usize = Shared::ALL.len();

/// The columns before the first table's: the shared ones, then the packed witnesses.
pub const N_SHARED: usize = Q_BASE + class_flock::N_FLOCKS;

/// The committed column holding packed witness `f`.
pub(crate) const fn q_column(f: FlockId) -> usize {
    Q_BASE + f.index()
}

/// The sizes the layout depends on: the program's, and the announced logs' heights.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Sizes {
    /// The base-two logarithm of the program's entries.
    pub log_bytecode: usize,
    /// The base-two logarithm of RAM's words.
    pub log_ram: usize,
    /// The base-two logarithm of the advice's words.
    pub log_advice: usize,
    /// The base-two logarithm of the padding tuples.
    pub log_padding: usize,
    /// The chunks of a memory cell.
    pub chunks: usize,
    /// Each log's base-two logarithm of rows.
    pub logs: [usize; 2],
}

impl Sizes {
    /// The sizes of `program` with logs of these heights.
    pub fn of(program: &ProgramView<'_>, logs: [usize; 2]) -> Self {
        let p = program.rv;
        Self {
            log_bytecode: crate::log2_strict_usize(p.entries().len()),
            log_ram: p.log_ram(),
            log_advice: p.log_advice(),
            log_padding: padding_tuples(program).len().next_power_of_two().trailing_zeros() as usize,
            chunks: regions(p).chunks(),
            logs,
        }
    }

    /// Where every column sits in the stacked witness, for tables of heights `2^taus`, and the stack's shape.
    pub(super) fn stack(self, taus: &PerTable<usize>) -> (Vec<Placement>, StackShape) {
        witness::placements_of(&self.column_sources(taus))
    }

    /// Every column's source, in global order: the shared columns, the packed witnesses, then each table's columns.
    ///
    /// A circuit word is a port of its table's packed witness, which already holds it, so it is never committed again.
    fn column_sources(self, taus: &PerTable<usize>) -> Vec<Source> {
        let mut sources: Vec<Source> = Shared::ALL
            .iter()
            .map(|c| Source::Committed(c.log_rows(self)))
            .collect();
        sources.extend(FlockId::ALL.map(|f| Source::Committed(taus[f.table()] + f.stride_log())));
        for (t, table) in ClassTable::all().iter() {
            let base = sources.len();
            let f = FlockId::of(t);
            sources.resize(base + table.n_committed_columns(), Source::Committed(taus[t]));
            for (port, c) in table.word_columns(f.part()) {
                sources[base + c] = Source::Port {
                    column: q_column(f),
                    port,
                    stride_log: f.stride_log(),
                };
            }
            for f in table.register_bits().fields {
                sources[base + f.col] = Source::Sliced;
            }
        }
        // Each table's packed register numbers: committed where its word opens, a field of that word otherwise.
        let base = sources.len();
        sources.resize(base + N_TABLES, Source::Sliced);
        for word in RegisterWord::of(taus) {
            sources[word.col] = Source::Committed(taus[word.tables[0]]);
        }
        debug_assert_eq!(sources.len(), Schema::get().n);
        sources
    }
}

/// A program as the layout reads it: its decoded text and its fill blocks.
#[derive(Clone, Copy)]
pub struct ProgramView<'a> {
    /// The decoded text.
    pub rv: &'a RiscvProgram,
    /// The fill blocks in it.
    pub fill: &'a FillBlocks,
}

/// One committed register word: the register numbers of tables of one height, one word per row (§sec:regpack).
///
/// Each table's fields follow the previous table's, low bits first.
///
/// Tables of one height share their table-sumcheck point, so a word is one ring-switched claim whatever it holds.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct RegisterWord {
    /// Its column: the register column of its first table.
    pub(crate) col: usize,
    /// Its tables, in table order.
    pub(crate) tables: Vec<TableId>,
}

impl RegisterWord {
    /// The words of tables of heights `2^taus`.
    ///
    /// In table order, each table joins the first word of its height with room for its fields, or opens one.
    pub(crate) fn of(taus: &PerTable<usize>) -> Vec<Self> {
        let bits = PerTable::from_fn(|t: TableId| t.class_table().register_bits().n_slices());
        let mut words: Vec<(Self, usize)> = Vec::new();
        for t in TableId::ALL {
            let room = words
                .iter_mut()
                .find(|(word, used)| taus[word.tables[0]] == taus[t] && used + bits[t] <= F64::DEGREE);
            match room {
                Some((word, used)) => {
                    word.tables.push(t);
                    *used += bits[t];
                }
                None => words.push((
                    Self {
                        col: Schema::get().registers[t],
                        tables: vec![t],
                    },
                    bits[t],
                )),
            }
        }
        words.into_iter().map(|(word, _)| word).collect()
    }

    /// Fill the word's column from its tables' register numbers.
    ///
    /// `windows` holds every column's values, the word's own column to be written.
    pub(crate) fn pack(&self, windows: &mut [&mut [F64]]) {
        let word = std::mem::take(&mut windows[self.col]);
        let schema = Schema::get();
        let tables: Vec<(BitColumns, Vec<&[F64]>)> = (self.tables.iter())
            .map(|&t| {
                let (base, n) = schema.spans[t];
                let cols = windows[base..base + n].iter().map(|c| &**c).collect();
                (t.class_table().register_bits(), cols)
            })
            .collect();
        parallel::fill(word, |x| {
            let (packed, _) = tables.iter().fold((0, 0), |(packed, shift), (bits, cols)| {
                (packed | bits.packed(cols, x) << shift, shift + bits.n_slices())
            });
            F64(packed)
        });
    }

    /// The word's claim at its tables' point: each table's register numbers' bits, then zeros up to 64.
    ///
    /// Why zeros: an unused bit of an honest word is zero, so a word with one set fails the opening.
    fn claim<E: Copy>(&self, tables: &[Claims<E>], zero: E) -> SliceClaim<E> {
        let slices = (self.tables.iter()).flat_map(|&t| tables[t.index()].slices.iter().copied());
        SliceClaim::zero_padded(tables[self.tables[0].index()].chi.clone(), slices, zero)
    }
}

/// Where each table's columns sit in the global column order.
///
/// - The shared columns and the packed witnesses come first.
/// - Then each table, in table order, owns a contiguous span of columns.
/// - Then each table's packed register numbers, one column per table, committed only where a register word opens (§sec:regpack).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Schema {
    /// Each table's first column and its number of columns.
    pub spans: PerTable<(usize, usize)>,
    /// Each table's packed register column: one word per row, its register numbers as bit fields.
    pub registers: PerTable<usize>,
    /// The total number of columns.
    pub n: usize,
}

impl Schema {
    /// The schema of the fixed table set, computed once.
    pub fn get() -> &'static Self {
        static SCHEMA: OnceLock<Schema> = OnceLock::new();
        SCHEMA.get_or_init(|| {
            let mut next = N_SHARED;
            let spans = PerTable::from_fn(|t: TableId| {
                let span = (next, t.class_table().n_committed_columns());
                next += span.1;
                span
            });
            let registers = PerTable::from_fn(|t: TableId| next + t.index());
            Self {
                spans,
                registers,
                n: next + N_TABLES,
            }
        })
    }
}

/// The public proof structure: everything the verifier rebuilds from the program and the announced sizes.
pub struct Layout {
    /// The push side's blocks: the framework's, the logs', then each table's.
    pub push: Vec<Block>,
    /// The pull side's blocks: the framework's, then each table's.
    pub pull: Vec<Block>,
    /// The lookup arrays' table sides, in lookup order (§sec:lookup).
    pub producers: Vec<Producer>,
    /// The proof-of-work bits before the bus's fingerprint challenges, fixed by the program alone.
    pub grinding: u32,
    /// Where each column sits in the stacked witness, from the columns' sizes alone.
    pub placements: Vec<Placement>,
    /// The stacked witness's shape: its announced size, and how many lane blocks are committed.
    pub shape: StackShape,
    /// Each table's base-two logarithm of rows.
    pub taus: PerTable<usize>,
    /// Each log's shape.
    pub(crate) logs: [LogShape; 2],
    /// The committed register words.
    pub(crate) registers: Vec<RegisterWord>,
}

impl Layout {
    /// The layout of a run of `program` with table heights `2^taus` and logs of heights `2^logs`.
    pub fn new(program: &ProgramView<'_>, taus: PerTable<usize>, logs: [usize; 2]) -> Self {
        let (p, sizes) = (program.rv, Sizes::of(program, logs));

        // The framework's blocks open both sides, then the logs push their accesses.
        let (mut push, mut pull) = (Vec::new(), Vec::new());
        for block in Framework::ALL {
            let (start, end) = block.tuples(p);
            push.push(Block::framework(0, start));
            pull.push(Block::framework(0, end));
        }
        for (i, &log_rows) in logs.iter().enumerate() {
            push.push(Block::log(i, log_rows));
        }

        // Each table declares its flushes in local column indices, offset here to its global span.
        let schema = Schema::get();
        for (t, table) in ClassTable::all().iter() {
            let (base, kappa) = (schema.spans[t].0, taus[t]);
            let flushes = table.flushes();
            let block = |c: Vec<Coord>| Block::table(t.index(), kappa, c.into_iter().map(|c| c.offset(base)).collect());
            push.extend(flushes.push.into_iter().map(block));
            pull.extend(flushes.pull.into_iter().map(block));
        }

        let producers = Lookup::ALL
            .into_iter()
            .map(|lookup| Producer {
                kappa: lookup.log_rows(sizes),
                coords: lookup.tuple(program),
                col: lookup.multiplicity().col(),
                bits: lookup.multiplicity_bits(&taus),
                deferred: lookup == Lookup::Bytecode,
            })
            .collect();

        let regions = regions(p);
        let (placements, shape) = sizes.stack(&taus);
        Self {
            push,
            pull,
            producers,
            grinding: Lookup::Bytecode.grinding_bits(sizes),
            placements,
            shape,
            registers: RegisterWord::of(&taus),
            logs: Log::ALL.map(|log| log.shape(&regions, logs[log as usize])),
            taus,
        }
    }

    /// Packed witness `f`'s window in the stack.
    pub(crate) fn witness_window(&self, f: FlockId) -> Window {
        self.window(q_column(f))
    }

    /// The pull side the prover's leaves take: the final state at the positions `live` rows of each log reach.
    ///
    /// The verifier's pull side holds zeros there, and adds the announced positions' share itself.
    pub(crate) fn pull_closed(&self, live: [usize; 2]) -> Vec<Block> {
        let mut pull = self.pull.clone();
        for (slot, live) in Framework::FINAL_POSITIONS.into_iter().zip(live) {
            pull[Framework::State as usize].coords[slot] = Const(g_pow(live));
        }
        pull
    }

    /// A committed column's window in the stack.
    pub(crate) fn window(&self, col: usize) -> Window {
        self.placements[col].window().expect("a committed column has a window")
    }

    /// Every ring-switched region of the opening, prover and verifiers alike.
    ///
    /// - Each packed witness, with its reduction's claim.
    /// - Each producer's multiplicity column, its bits' evaluations as the slices, then zeros up to 64.
    /// - Each register word, its tables' register numbers' bits as the slices, then zeros up to 64.
    /// - Each log's address words, and the register log's flags, with their slices at the log's two points.
    pub(crate) fn rings<E: Copy>(
        &self,
        witnesses: impl IntoIterator<Item = SliceClaim<E>>,
        multiplicities: &[Claims<E>],
        tables: &[Claims<E>],
        logs: &[LogOpening<E>],
        zero: E,
    ) -> Vec<RingSwitch<E>> {
        let witnesses = (FlockId::ALL.into_iter().zip(witnesses)).map(|(f, claim)| self.witness_window(f).ring(claim));
        let producers = (self.producers.iter().zip(multiplicities)).map(|(p, claims)| {
            let claim = SliceClaim::zero_padded(claims.chi.clone(), claims.evals.iter().copied(), zero);
            self.window(p.col).ring(claim)
        });
        let registers = self
            .registers
            .iter()
            .map(|word| self.window(word.col).ring(word.claim(tables, zero)));
        let mut rings: Vec<RingSwitch<E>> = witnesses.chain(producers).chain(registers).collect();
        for (log, opening) in Log::ALL.iter().zip(logs) {
            let (window, n) = (self.window(log.column().col()), self.logs[*log as usize].log_rows);
            for (slot, claims) in opening.addresses.iter().enumerate() {
                rings.push(RingSwitch {
                    offset: window.offset + (slot << n),
                    qflock_vars: n,
                    claims: claims.to_vec(),
                });
            }
            if let Some(flags) = &opening.flag {
                let window = self.window(Shared::RegisterFlags.col());
                rings.push(RingSwitch {
                    offset: window.offset,
                    qflock_vars: window.n_vars,
                    claims: flags.to_vec(),
                });
            }
        }
        rings
    }

    /// Every claim the opening discharges, located in the stack, in the order that feeds the batch's weights.
    ///
    /// - The bus's framework claims.
    /// - The batch's per-table column claims.
    /// - Each log's increments at its two points, and the advice's initial words.
    ///
    /// Prover and verifiers all assemble them here, so no claim can shift by one.
    pub(crate) fn opening_claims<E: Copy>(
        &self,
        bus_claims: Vec<ColumnClaim<E>>,
        table_claims: &[Claims<E>],
        logs: &[LogOpening<E>],
    ) -> Vec<StackClaim<E>> {
        let schema = Schema::get();
        let mut claims = bus_claims;
        for (&(base, _), table) in schema.spans.values().zip(table_claims) {
            claims.extend(table.evals.iter().enumerate().map(|(c, &value)| ColumnClaim {
                col: base + c,
                point: table.chi.clone(),
                value,
            }));
        }
        let mut located: Vec<StackClaim<E>> = (claims.into_iter())
            .filter_map(|c| self.placements[c.col].claim(c.point, c.value))
            .collect();
        for (log, opening) in Log::ALL.iter().zip(logs) {
            let shape = &self.logs[*log as usize];
            let inc = shape.groups() * shape.chunks();
            let window = self.window(log.column().col());
            for (point, value) in &opening.inc {
                located.push(StackClaim::Point {
                    offset: window.offset + (inc << shape.log_rows),
                    low_point: point.clone(),
                    value: *value,
                });
            }
            if let Some((point, value)) = &opening.advice {
                located.extend(self.placements[Shared::AdvInit.col()].claim(point.clone(), *value));
            }
        }
        located
    }
}

/// The sizes the prover announces before committing: each table's height, each log's, the rate, and each log's live rows.
///
/// The program's own sizes are public, so they are never announced.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct Announcement {
    /// Each table's base-two logarithm of rows.
    pub(crate) taus: PerTable<usize>,
    /// Each log's base-two logarithm of rows.
    pub(crate) logs: [usize; 2],
    /// The commitment's rate.
    pub(crate) rate: Rate,
    /// Each log's live rows: the run's cycles, then its memory accesses.
    pub(crate) live: [u64; 2],
}

impl Announcement {
    /// The scalars it takes on the stream: each table's height, each log's, the rate, then each log's live rows.
    pub(crate) const LEN: usize = N_TABLES + 2 + 1 + 2;

    /// The scalars announcing the heights, then the rate's, each an integer in the first coordinate.
    pub(crate) fn sizes(taus: &PerTable<usize>, logs: [usize; 2], rate: Rate) -> impl Iterator<Item = F192> {
        let rate = usize::from(rate.log_inv_rate());
        (taus.values().copied().chain(logs).chain([rate])).map(|size| F192::new(size as u64, 0, 0))
    }

    /// Write the announcement onto the scalar stream, which binds it into the transcript.
    pub(super) fn write(&self, ps: &mut ProverState) {
        for size in Self::sizes(&self.taus, self.logs, self.rate) {
            ps.add_scalar(size);
        }
        for live in self.live {
            ps.add_scalar(F192::new(live, 0, 0));
        }
    }

    /// Read an announcement off the scalar stream, binding it, and check every value is in range.
    ///
    /// # Errors
    ///
    /// Refuses a short stream, then what decoding refuses.
    pub(super) fn read(vs: &mut VerifierState) -> Result<Self, CpuError> {
        let mut scalars = [F192::ZERO; Self::LEN];
        for x in &mut scalars {
            *x = vs.next_scalar()?;
        }
        Self::decode(&scalars)
    }

    /// The announcement its scalars state, every value checked in range.
    ///
    /// # Errors
    ///
    /// Refuses a non-canonical size, a height or a rate outside its range, or a live count its log does not hold.
    pub(crate) fn decode(scalars: &[F192; Self::LEN]) -> Result<Self, CpuError> {
        let size = |x: &F192| -> Result<usize, CpuError> {
            if x.c1 != 0 || x.c2 != 0 {
                return Err(CpuError::NonCanonicalSize);
            }
            usize::try_from(x.c0).map_err(|_| CpuError::NonCanonicalSize)
        };
        let mut taus = PerTable::default();
        for (t, x) in TableId::ALL.into_iter().zip(scalars) {
            taus[t] = size(x)?;
        }
        let logs = [size(&scalars[N_TABLES])?, size(&scalars[N_TABLES + 1])?];
        let log_inv_rate = size(&scalars[N_TABLES + 2])?;
        let live = [size(&scalars[N_TABLES + 3])?, size(&scalars[N_TABLES + 4])?];
        Layout::check_heights(&taus, logs)?;
        // The run has a cycle, its exit, and each log holds its live rows.
        if live[0] == 0 || (0..2).any(|i| live[i] > 1 << logs[i]) {
            return Err(CpuError::LiveRows);
        }
        let rate = (u8::try_from(log_inv_rate).ok())
            .and_then(|r| Rate::new(r).ok())
            .ok_or(CpuError::Rate { log_inv_rate })?;
        Ok(Self {
            taus,
            logs,
            rate,
            live: live.map(|l| l as u64),
        })
    }

    /// The layout the announced heights describe for `program`.
    ///
    /// # Errors
    ///
    /// Refuses heights whose stacked witness the commitment does not take.
    pub(super) fn layout(&self, program: &ProgramView<'_>) -> Result<Layout, CpuError> {
        Layout::announced(program, self.taus, self.logs)
    }
}

impl Layout {
    /// The layout a verifier rebuilds from announced heights.
    ///
    /// # Errors
    ///
    /// Refuses a height outside its range, or heights whose stacked witness the commitment does not take.
    pub(crate) fn announced(
        program: &ProgramView<'_>,
        taus: PerTable<usize>,
        logs: [usize; 2],
    ) -> Result<Self, CpuError> {
        Self::check_heights(&taus, logs)?;
        let layout = Self::new(program, taus, logs);
        if !(crate::pcs::MIN_MU..=crate::pcs::MAX_MU).contains(&layout.shape.mu) {
            return Err(CpuError::WitnessSize { mu: layout.shape.mu });
        }
        Ok(layout)
    }

    /// Check each table's and log's height lies between its floor and the public cap.
    fn check_heights(taus: &PerTable<usize>, logs: [usize; 2]) -> Result<(), CpuError> {
        for (t, &log_rows) in taus.iter() {
            let min = t.spec().n_blocks_log(1);
            if !(min..=MAX_LOG_ROWS).contains(&log_rows) {
                return Err(CpuError::TableHeight {
                    table: t.name(),
                    log_rows,
                    min,
                    max: MAX_LOG_ROWS,
                });
            }
        }
        for log_rows in logs {
            if !(Log::MIN_LOG_ROWS..=MAX_LOG_ROWS).contains(&log_rows) {
                return Err(CpuError::LogHeight { log_rows });
            }
        }
        Ok(())
    }
}
