//! The public proof structure: the global column order, the bus blocks, the producers, and where every claim lands.
//!
//! The verifier rebuilds it from the program and the prover's announced sizes, with no witness value.
//!
//! The blocks name columns by index, so the layout is pure public structure.
//!
//! Each enum's declaration order is protocol order: reordering a variant changes the proof layout.

use super::error::CpuError;
use super::execute::{Trace, padding_row};
use super::filler::FillBlocks;
use super::{MAX_LOG_ROWS, UNGROUND_LOG_BYTECODE};
use crate::class_flock::FlockId;
use crate::constraints::{BitColumns, Claims};
use crate::leaf::{Block, ColumnClaim, Coord, Producer, PublicColumn, SparseColumn};
use crate::pcs::{Rate, RingSwitch, SliceClaim, StackClaim};
use crate::registers::{CELL_BITS, GROUPS, LogOpening, LogShape, Slot};
use crate::rv::{Entry, Reg, Region, RiscvProgram};
use crate::tables::{ClassTable, Clock, N_TABLES, PerTable, Separator, TableId};
use crate::witness::{Placement, Source, StackShape, Window};
use crate::{class_flock, witness};
use Coord::{Col, Const, IntIndex, Public, Sparse};
use fiat_shamir::MAX_GRINDING_BITS;
use fiat_shamir::transcript::{ProverState, Receiver, Transmitter, VerifierState};
use primitives::field::{F64, F192, g_pow};
use std::sync::{Arc, OnceLock};

// The largest text grinds within the proof of work's window.
const _: () = assert!(Region::TEXT.max_log_words() - UNGROUND_LOG_BYTECODE <= MAX_GRINDING_BITS as usize);

/// The bus blocks no table owns, which each side of the bus starts with.
///
/// Each has a push block and a pull block of the same height.
///
/// - The push block seeds a memory array, or starts the run.
/// - The pull block finalizes it, or ends the run, with committed columns.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Framework {
    /// The run's boundary: it starts at the entry point on cycle 1 and time one, and ends on the halt slot.
    State,
    /// RAM.
    Ram,
    /// The advice.
    Advice,
    /// The zero cell, which a base-field extension operand's high limbs read.
    Zero,
}

impl Framework {
    /// Every framework block, in bus order.
    pub const ALL: [Self; 4] = [Self::State, Self::Ram, Self::Advice, Self::Zero];

    /// Where the final clock sits in the state's finalizing tuple: the run's last state is `(pc, ts, time)`.
    pub(crate) const FINAL_CLOCK: usize = 2;

    /// Where the final time sits in the state's finalizing tuple: `g^cycles`, from the announced cycles.
    pub(crate) const FINAL_TIME: usize = 3;

    /// The base-two logarithm of the block's rows: one per cell of its array.
    pub const fn log_rows(self, sizes: Sizes) -> usize {
        match self {
            Self::State | Self::Zero => 0,
            Self::Ram => sizes.log_ram,
            Self::Advice => sizes.log_advice,
        }
    }

    /// The block's two tuples: the push side's seed, then the pull side's finalization.
    fn tuples(self, p: &RiscvProgram, ts_final: u64) -> (Vec<Coord>, Vec<Coord>) {
        // A read-write array: each cell starts at the seed's clock holding `init`.
        //
        // It ends at its last timestamp holding its final word (§sec:memchan).
        let array = |sep: F64, cell: Coord, init: Option<Coord>, ts: Shared, fin: Shared| {
            let seed = [Const(sep), cell.clone(), Const(F64(Clock::SEED_CLOCK))]
                .into_iter()
                .chain(init)
                .collect();
            (seed, vec![Const(sep), cell, Col(ts.col()), Col(fin.col())])
        };

        // Word `z` of a memory region sits at `base + 8z`.
        let word = |base: u64| IntIndex {
            base: F64(base),
            shift: 3,
        };

        match self {
            // The run starts at the entry point and ends on the halt slot, marked by the exit.
            //
            // A wrong clock or time leaves the end unmatched, and so does a padding row's exit, whose time is zero.
            // The end's time is zero here: the verifier adds the announced cycles' share itself.
            Self::State => (
                vec![
                    Separator::State.coordinate(),
                    Const(F64(p.entry_pc())),
                    Const(F64(Clock::CLOCK_START)),
                    Const(F64::ONE),
                    Const(F64::ZERO),
                ],
                vec![
                    Separator::State.coordinate(),
                    Const(F64(p.halt_pc())),
                    Const(F64(ts_final)),
                    Const(F64::ZERO),
                    Const(F64::ONE),
                ],
            ),
            // RAM starts as the program's image, then zeros, all public.
            Self::Ram => {
                let image = Sparse(Arc::new(SparseColumn::new(p.log_ram(), &[(0, p.image())])));
                array(
                    Separator::Memory.value(),
                    word(Region::RAM.base()),
                    Some(image),
                    Shared::RamTs,
                    Shared::RamFin,
                )
            }
            // The one array seeded from a committed column: the prover's words.
            Self::Advice => array(
                Separator::Memory.value(),
                word(Region::ADVICE.base()),
                Some(Col(Shared::AdvInit.col())),
                Shared::AdvTs,
                Shared::AdvFin,
            ),
            // One cell at address zero, seeded and finalized holding zero: nothing writes it.
            Self::Zero => {
                let (sep, cell) = (Separator::Zero.coordinate(), Const(F64::ZERO));
                (
                    vec![sep.clone(), cell.clone(), Const(F64(Clock::SEED_CLOCK))],
                    vec![sep, cell, Col(Shared::ZeroTs.col())],
                )
            }
        }
    }
}

/// The register log (§sec:regchan): a row per cycle, which the tables' rows pull at their time.
pub struct RegisterLog;

impl RegisterLog {
    /// The fewest rows the log has: its packed flags fill a word.
    pub const MIN_LOG_ROWS: usize = CELL_BITS;

    /// The log's height for a run of `cycles` cycles.
    pub const fn log_rows(cycles: usize) -> usize {
        let log = cycles.next_power_of_two().trailing_zeros() as usize;
        if log > Self::MIN_LOG_ROWS {
            log
        } else {
            Self::MIN_LOG_ROWS
        }
    }

    /// The log's shape at `2^log_rows` rows.
    ///
    /// A table's row pulls the cycle `(sep, a1, time, a2, ad, v1, v2, vd)`: the log pushes the same tuples.
    pub(crate) fn shape(log_rows: usize) -> LogShape {
        LogShape {
            log_rows,
            slots: vec![
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
                Slot::Written,
            ],
            outputs: std::iter::once(&Reg::SYSCALL)
                .chain(&Reg::OUTPUTS)
                .map(|r| r.index())
                .collect(),
        }
    }
}

/// The read-only arrays (§sec:lookup).
///
/// Their table side is a producer rather than a pair of framework blocks.
///
/// It pushes every entry as often as it is read, which a committed multiplicity column says.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Lookup {
    /// The program: one entry per instruction slot.
    Bytecode,
    /// The register cycles padding rows pull: they are at time zero, which no log row has.
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
    /// Enough for the most reads tables of these heights can make of it: every row reads the bytecode once, and a
    /// padding row pulls one padding tuple.
    ///
    /// Completeness only: no read count is too large for soundness.
    pub fn multiplicity_bits(self, taus: &PerTable<usize>) -> usize {
        let rows: u64 = taus.values().map(|&tau| 1u64 << tau).sum();
        (u64::BITS - rows.leading_zeros()) as usize
    }

    /// Whether the verifier leaves the producer's public columns to the program's claim, else evaluates them itself.
    ///
    /// The padding tuples are few, so evaluating them is cheaper than deferring.
    pub const fn deferred(self) -> bool {
        matches!(self, Self::Bytecode)
    }

    /// The tuple the array's producer pushes for each entry, none of it committed.
    pub fn tuple(self, p: &ProgramView<'_>) -> Vec<Coord> {
        let column = |c: Vec<F64>| Public(PublicColumn::new(Arc::new(c)));
        match self {
            // Entry `i` at its byte address, four bytes after the preceding one, then the program's public columns.
            Self::Bytecode => {
                let pc = IntIndex {
                    base: F64(Region::TEXT.base()),
                    shift: 2,
                };
                [Separator::Bytecode.coordinate(), pc]
                    .into_iter()
                    .chain(self.columns(p).into_iter().map(column))
                    .collect()
            }
            // Each slot's column, the time zero.
            Self::Padding => (self.columns(p).into_iter().enumerate())
                .map(|(slot, c)| if slot == 2 { Const(F64::ZERO) } else { column(c) })
                .collect(),
        }
    }

    /// The array's stacked polynomial: its columns at their bus tuple coordinates.
    ///
    /// It makes the array's whole share of a bus leaf one evaluation.
    ///
    /// For the bytecode, it is what an outer verifier is handed in place of a structured program.
    ///
    /// It is also what the program digest binds.
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
                            .map(|e| entries.get(e).map_or(F64::ZERO, |t| t[slot]))
                            .collect()
                    })
                    .collect()
            }
        }
    }
}

/// The distinct register cycles the fill blocks' padding rows pull, sorted.
pub(crate) fn padding_tuples(p: &ProgramView<'_>) -> Vec<Vec<F64>> {
    let mut tuples: Vec<Vec<F64>> = (p.fill.entries()).map(|index| padding_tuple(p.rv, index)).collect();
    tuples.sort_unstable_by_key(|t| t.iter().map(|w| w.0).collect::<Vec<_>>());
    tuples.dedup();
    tuples
}

/// The register cycle a padding row of entry `index` pulls.
fn padding_tuple(p: &RiscvProgram, index: usize) -> Vec<F64> {
    let padding = padding_row(p, index);
    let table = TableId::of(p.entries()[index].class).expect("a fill block's class has a table");
    let table = table.class_table();
    table.register_tuple(&table.row_columns(p, padding.view()))
}

/// How often each padding tuple is pulled, as integer words: once by each padding row.
pub(crate) fn padding_multiplicities(p: &ProgramView<'_>, trace: &Trace) -> Vec<F64> {
    let tuples = padding_tuples(p);
    let mut counts = vec![F64::ZERO; tuples.len().next_power_of_two()];
    // A fill entry's padding rows pull the same tuple, so they are counted per entry first.
    let mut rows = std::collections::BTreeMap::new();
    for row in trace.rows.values().flatten().filter(|r| r.time == 0) {
        *rows.entry(row.index as usize).or_insert(0u64) += 1;
    }
    for (index, n) in rows {
        let tuple = padding_tuple(p.rv, index);
        let key = |t: &[F64]| t.iter().map(|w| w.0).collect::<Vec<_>>();
        let entry = tuples
            .binary_search_by_key(&key(&tuple), |t| key(t))
            .expect("a padding tuple");
        counts[entry].0 += n;
    }
    counts
}

/// The committed columns no table owns, first in the global column order.
///
/// What is committed of memory is what each array holds after the run, and each cell's last timestamp (§sec:memchan).
///
/// - The program is public, not committed: only the multiplicities of its reads are.
/// - RAM starts at the program's image, public.
/// - The advice is the one array whose initial words are committed too: they are the prover's.
/// - The register log is committed whole: its cells' one-hot words, its increments, and its flags (§sec:regchan).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Shared {
    /// Each RAM word's final value.
    RamFin,
    /// Each RAM word's final timestamp.
    RamTs,
    /// Each advice word's initial value, the prover's.
    AdvInit,
    /// Each advice word's final value.
    AdvFin,
    /// Each advice word's final timestamp.
    AdvTs,
    /// The zero cell's final timestamp.
    ZeroTs,
    /// How often each bytecode entry is read (§sec:lookup).
    ///
    /// Entry `x`'s word is the integer `m_x`.
    ///
    /// Its bits are the producer's one-bit columns, opened by ring switching.
    BytecodeMult,
    /// How often each padding tuple is pulled.
    PaddingMult,
    /// The register log: each group's one-hot cell words, then the increments, `2^log_rows` words each.
    RegisterLog,
    /// The register log's flags, 64 rows a word.
    RegisterFlags,
}

impl Shared {
    /// Every shared column, in global column order.
    pub const ALL: [Self; 10] = [
        Self::RamFin,
        Self::RamTs,
        Self::AdvInit,
        Self::AdvFin,
        Self::AdvTs,
        Self::ZeroTs,
        Self::BytecodeMult,
        Self::PaddingMult,
        Self::RegisterLog,
        Self::RegisterFlags,
    ];

    /// The column's global index: its position in the declaration.
    pub const fn col(self) -> usize {
        self as usize
    }

    /// The base-two logarithm of the column's rows: one per cell or entry of its array, or per row of the log.
    pub const fn log_rows(self, sizes: Sizes) -> usize {
        match self {
            Self::RamFin | Self::RamTs => Framework::Ram.log_rows(sizes),
            Self::AdvInit | Self::AdvFin | Self::AdvTs => Framework::Advice.log_rows(sizes),
            Self::ZeroTs => Framework::Zero.log_rows(sizes),
            Self::BytecodeMult => Lookup::Bytecode.log_rows(sizes),
            Self::PaddingMult => Lookup::Padding.log_rows(sizes),
            // Three cell words and the increment per row.
            Self::RegisterLog => sizes.log_cycles + 2,
            Self::RegisterFlags => sizes.log_cycles - CELL_BITS,
        }
    }

    /// The column's values as the run left them.
    ///
    /// A multiplicity column and the log's have none: they are built from the rows.
    pub(super) fn values(self, trace: &Trace) -> Option<&[F64]> {
        Some(match self {
            Self::RamFin => &trace.ram_fin,
            Self::RamTs => &trace.ram_ts,
            Self::AdvInit => &trace.adv_init,
            Self::AdvFin => &trace.adv_fin,
            Self::AdvTs => &trace.adv_ts,
            Self::ZeroTs | Self::BytecodeMult | Self::PaddingMult | Self::RegisterLog | Self::RegisterFlags => {
                return None;
            }
        })
    }
}

// Invariant: `Shared::ALL` lists the variants in declaration order.
//
// A column's index is its discriminant, and the stack is built in the order of `ALL`.
//
// So the two orders must be one, or a column's claims would land in another column's window.
const _: () = {
    let mut i = 0;
    while i < Shared::ALL.len() {
        assert!(Shared::ALL[i] as usize == i);
        i += 1;
    }
};

/// The index of the first packed flock witness, right after the shared columns.
///
/// Every class circuit's in table order, then the clock circuit's of every table whose rows touch memory.
///
/// Each is the sole copy of its circuit's words, committed in the same stack as every other column.
pub const Q_BASE: usize = Shared::ALL.len();

/// The columns before the first table's: the shared ones, then the packed witnesses.
pub const N_SHARED: usize = Q_BASE + class_flock::N_FLOCKS;

/// The committed column holding packed witness `f`.
pub(crate) const fn q_column(f: FlockId) -> usize {
    Q_BASE + f.index()
}

/// The sizes the layout depends on: the program's, and the register log's height.
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
    /// The base-two logarithm of the register log's rows.
    pub log_cycles: usize,
}

impl Sizes {
    /// The sizes of `p` with a register log of `2^log_cycles` rows.
    pub fn of(p: &ProgramView<'_>, log_cycles: usize) -> Self {
        let rv = p.rv;
        Self {
            log_bytecode: crate::log2_strict_usize(rv.entries().len()),
            log_ram: rv.log_ram(),
            log_advice: rv.log_advice(),
            log_padding: padding_tuples(p).len().next_power_of_two().trailing_zeros() as usize,
            log_cycles,
        }
    }

    /// Where every column of a program of these sizes sits in the stacked witness, for tables of heights `2^taus`, and the stack's shape.
    ///
    /// No witness is needed.
    pub(super) fn stack(self, taus: &PerTable<usize>) -> (Vec<Placement>, StackShape) {
        witness::placements_of(&self.column_sources(taus))
    }

    /// Every column's source, in global order.
    ///
    /// - The shared columns, at their arrays' sizes.
    /// - The packed witnesses, at their tables' heights times their instance strides.
    /// - Each table's columns, at its height.
    ///
    /// A circuit word is a port of its class's packed witness, which already holds it.
    ///
    /// So it is never committed again: its bus claims settle against that witness.
    fn column_sources(self, taus: &PerTable<usize>) -> Vec<Source> {
        let mut sources: Vec<Source> = Shared::ALL
            .iter()
            .map(|c| Source::Committed(c.log_rows(self)))
            .collect();

        // The packed witnesses: every class circuit's, then every clock circuit's.
        sources.extend(FlockId::ALL.map(|f| Source::Committed(taus[f.table()] + f.stride_log())));

        // Each table's columns, its circuit words turned into ports of its packed witnesses.
        //
        // Its register numbers are fields of its packed register column instead.
        for (t, table) in ClassTable::all().iter() {
            let base = sources.len();
            sources.resize(base + table.n_committed_columns(), Source::Committed(taus[t]));
            for f in FlockId::class(t).into_iter().chain(FlockId::clock(t)) {
                for (port, c) in table.word_columns(f.part()) {
                    sources[base + c] = Source::Port {
                        column: q_column(f),
                        port,
                        stride_log: f.stride_log(),
                    };
                }
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
    ///
    /// Tables of one height share the first one's word while it has room.
    pub registers: PerTable<usize>,
    /// The total number of columns.
    pub n: usize,
}

impl Schema {
    /// The schema of the fixed table set, computed once.
    pub fn get() -> &'static Self {
        static SCHEMA: OnceLock<Schema> = OnceLock::new();
        SCHEMA.get_or_init(|| {
            // Each table's span starts where the previous one ends.
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

/// A program as the layout reads it: its decoded text and its fill blocks.
#[derive(Clone, Copy)]
pub struct ProgramView<'a> {
    /// The decoded program.
    pub rv: &'a RiscvProgram,
    /// Where each fill block sits in the text.
    pub fill: &'a FillBlocks,
}

/// The public proof structure: everything the verifier rebuilds from the program and the announced sizes.
pub struct Layout {
    /// The push side's blocks: the framework's, the register log's, then each table's.
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
    /// The register log's shape.
    pub(crate) log: LogShape,
    /// The committed register words.
    pub(crate) registers: Vec<RegisterWord>,
}

impl Layout {
    /// The layout of a run of `program` with table heights `2^taus`, ending on clock `ts_final`, with a register log
    /// of `2^log_cycles` rows.
    ///
    /// A table's height is its row count: the fill blocks bring every count to a power of two.
    pub fn new(program: &ProgramView<'_>, taus: PerTable<usize>, ts_final: u64, log_cycles: usize) -> Self {
        let (p, sizes) = (program.rv, Sizes::of(program, log_cycles));

        // The framework's blocks open both sides, one push and one pull block each, then the register log pushes.
        let (mut push, mut pull) = (Vec::new(), Vec::new());
        for block in Framework::ALL {
            let kappa = block.log_rows(sizes);
            let (seed, finalize) = block.tuples(p, ts_final);
            push.push(Block::framework(kappa, seed));
            pull.push(Block::framework(kappa, finalize));
        }
        push.push(Block::log(0, log_cycles));

        // Each table declares its flushes in local column indices, offset here to its global span.
        let schema = Schema::get();
        for (t, table) in ClassTable::all().iter() {
            let (base, kappa) = (schema.spans[t].0, taus[t]);
            let flushes = table.flushes();
            let block = |c: Vec<Coord>| Block::table(t.index(), kappa, c.into_iter().map(|c| c.offset(base)).collect());
            push.extend(flushes.push.into_iter().map(block));
            pull.extend(flushes.pull.into_iter().map(block));
        }

        // Each lookup array's producer: its tuple, its multiplicity column, and how many bits of it the bus reads.
        let producers = Lookup::ALL
            .into_iter()
            .map(|lookup| Producer {
                kappa: lookup.log_rows(sizes),
                coords: lookup.tuple(program),
                col: lookup.multiplicity().col(),
                bits: lookup.multiplicity_bits(&taus),
                deferred: lookup.deferred(),
            })
            .collect();

        let (placements, shape) = sizes.stack(&taus);
        Self {
            push,
            pull,
            producers,
            grinding: Lookup::Bytecode.grinding_bits(sizes),
            placements,
            shape,
            log: RegisterLog::shape(log_cycles),
            registers: RegisterWord::of(&taus),
            taus,
        }
    }

    /// The pull side the prover's leaves take: the final state at the time `cycles` cycles reach.
    ///
    /// The verifier's pull side holds zero there, and adds the announced time's share itself.
    pub(crate) fn pull_closed(&self, cycles: usize) -> Vec<Block> {
        let mut pull = self.pull.clone();
        pull[Framework::State as usize].coords[Framework::FINAL_TIME] = Const(g_pow(cycles));
        pull
    }

    /// A committed column's window in the stack.
    pub(crate) fn window(&self, col: usize) -> Window {
        self.placements[col].window().expect("a committed column has a window")
    }

    /// Packed witness `f`'s window in the stack.
    pub(crate) fn witness_window(&self, f: FlockId) -> Window {
        self.placements[q_column(f)]
            .window()
            .expect("a packed witness is committed")
    }

    /// A producer's multiplicity column's window in the stack.
    pub(crate) fn multiplicity_window(&self, p: &Producer) -> Window {
        self.placements[p.col]
            .window()
            .expect("a multiplicity column is committed")
    }

    /// Every ring-switched region of the opening, prover and verifiers alike.
    ///
    /// - Each packed witness, with its reduction's claim.
    /// - Each producer's multiplicity column, its bits' evaluations as the slices, then zeros up to 64.
    /// - Each register word, its tables' register numbers' bits as the slices, then zeros up to 64.
    /// - The register log's cell words and its flags, with their slices at the log's two points.
    pub(crate) fn rings<E: Copy>(
        &self,
        witnesses: impl IntoIterator<Item = SliceClaim<E>>,
        multiplicities: &[Claims<E>],
        tables: &[Claims<E>],
        log: &LogOpening<E>,
        zero: E,
    ) -> Vec<RingSwitch<E>> {
        let witnesses = (FlockId::ALL.into_iter().zip(witnesses)).map(|(f, claim)| self.witness_window(f).ring(claim));
        let producers = (self.producers.iter().zip(multiplicities)).map(|(p, claims)| {
            let claim = SliceClaim::zero_padded(claims.chi.clone(), claims.evals.iter().copied(), zero);
            self.multiplicity_window(p).ring(claim)
        });
        let registers = self.registers.iter().map(|word| {
            let window = self.placements[word.col]
                .window()
                .expect("a register word is committed");
            window.ring(word.claim(tables, zero))
        });
        let (window, n) = (self.window(Shared::RegisterLog.col()), self.log.log_rows);
        let cells = log.cells.iter().enumerate().map(|(g, claims)| RingSwitch {
            offset: window.offset + (g << n),
            qflock_vars: n,
            claims: claims.to_vec(),
        });
        let flags = self.window(Shared::RegisterFlags.col());
        let flags = RingSwitch {
            offset: flags.offset,
            qflock_vars: flags.n_vars,
            claims: log.flag.to_vec(),
        };
        (witnesses.chain(producers).chain(registers).chain(cells))
            .chain([flags])
            .collect()
    }

    /// Every claim the opening discharges, located in the stack, in the order that feeds the batch's weights.
    ///
    /// - The bus's framework claims.
    /// - The batch's per-table column claims.
    /// - The register log's increments at its two points.
    ///
    /// Prover and verifiers all assemble them here, so no claim can shift by one.
    pub(crate) fn opening_claims<E: Copy>(
        &self,
        bus_claims: Vec<ColumnClaim<E>>,
        table_claims: &[Claims<E>],
        log: &LogOpening<E>,
    ) -> Vec<StackClaim<E>> {
        let schema = Schema::get();
        let mut claims = bus_claims;
        claims.reserve(schema.n - N_SHARED);

        // Each table's column claims, at the batch's point.
        for (&(base, _), table) in schema.spans.values().zip(table_claims) {
            claims.extend(table.evals.iter().enumerate().map(|(c, &value)| ColumnClaim {
                col: base + c,
                point: table.chi.clone(),
                value,
            }));
        }

        // The register log's increments: the column's last quarter, past the three groups' cell words.
        let window = self.window(Shared::RegisterLog.col());
        let inc = window.offset + (GROUPS << self.log.log_rows);
        let mut stacked: Vec<StackClaim<E>> = log
            .inc
            .iter()
            .map(|(point, value)| StackClaim::Point {
                offset: inc,
                low_point: point.clone(),
                value: *value,
            })
            .collect();

        // A port's claim is folded at the table's height, not its packed witness's, and joins the one opening.
        //
        // A register number's has no place in the stack: its bits' claim is its table's ring-switched region.
        let mut out: Vec<StackClaim<E>> = (claims.into_iter())
            .filter_map(|c| self.placements[c.col].claim(c.point, c.value))
            .collect();
        out.append(&mut stacked);
        out
    }
}

/// The sizes the prover announces before committing: each table's height, the rate, and the final clock.
///
/// The program's own sizes are public, so they are never announced.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct Announcement {
    /// Each table's base-two logarithm of rows.
    pub(crate) taus: PerTable<usize>,
    /// The register log's base-two logarithm of rows.
    pub(crate) log_cycles: usize,
    /// The commitment's rate.
    pub(crate) rate: Rate,
    /// The clock the run ended on: the final state's timestamp (§sec:state).
    pub(crate) ts_final: u64,
    /// The run's cycles: the register log's live rows.
    pub(crate) cycles: u64,
}

impl Announcement {
    /// The scalars it takes on the stream: each table's height, the log's, the rate, the final clock, the cycles.
    pub(crate) const LEN: usize = N_TABLES + 4;

    /// The scalars announcing each table's height, the log's, then the rate's, each an integer in the first coordinate.
    ///
    /// A height, not a row count: every table's rows are real, filled to a power of two.
    pub(crate) fn sizes(taus: &PerTable<usize>, log_cycles: usize, rate: Rate) -> impl Iterator<Item = F192> {
        let rate = usize::from(rate.log_inv_rate());
        (taus.values().copied().chain([log_cycles, rate])).map(|size| F192::new(size as u64, 0, 0))
    }

    /// Write the announcement onto the scalar stream, which binds it into the transcript.
    pub(super) fn write(&self, ps: &mut ProverState) {
        for size in Self::sizes(&self.taus, self.log_cycles, self.rate) {
            ps.add_scalar(size);
        }
        ps.add_scalar(F192::new(self.ts_final, 0, 0));
        ps.add_scalar(F192::new(self.cycles, 0, 0));
    }

    /// Read an announcement off the scalar stream, binding it, and check every value is in range.
    ///
    /// The checks run before any reduction, so an out-of-range announcement costs nothing.
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
    /// Refuses a non-canonical size, a final clock that is not live, a height or a rate outside its range, or cycles
    /// the log does not hold.
    pub(crate) fn decode(scalars: &[F192; Self::LEN]) -> Result<Self, CpuError> {
        // A size is a canonical integer in the first coordinate.
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
        let log_cycles = size(&scalars[N_TABLES])?;
        let log_inv_rate = size(&scalars[N_TABLES + 1])?;

        // A live clock at slot zero: neither a padding row's clock nor a failed row's can end the run.
        let ts_final = scalars[N_TABLES + 2];
        let live = ts_final.c0 >> Clock::LIVE_BIT == 1 && ts_final.c0.is_multiple_of(Clock::CYCLE);
        if !live || ts_final.c1 != 0 || ts_final.c2 != 0 {
            return Err(CpuError::FinalClock);
        }

        Layout::check_heights(&taus, log_cycles)?;

        // The run has a cycle, its exit, and the log holds every cycle.
        let cycles = size(&scalars[N_TABLES + 3])?;
        if cycles == 0 || cycles > 1 << log_cycles {
            return Err(CpuError::Cycles);
        }

        // A rate the commitment supports.
        let rate = (u8::try_from(log_inv_rate).ok())
            .and_then(|r| Rate::new(r).ok())
            .ok_or(CpuError::Rate { log_inv_rate })?;
        Ok(Self {
            taus,
            log_cycles,
            rate,
            ts_final: ts_final.c0,
            cycles: cycles as u64,
        })
    }

    /// The layout the announced heights describe for `program`, its final clock and time zero.
    ///
    /// The verifier adds the announced clock's and time's shares itself.
    ///
    /// # Errors
    ///
    /// Refuses heights whose stacked witness the commitment does not take.
    pub(super) fn layout(&self, program: &ProgramView<'_>) -> Result<Layout, CpuError> {
        Layout::announced(program, self.taus, self.log_cycles)
    }
}

impl Layout {
    /// The layout a verifier rebuilds from announced heights, its final clock and time zero.
    ///
    /// # Errors
    ///
    /// Refuses a height outside its range, or heights whose stacked witness the commitment does not take.
    pub(crate) fn announced(
        program: &ProgramView<'_>,
        taus: PerTable<usize>,
        log_cycles: usize,
    ) -> Result<Self, CpuError> {
        Self::check_heights(&taus, log_cycles)?;
        // The caps bound each height alone; the stacked size they imply is checked here.
        let layout = Self::new(program, taus, 0, log_cycles);
        if !(crate::pcs::MIN_MU..=crate::pcs::MAX_MU).contains(&layout.shape.mu) {
            return Err(CpuError::WitnessSize { mu: layout.shape.mu });
        }
        Ok(layout)
    }

    /// Check each table's height lies between flock's instance floor and the public cap.
    ///
    /// A table's rows are its class's runs, unbounded by the program's size, so it has a cap of its own, and so has the
    /// register log.
    pub(crate) fn check_heights(taus: &PerTable<usize>, log_cycles: usize) -> Result<(), CpuError> {
        if !(RegisterLog::MIN_LOG_ROWS..=MAX_LOG_ROWS).contains(&log_cycles) {
            return Err(CpuError::LogHeight { log_rows: log_cycles });
        }
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
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn multiplicity_bits_cover_every_read() {
        // Fixture: one table of 2^10 rows, the rest of 2^3.
        let mut taus = PerTable::new([3; N_TABLES]);
        taus[TableId::ALU] = 10;
        let rows: u64 = taus.values().map(|&tau| 1u64 << tau).sum();

        // The bits hold the most reads one entry can get, every row reading it, and no more.
        let bits = Lookup::Bytecode.multiplicity_bits(&taus);
        assert!(rows < 1 << bits);
        assert!(rows >= 1 << (bits - 1));
    }
}
