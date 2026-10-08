//! The public proof structure: the global column order, the bus blocks, the producers, and where every claim lands.
//!
//! The verifier rebuilds it from the program and the prover's announced sizes, with no witness value.
//!
//! The blocks name columns by index, so the layout is pure public structure.
//!
//! Each enum's declaration order is protocol order.
//!
//! The Python verifier mirrors it, so reordering a variant changes the proof layout.

use super::error::CpuError;
use super::execute::Trace;
use super::{MAX_LOG_ROWS, UNGROUND_LOG_BYTECODE};
use crate::class_flock::FlockId;
use crate::constraints::{BitColumns, Claims};
use crate::leaf::{Block, ColumnClaim, Coord, Producer, PublicColumn, SparseColumn};
use crate::pcs::{Rate, RingSwitch, SliceClaim, StackClaim};
use crate::rv::{Entry, Reg, Region, RegisterFile, RiscvProgram, Syscall};
use crate::tables::{ClassTable, Clock, N_TABLES, PerTable, Separator, TableId};
use crate::witness::{Placement, Source, StackShape, Window};
use crate::{class_flock, pcs, witness};
use Coord::{Col, Const, IntIndex, Sparse};
use fiat_shamir::MAX_GRINDING_BITS;
use fiat_shamir::arith::Arith;
use fiat_shamir::transcript::{ProverState, Receiver, Transmitter, VerifierState};
use primitives::field::{F64, F192};
use std::sync::{Arc, OnceLock};

// The largest text grinds within the proof of work's window.
const _: () = assert!(Region::TEXT.max_log_words() - UNGROUND_LOG_BYTECODE <= MAX_GRINDING_BITS as usize);

/// The bus blocks no table owns, which each side of the bus starts with.
///
/// Each has a push block and a pull block of the same height.
///
/// - The push block seeds an array, or starts the run.
/// - The pull block finalizes it, or ends the run, with committed columns.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Framework {
    /// The run's boundary: it starts at the entry point on cycle 1 and ends on the halt slot.
    State,
    /// The register file.
    Registers,
    /// RAM.
    Ram,
    /// The advice.
    Advice,
}

impl Framework {
    /// Every framework block, in bus order.
    pub const ALL: [Self; 4] = [Self::State, Self::Registers, Self::Ram, Self::Advice];

    /// Where the final clock sits in the state's finalizing tuple: the run's last state is `(pc, ts)` at slot zero.
    pub(crate) const FINAL_CLOCK: usize = 2;

    /// The base-two logarithm of the block's rows: one per cell of its array.
    pub const fn log_rows(self, sizes: Sizes) -> usize {
        match self {
            Self::State => 0,
            Self::Registers => RegisterFile::LOG_CELLS,
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
            // A wrong clock leaves the end unmatched, and so does a padding row's exit, whose clock is zero.
            Self::State => (
                vec![
                    Separator::State.coordinate(),
                    Const(F64(p.entry_pc())),
                    Const(F64(Clock::CLOCK_START)),
                    Const(F64::ZERO),
                ],
                vec![
                    Separator::State.coordinate(),
                    Const(F64(p.halt_pc())),
                    Const(F64(ts_final)),
                    Const(F64::ONE),
                ],
            ),
            // Register `i` is cell `i`, starting at zero.
            Self::Registers => {
                let cell = IntIndex {
                    base: F64::ZERO,
                    shift: 0,
                };
                array(Separator::Registers.value(), cell, None, Shared::RegTs, Shared::RegFin)
            }
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
}

impl Lookup {
    /// Every lookup array, in producer order.
    pub const ALL: [Self; 1] = [Self::Bytecode];

    /// The base-two logarithm of the array's entries.
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

    /// The proof-of-work bits the bus grinds for this array: one per bit of entries past the most the field alone covers.
    pub const fn grinding_bits(self, sizes: Sizes) -> u32 {
        match self {
            Self::Bytecode => sizes.log_bytecode.saturating_sub(UNGROUND_LOG_BYTECODE) as u32,
        }
    }

    /// How many bits of its multiplicities the array's producer puts on the bus.
    ///
    /// Enough for the most reads tables of these heights can make of it.
    ///
    /// Completeness only: no read count is too large for soundness.
    pub fn multiplicity_bits(self, taus: &PerTable<usize>) -> usize {
        match self {
            // Every row reads the bytecode once.
            Self::Bytecode => {
                let rows: u64 = taus.values().map(|&tau| 1u64 << tau).sum();
                (u64::BITS - rows.leading_zeros()) as usize
            }
        }
    }

    /// The tuple the array's producer pushes for each entry, none of it committed.
    pub fn tuple(self, p: &RiscvProgram) -> Vec<Coord> {
        match self {
            // Entry `i` at its byte address, four bytes after the preceding one, then the program's public columns.
            Self::Bytecode => {
                let pc = Coord::IntIndex {
                    base: F64(Region::TEXT.base()),
                    shift: 2,
                };
                [Separator::Bytecode.coordinate(), pc]
                    .into_iter()
                    .chain(
                        self.columns(p)
                            .into_iter()
                            .map(|c| Coord::Public(PublicColumn::new(Arc::new(c)))),
                    )
                    .collect()
            }
        }
    }

    /// The array's stacked polynomial: its columns at their bus tuple coordinates.
    ///
    /// It makes the array's whole share of a bus leaf one evaluation.
    ///
    /// For the bytecode, it is what an outer verifier is handed in place of a structured program.
    ///
    /// It is also what the program digest binds.
    pub fn table(self, p: &RiscvProgram) -> Vec<F64> {
        crate::leaf::stacked_bytecode_table(self.log_rows(Sizes::of(p)), &self.tuple(p))
    }

    /// The array's public columns over its entries, in tuple order after the address.
    pub fn columns(self, p: &RiscvProgram) -> Vec<Vec<F64>> {
        match self {
            // The program's columns, in bytecode slot order.
            Self::Bytecode => {
                let entries = p.entries();
                let column = |f: &(dyn Fn(usize, &Entry) -> u64 + Sync)| {
                    parallel::map_collect(entries.len(), |i| F64(f(i, &entries[i])))
                };
                vec![
                    // An illegal entry's tag is zero, which is no table's: nothing can read it.
                    parallel::map_collect(entries.len(), |i| {
                        TableId::of(entries[i].class).map_or(F64::ZERO, |t| primitives::field::g_pow(t.index()))
                    }),
                    column(&|_, e| e.flags),
                    column(&|_, e| e.a1 as u64),
                    column(&|_, e| e.a2 as u64),
                    column(&|_, e| e.ad as u64),
                    column(&|_, e| e.imm),
                    column(&|i, _| p.pc_of(i).wrapping_add(4)),
                    column(&|i, _| p.dt_of(i)),
                    column(&|_, _| 0),
                    column(&|_, e| e.is_exit() as u64),
                ]
            }
        }
    }
}

/// The committed columns no table owns, first in the global column order.
///
/// What is committed is what each array holds after the run, and each cell's last timestamp (§sec:memchan).
///
/// - The program is public, not committed: only the multiplicities of its reads are.
/// - The registers start at zero and RAM at the program's image, both public.
/// - The advice is the one array whose initial words are committed too: they are the prover's.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Shared {
    /// Each register's final value.
    RegFin,
    /// Each register's final timestamp, the seed's if never accessed.
    RegTs,
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
    /// How often each bytecode entry is read (§sec:lookup).
    ///
    /// Entry `x`'s word is the integer `m_x`.
    ///
    /// Its bits are the producer's one-bit columns, opened by ring switching.
    BytecodeMult,
}

impl Shared {
    /// Every shared column, in global column order.
    pub const ALL: [Self; 8] = [
        Self::RegFin,
        Self::RegTs,
        Self::RamFin,
        Self::RamTs,
        Self::AdvInit,
        Self::AdvFin,
        Self::AdvTs,
        Self::BytecodeMult,
    ];

    /// The column's global index: its position in the declaration.
    pub const fn col(self) -> usize {
        self as usize
    }

    /// The base-two logarithm of the column's rows: one per cell or entry of its array.
    pub const fn log_rows(self, sizes: Sizes) -> usize {
        match self {
            Self::RegFin | Self::RegTs => Framework::Registers.log_rows(sizes),
            Self::RamFin | Self::RamTs => Framework::Ram.log_rows(sizes),
            Self::AdvInit | Self::AdvFin | Self::AdvTs => Framework::Advice.log_rows(sizes),
            Self::BytecodeMult => Lookup::Bytecode.log_rows(sizes),
        }
    }

    /// The column's values as the run left them.
    ///
    /// A multiplicity column has none: it is counted from the rows.
    pub(super) fn values(self, trace: &Trace) -> Option<&[F64]> {
        Some(match self {
            Self::RegFin => &trace.reg_fin,
            Self::RegTs => &trace.reg_ts,
            Self::RamFin => &trace.ram_fin,
            Self::RamTs => &trace.ram_ts,
            Self::AdvInit => &trace.adv_init,
            Self::AdvFin => &trace.adv_fin,
            Self::AdvTs => &trace.adv_ts,
            Self::BytecodeMult => return None,
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
/// Each table has two packed witnesses: every class circuit's in table order, then every clock circuit's.
///
/// Each is the sole copy of its circuit's words, committed in the same stack as every other column.
pub const Q_BASE: usize = Shared::ALL.len();

/// The columns before the first table's: the shared ones, then the packed witnesses.
pub const N_SHARED: usize = Q_BASE + class_flock::N_FLOCKS;

/// The committed column holding packed witness `f`.
pub(crate) const fn q_column(f: FlockId) -> usize {
    Q_BASE + f.index()
}

/// The program's sizes the layout depends on.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Sizes {
    /// The base-two logarithm of the program's entries.
    pub log_bytecode: usize,
    /// The base-two logarithm of RAM's words.
    pub log_ram: usize,
    /// The base-two logarithm of the advice's words.
    pub log_advice: usize,
}

impl Sizes {
    /// The sizes of `p`.
    pub fn of(p: &RiscvProgram) -> Self {
        Self {
            log_bytecode: crate::log2_strict_usize(p.entries().len()),
            log_ram: p.log_ram(),
            log_advice: p.log_advice(),
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
            for f in FlockId::class(t).into_iter().chain([FlockId::clock(t)]) {
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

/// The public proof structure: everything the verifier rebuilds from the program and the announced sizes.
pub struct Layout {
    /// The push side's blocks: the framework's, then each table's.
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
    /// The committed register words.
    pub(crate) registers: Vec<RegisterWord>,
}

impl Layout {
    /// The layout of a run of `p` with table heights `2^taus`, ending on clock `ts_final`.
    ///
    /// A table's height is its row count: the fill blocks bring every count to a power of two.
    ///
    /// So every row was executed, and no flush has padding tuples to divide back out of the bus.
    pub fn new(p: &RiscvProgram, taus: PerTable<usize>, ts_final: u64) -> Self {
        let sizes = Sizes::of(p);

        // The framework's blocks open both sides, one push and one pull block each.
        let (mut push, mut pull) = (Vec::new(), Vec::new());
        for block in Framework::ALL {
            let kappa = block.log_rows(sizes);
            let (seed, finalize) = block.tuples(p, ts_final);
            push.push(Block::framework(kappa, seed));
            pull.push(Block::framework(kappa, finalize));
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

        // Each lookup array's producer: its tuple, its multiplicity column, and how many bits of it the bus reads.
        let producers = Lookup::ALL
            .into_iter()
            .map(|lookup| Producer {
                kappa: lookup.log_rows(sizes),
                coords: lookup.tuple(p),
                col: lookup.multiplicity().col(),
                bits: lookup.multiplicity_bits(&taus),
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
            registers: RegisterWord::of(&taus),
            taus,
        }
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
    pub(crate) fn rings<E: Copy>(
        &self,
        witnesses: impl IntoIterator<Item = SliceClaim<E>>,
        multiplicities: &[Claims<E>],
        tables: &[Claims<E>],
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
        witnesses.chain(producers).chain(registers).collect()
    }

    /// Every claim the opening discharges, located in the stack, in the order that feeds the batch's weights.
    ///
    /// - The bus's framework claims.
    /// - The batch's per-table column claims.
    /// - The exit's claims: the run halted on `exit`, returning `output` (§sec:e2e-pi).
    ///
    /// Prover and verifiers all assemble them here, so no claim can shift by one.
    pub(crate) fn opening_claims<A: Arith>(
        &self,
        a: &mut A,
        bus_claims: Vec<ColumnClaim<A::E>>,
        table_claims: &[Claims<A::E>],
        output: &[A::E; 4],
    ) -> Vec<StackClaim<A::E>> {
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

        // The exit: the syscall register holds `exit`, and the output registers the output.
        //
        // Each is the final registers at the Boolean point naming the register.
        // Both parties know the value, so the claim is computed rather than sent.
        let exit = a.constant(F192::from(F64(Syscall::Exit.number())));
        let mut register_claim = |reg: Reg, value: A::E| ColumnClaim {
            col: Shared::RegFin.col(),
            point: (0..RegisterFile::LOG_CELLS)
                .map(|b| a.constant(F192::from(F64(((reg.index() >> b) & 1) as u64))))
                .collect(),
            value,
        };
        claims.push(register_claim(Reg::SYSCALL, exit));
        claims.extend((Reg::OUTPUTS.into_iter().zip(output)).map(|(reg, &value)| register_claim(reg, value)));

        // A port's claim is folded at the table's height, not its packed witness's, and joins the one opening.
        //
        // A register number's has no place in the stack: its bits' claim is its table's ring-switched region.
        (claims.into_iter())
            .filter_map(|c| self.placements[c.col].claim(c.point, c.value))
            .collect()
    }
}

/// The sizes the prover announces before committing: each table's height, the rate, and the final clock.
///
/// The program's own sizes are public, so they are never announced.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct Announcement {
    /// Each table's base-two logarithm of rows.
    pub(crate) taus: PerTable<usize>,
    /// The commitment's rate.
    pub(crate) rate: Rate,
    /// The clock the run ended on: the final state's timestamp (§sec:state).
    pub(crate) ts_final: u64,
}

impl Announcement {
    /// The scalars it takes on the stream: each table's height, the rate, then the final clock.
    pub(crate) const LEN: usize = N_TABLES + 2;

    /// The scalars announcing each table's height, then the rate's, each an integer in the first coordinate.
    ///
    /// A height, not a row count: every table's rows are real, filled to a power of two.
    pub(crate) fn sizes(taus: &PerTable<usize>, rate: Rate) -> impl Iterator<Item = F192> {
        let rate = usize::from(rate.log_inv_rate());
        (taus.values().copied().chain([rate])).map(|size| F192::new(size as u64, 0, 0))
    }

    /// Write the announcement onto the scalar stream, which binds it into the transcript.
    pub(super) fn write(&self, ps: &mut ProverState) {
        for size in Self::sizes(&self.taus, self.rate) {
            ps.add_scalar(size);
        }
        ps.add_scalar(F192::new(self.ts_final, 0, 0));
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
    /// Refuses a non-canonical size, a final clock that is not live, a table height or a rate outside its range.
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
        let log_inv_rate = size(&scalars[N_TABLES])?;

        // A live clock at slot zero: neither a padding row's clock nor a failed row's can end the run.
        let ts_final = scalars[N_TABLES + 1];
        let live = ts_final.c0 >> Clock::LIVE_BIT == 1 && ts_final.c0.is_multiple_of(Clock::CYCLE);
        if !live || ts_final.c1 != 0 || ts_final.c2 != 0 {
            return Err(CpuError::FinalClock);
        }

        Layout::check_heights(&taus)?;

        // A rate the commitment supports.
        let rate = (u8::try_from(log_inv_rate).ok())
            .and_then(|r| Rate::new(r).ok())
            .ok_or(CpuError::Rate { log_inv_rate })?;
        Ok(Self {
            taus,
            rate,
            ts_final: ts_final.c0,
        })
    }

    /// The layout the announced heights describe for `p`, its final clock zero.
    ///
    /// The verifier adds the announced clock's share itself.
    ///
    /// # Errors
    ///
    /// Refuses heights whose stacked witness the commitment does not take.
    pub(super) fn layout(&self, p: &RiscvProgram) -> Result<Layout, CpuError> {
        Layout::announced(p, self.taus)
    }
}

impl Layout {
    /// The layout a verifier rebuilds from announced heights, its final clock zero.
    ///
    /// # Errors
    ///
    /// Refuses a height outside its table's range, or heights whose stacked witness the commitment does not take.
    pub(crate) fn announced(p: &RiscvProgram, taus: PerTable<usize>) -> Result<Self, CpuError> {
        Self::check_heights(&taus)?;
        // The caps bound each height alone; the stacked size they imply is checked here.
        let layout = Self::new(p, taus, 0);
        if !(pcs::MIN_MU..=pcs::MAX_MU).contains(&layout.shape.mu) {
            return Err(CpuError::WitnessSize { mu: layout.shape.mu });
        }
        Ok(layout)
    }

    /// Check each table's height lies between flock's instance floor and the public cap.
    ///
    /// A table's rows are its class's runs, unbounded by the program's size, so it has a cap of its own.
    fn check_heights(taus: &PerTable<usize>) -> Result<(), CpuError> {
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
        taus[TableId::ADD] = 10;
        let rows: u64 = taus.values().map(|&tau| 1u64 << tau).sum();

        // The bits hold the most reads one entry can get, every row reading it, and no more.
        let bits = Lookup::Bytecode.multiplicity_bits(&taus);
        assert!(rows < 1 << bits);
        assert!(rows >= 1 << (bits - 1));
    }
}
