//! The public proof structure: the global column order, the bus blocks, the producers, and where every claim lands.
//!
//! The verifier rebuilds it from the program and the prover's announced sizes, with no witness value.
//!
//! The blocks name columns by index, so the layout is pure public structure.
//!
//! Each enum's declaration order is protocol order.
//!
//! The Python verifier mirrors it, so reordering a variant changes the proof layout.

use super::MAX_LOG_ROWS;
use super::error::CpuError;
use super::execute::Trace;
use crate::constraints::Claims;
use crate::leaf::{Block, ColumnClaim, Coord, Producer, SparseColumn};
use crate::rv::{self, Reg, Region, RegisterFile, Syscall};
use crate::tables::{self, Part, SEP_BYTECODE, SEP_STATE};
use crate::witness::{self, Placement, Source, StackShape};
use crate::{class_flock, pcs};
use fiat_shamir::transcript::{ProverState, Receiver, Transmitter, VerifierState};
use primitives::field::{F64, F192};
use std::sync::{Arc, OnceLock};

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
    fn tuples(self, p: &rv::Program, ts_final: u64) -> (Vec<Coord>, Vec<Coord>) {
        use Coord::{Col, Const, IntIndex, Sparse};

        // A read-write array: each cell starts at the seed's clock holding `init`.
        //
        // It ends at its last timestamp holding its final word (§sec:memchan).
        let array = |sep: F64, cell: Coord, init: Option<Coord>, ts: Shared, fin: Shared| {
            let seed = [Const(sep), cell.clone(), Const(F64(tables::SEED_CLOCK))]
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
            // The run starts at the entry point and ends on the halt slot; a wrong clock leaves the end unmatched.
            Self::State => (
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
            // Register `i` is cell `i`, starting at zero.
            Self::Registers => {
                let cell = IntIndex {
                    base: F64::ZERO,
                    shift: 0,
                };
                array(tables::SEP_REG, cell, None, Shared::RegTs, Shared::RegFin)
            }
            // RAM starts as the program's image, then zeros, all public.
            Self::Ram => {
                let image = Sparse(Arc::new(SparseColumn::new(p.log_ram(), &[(0, p.image())])));
                array(
                    tables::SEP_MEM,
                    word(Region::RAM.base()),
                    Some(image),
                    Shared::RamTs,
                    Shared::RamFin,
                )
            }
            // The one array seeded from a committed column: the prover's words.
            Self::Advice => array(
                tables::SEP_MEM,
                word(Region::ADVICE.base()),
                Some(Col(Shared::AdvInit.col())),
                Shared::AdvTs,
                Shared::AdvFin,
            ),
        }
    }
}

/// How many public columns a bytecode entry has.
///
/// They are the class tag, `flags`, `a1`, `a2`, `ad`, `imm`, `pc4`, `dt`, `link` and `jalr` (§sec:e2e-bc).
///
/// Then come a zero verdict and the exit selector.
pub const N_BYTECODE_COLUMNS: usize = tables::EXIT_SLOT + 1 - crate::leaf::BYTECODE_PUBLIC_SLOT;

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

    /// How many bits of its multiplicities the array's producer puts on the bus.
    ///
    /// Enough for the most reads tables of these heights can make of it.
    ///
    /// Completeness only: no read count is too large for soundness.
    pub fn multiplicity_bits(self, taus: [usize; tables::N_TABLES]) -> usize {
        match self {
            // Every row reads the bytecode once.
            Self::Bytecode => {
                let rows: u64 = taus.iter().map(|&tau| 1u64 << tau).sum();
                (u64::BITS - rows.leading_zeros()) as usize
            }
        }
    }

    /// The tuple the array's producer pushes for each entry, none of it committed.
    pub fn tuple(self, p: &rv::Program) -> Vec<Coord> {
        match self {
            // Entry `i` at its byte address, four bytes after the preceding one, then the program's public columns.
            Self::Bytecode => {
                let pc = Coord::IntIndex {
                    base: F64(Region::TEXT.base()),
                    shift: 2,
                };
                [Coord::Const(SEP_BYTECODE), pc]
                    .into_iter()
                    .chain(self.columns(p).into_iter().map(|c| Coord::Public(Arc::new(c))))
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
    pub fn table(self, p: &rv::Program) -> Vec<F64> {
        crate::leaf::stacked_bytecode_table(self.log_rows(Sizes::of(p)), &self.tuple(p))
    }

    /// The array's public columns over its entries, in tuple order after the address.
    pub fn columns(self, p: &rv::Program) -> Vec<Vec<F64>> {
        match self {
            // The program's columns, in bytecode slot order.
            Self::Bytecode => {
                let entries = p.entries();
                let column = |f: &(dyn Fn(usize, &rv::Entry) -> u64 + Sync)| {
                    parallel::map_collect(entries.len(), |i| F64(f(i, &entries[i])))
                };
                vec![
                    // An illegal entry's tag is zero, which is no table's: nothing can read it.
                    parallel::map_collect(entries.len(), |i| {
                        tables::table_of(entries[i].class).map_or(F64::ZERO, primitives::field::g_pow)
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
pub(crate) const fn q_column(f: usize) -> usize {
    Q_BASE + f
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
    pub fn of(p: &rv::Program) -> Self {
        Self {
            log_bytecode: crate::log2_strict_usize(p.entries().len()),
            log_ram: p.log_ram(),
            log_advice: p.log_advice(),
        }
    }

    /// Where every column of a program of these sizes sits in the stacked witness, for tables of these heights, and the stack's shape.
    ///
    /// No witness is needed.
    pub(super) fn stack(self, heights: [usize; tables::N_TABLES]) -> (Vec<Placement>, StackShape) {
        witness::placements_of(&self.column_sources(heights))
    }

    /// Every column's source, in global order.
    ///
    /// - The shared columns, at their arrays' sizes.
    /// - The packed witnesses, at their tables' proven sizes times their instance strides.
    /// - Each table's columns, at its proven size.
    ///
    /// A table's columns and packed witnesses commit [`committed_rows`] of their rows (§sec:jagged).
    ///
    /// A circuit word is a port of its class's packed witness, which already holds it.
    ///
    /// So it is never committed again: its bus claims settle against that witness.
    pub(super) fn column_sources(self, heights: [usize; tables::N_TABLES]) -> Vec<Source> {
        let taus: [usize; tables::N_TABLES] = std::array::from_fn(|t| tau_of(t, heights[t]));
        let jagged = |t: usize, stride_log: usize| Source::Committed {
            row_vars: taus[t],
            stride_log,
            rows: committed_rows(heights[t], taus[t]),
        };
        let mut sources: Vec<Source> = Shared::ALL.iter().map(|c| Source::full(c.log_rows(self))).collect();

        // The packed witnesses: every class circuit's, then every clock circuit's.
        sources.extend((0..class_flock::N_FLOCKS).map(|f| {
            let (t, part) = class_flock::flock(f);
            jagged(t, class_flock::stride_log(tables::CLASSES[t], part))
        }));

        // Each table's columns, its circuit words turned into ports of its packed witnesses.
        for (t, table) in tables::tables().iter().enumerate() {
            let base = sources.len();
            sources.resize(base + table.n_committed_columns(), jagged(t, 0));
            for part in [Part::Class, Part::Clock] {
                for (port, c) in table.word_columns(part) {
                    sources[base + c] = Source::Port {
                        column: q_column(class_flock::flock_index(t, part)),
                        port,
                        stride_log: class_flock::stride_log(tables::CLASSES[t], part),
                    };
                }
            }
        }
        debug_assert_eq!(sources.len(), Schema::get().n);
        sources
    }
}

/// A table's base-two logarithm of rows as proven: its height padded to a power of two, and to flock's instance floor.
pub fn tau_of(t: usize, height: usize) -> usize {
    class_flock::n_blocks_log(tables::CLASSES[t], height)
}

/// The rows a table's columns commit: its live rows, then the first padding row, which every later one repeats (§sec:jagged).
pub const fn committed_rows(height: usize, tau: usize) -> usize {
    if height < 1 << tau { height + 1 } else { 1 << tau }
}

/// Where each table's columns sit in the global column order.
///
/// The shared columns and the packed witnesses come first.
///
/// Then each table, in table order, owns a contiguous span of columns.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Schema {
    /// Each table's first column and its number of columns.
    pub spans: [(usize, usize); tables::N_TABLES],
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
            let spans = tables::tables().each_ref().map(|table| {
                let span = (next, table.n_committed_columns());
                next += span.1;
                span
            });
            Self { spans, n: next }
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
    /// Where each column sits in the stacked witness, from the columns' sizes alone.
    pub placements: Vec<Placement>,
    /// The stacked witness's shape: its announced size, and how many lane blocks are committed.
    pub shape: StackShape,
    /// Each table's announced height, its live rows (§sec:jagged).
    pub heights: [usize; tables::N_TABLES],
    /// Each table's base-two logarithm of rows as proven, its height padded.
    pub taus: [usize; tables::N_TABLES],
}

impl Layout {
    /// The layout of a run of `p` with these table heights, ending on clock `ts_final`.
    ///
    /// A table's rows past its height are padding (§sec:jagged): they repeat the row at its height.
    ///
    /// Its bus blocks take the identity there, so the bus is over its live rows.
    pub fn new(p: &rv::Program, heights: [usize; tables::N_TABLES], ts_final: u64) -> Self {
        let sizes = Sizes::of(p);
        let taus: [usize; tables::N_TABLES] = std::array::from_fn(|t| tau_of(t, heights[t]));

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
        for (t, table) in tables::tables().iter().enumerate() {
            let (base, kappa) = (schema.spans[t].0, taus[t]);
            let flushes = table.flushes();
            push.extend(
                flushes
                    .push
                    .into_iter()
                    .map(|c| Block::table(t, kappa, c.into_iter().map(|c| c.offset(base)).collect())),
            );
            pull.extend(
                flushes
                    .pull
                    .into_iter()
                    .map(|c| Block::table(t, kappa, c.into_iter().map(|c| c.offset(base)).collect())),
            );
        }

        // Each lookup array's producer: its tuple, its multiplicity column, and how many bits of it the bus reads.
        let producers = Lookup::ALL
            .into_iter()
            .map(|lookup| Producer {
                kappa: lookup.log_rows(sizes),
                coords: lookup.tuple(p),
                col: lookup.multiplicity().col(),
                bits: lookup.multiplicity_bits(taus),
            })
            .collect();

        let (placements, shape) = sizes.stack(heights);
        Self {
            push,
            pull,
            producers,
            placements,
            shape,
            heights,
            taus,
        }
    }

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

    /// Whether table `t` has padding rows: rows past its height, which repeat the row at its height and which the bus leaves out.
    pub(crate) const fn padded(&self, t: usize) -> bool {
        self.heights[t] < 1 << self.taus[t]
    }

    /// Every claim the opening discharges, located in the stack, in the order that feeds the batch's weights.
    ///
    /// - The bus's framework claims.
    /// - The batch's per-table column claims.
    /// - Each padded table's padding row, at the Boolean point of its height (§sec:jagged).
    /// - The exit's claims: the run halted on `exit`, returning `output` (§sec:e2e-pi).
    ///
    /// Prover and verifier both assemble them here, so no claim can shift by one.
    pub(super) fn opening_claims(
        &self,
        bus_claims: Vec<ColumnClaim>,
        table_claims: &[Claims],
        pads: &[Option<Vec<F192>>],
        output: &[u64; 4],
    ) -> Vec<pcs::SlotClaim> {
        let schema = Schema::get();
        let mut claims = bus_claims;
        claims.reserve(2 * (schema.n - N_SHARED));

        // Each table's column claims, at the batch's point.
        for (&(base, _), table) in schema.spans.iter().zip(table_claims) {
            claims.extend(table.evals.iter().enumerate().map(|(c, &value)| ColumnClaim {
                col: base + c,
                point: table.chi.clone(),
                value,
            }));
        }

        // The row a table's padding rows repeat is the one at its height.
        for (t, (&(base, _), row)) in schema.spans.iter().zip(pads).enumerate() {
            let Some(row) = row else { continue };
            let point = boolean_point(self.heights[t], self.taus[t]);
            claims.extend(row.iter().enumerate().map(|(c, &value)| ColumnClaim {
                col: base + c,
                point: point.clone(),
                value,
            }));
        }

        // The exit: the syscall register holds `exit`, and the output registers the output.
        //
        // Each is the final registers at the Boolean point naming the register.
        // Both parties know the value, so the claim is computed rather than sent.
        let register_claim = |reg: Reg, value: u64| ColumnClaim {
            col: Shared::RegFin.col(),
            point: boolean_point(reg.index(), RegisterFile::LOG_CELLS),
            value: F192::from(F64(value)),
        };
        claims.push(register_claim(Reg::SYSCALL, Syscall::Exit.number()));
        claims.extend(
            Reg::OUTPUTS
                .into_iter()
                .zip(output)
                .map(|(reg, &value)| register_claim(reg, value)),
        );
        claims.into_iter().map(|c| self.slot_claim(c)).collect()
    }

    /// A column claim, located in the stacked witness: one scaled term per piece of the column (§sec:jagged).
    ///
    /// - A committed column's claim weighs its pieces at the claim's point.
    /// - A port has no place of its own: its claim is a strided evaluation of its class's packed witness.
    ///
    /// The strided form freezes the low coordinates to the port's bits and the high ones to the claim's point.
    ///
    /// It is folded at the table's height, not the packed witness's, and joins the one opening.
    fn slot_claim(&self, c: ColumnClaim) -> pcs::SlotClaim {
        let terms = |column: &witness::Column, point: &[F192], low_vars: usize| -> Vec<pcs::Term> {
            column
                .terms(&point[low_vars..], low_vars)
                .into_iter()
                .map(|(offset, n_vars, scale)| pcs::Term { offset, n_vars, scale })
                .collect()
        };
        match &self.placements[c.col] {
            Placement::Committed(column) => pcs::SlotClaim {
                terms: terms(column, &c.point, c.point.len() - column.row_vars),
                point: c.point,
                slot: 0,
                stride_log: 0,
                value: c.value,
            },
            &Placement::Port {
                column,
                port,
                stride_log,
            } => pcs::SlotClaim {
                terms: terms(
                    self.placements[column]
                        .column()
                        .expect("a port is of a committed column"),
                    &c.point,
                    0,
                ),
                point: c.point,
                slot: port,
                stride_log,
                value: c.value,
            },
        }
    }
}

/// The Boolean point of `n` coordinates naming `index`, least significant bit first.
fn boolean_point(index: usize, n: usize) -> Vec<F192> {
    (0..n)
        .map(|bit| if (index >> bit) & 1 == 1 { F192::ONE } else { F192::ZERO })
        .collect()
}

/// A ring-switched claim's terms on a committed column at `suffix_point`, a row's coordinates then the row point: one per piece of the column (§sec:jagged).
pub(super) fn ring_terms(column: &witness::Column, suffix_point: &[F192]) -> Vec<pcs::RingTerm> {
    column
        .terms(&suffix_point[column.stride_log..], column.stride_log)
        .into_iter()
        .map(|(offset, n_vars, scale)| pcs::RingTerm { offset, n_vars, scale })
        .collect()
}

/// The sizes the prover announces before committing: each table's height, the rate, and the final clock.
///
/// The program's own sizes are public, so they are never announced.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) struct Announcement {
    /// Each table's height: its live rows.
    pub(super) heights: [usize; tables::N_TABLES],
    /// The commitment's base-two logarithm of the inverse rate.
    pub(super) log_inv_rate: usize,
    /// The clock the run ended on: the final state's timestamp (§sec:state).
    pub(super) ts_final: u64,
}

impl Announcement {
    /// Write the announcement onto the scalar stream, which binds it into the transcript.
    ///
    /// Heights, not log heights: a table's rows past its height are padding, which the bus leaves out and the commitment stores once (§sec:jagged).
    ///
    /// So the height is what the layout and the bus are made of.
    pub(super) fn write(&self, ps: &mut ProverState) {
        for &height in &self.heights {
            ps.add_scalar(F192::new(height as u64, 0, 0));
        }
        ps.add_scalar(F192::new(self.log_inv_rate as u64, 0, 0));
        ps.add_scalar(F192::new(self.ts_final, 0, 0));
    }

    /// Read an announcement off the scalar stream, and check every value is in range.
    ///
    /// The checks run before any reduction, so an out-of-range announcement costs nothing.
    ///
    /// # Errors
    ///
    /// Refuses a non-canonical size, a final clock that is not live, a table height or a rate outside its range.
    pub(super) fn read(vs: &mut VerifierState) -> Result<Self, CpuError> {
        // A size is a canonical integer in the first coordinate.
        let read_size = |vs: &mut VerifierState| -> Result<usize, CpuError> {
            let word = vs.next_scalar()?;
            if word.c1 != 0 || word.c2 != 0 {
                return Err(CpuError::NonCanonicalSize);
            }
            usize::try_from(word.c0).map_err(|_| CpuError::NonCanonicalSize)
        };
        let mut heights = [0usize; tables::N_TABLES];
        for height in &mut heights {
            *height = read_size(vs)?;
        }
        let log_inv_rate = read_size(vs)?;

        // A live clock at slot zero: neither a padding row's clock nor a failed row's can end the run.
        let ts_final = vs.next_scalar()?;
        let live = ts_final.c0 >> tables::LIVE_BIT == 1 && ts_final.c0.is_multiple_of(tables::CYCLE);
        if !live || ts_final.c1 != 0 || ts_final.c2 != 0 {
            return Err(CpuError::FinalClock);
        }

        // Each table's height at most the public cap.
        //
        // A table's rows are its class's runs, unbounded by the program's size, so it has a cap of its own.
        //
        // Any height below the cap has a layout: the padding rows bring it up to a power of two at or above flock's instance floor.
        for (spec, &rows) in tables::CLASSES.iter().zip(&heights) {
            if rows > 1 << MAX_LOG_ROWS {
                return Err(CpuError::TableHeight {
                    table: spec.name,
                    rows,
                    max: MAX_LOG_ROWS,
                });
            }
        }

        // A rate the commitment supports.
        if !u8::try_from(log_inv_rate).is_ok_and(|r| pcs::Rate::new(r).is_ok()) {
            return Err(CpuError::Rate { log_inv_rate });
        }
        Ok(Self {
            heights,
            log_inv_rate,
            ts_final: ts_final.c0,
        })
    }

    /// The layout the announcement describes for `p`.
    ///
    /// # Errors
    ///
    /// Refuses heights whose stacked witness the commitment does not take.
    pub(super) fn layout(&self, p: &rv::Program) -> Result<Layout, CpuError> {
        // The caps bound each height alone; the stacked size they imply is checked here.
        let layout = Layout::new(p, self.heights, self.ts_final);
        if !(pcs::MIN_MU..=pcs::MAX_MU).contains(&layout.shape.mu) {
            return Err(CpuError::WitnessSize { mu: layout.shape.mu });
        }
        Ok(layout)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn multiplicity_bits_cover_every_read() {
        // Fixture: one table of 2^10 rows, the rest of 2^3.
        let mut taus = [3; tables::N_TABLES];
        taus[0] = 10;
        let rows: u64 = taus.iter().map(|&tau| 1u64 << tau).sum();

        // The bits hold the most reads one entry can get, every row reading it, and no more.
        let bits = Lookup::Bytecode.multiplicity_bits(taus);
        assert!(rows < 1 << bits);
        assert!(rows >= 1 << (bits - 1));
    }
}
