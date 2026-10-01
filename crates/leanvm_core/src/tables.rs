//! The instruction tables (`doc/leanvm/body/07-instruction-tables.tex`): one per
//! instruction class ([`crate::rv::Class`]), all of them the same table, which a
//! [`ClassSpec`] specializes. Column indices here are *local*
//! (`0..n_committed_columns`); `cpu`'s schema offsets them to global witness columns.
//!
//! A table does plumbing only. What its class computes is a flock circuit
//! ([`crate::rv::circuits`]), and every word that circuit reads or writes is a
//! VIRTUAL column here: it lives in the circuit's packed witness
//! ([`crate::class_flock`]) and rides the bus from there, in the register and RAM
//! tuples and the bytecode tuple, which is all that binds the circuit to the machine.
//! What a row commits of its own is the rest of its bytecode entry and the old value of
//! what it writes. What orders its accesses in time (§sec:memchan) is a second circuit,
//! its clock circuit, whose words are virtual columns too: the row's clock, each
//! access's previous timestamp, and the bits the row flips in its clock.

use crate::cpu::{HashRow, Row, Trace};
use crate::leaf::Coord::{self, Col, Const, GCol, Prod};
use crate::rv::{self, Class, SINK, hash};
use flock::circuit::{Builder, Circuit};
use primitives::field::{F64, mul_by_g};

// ---- shared bus vocabulary ---------------------------------------------------

/// `g^k` at compile time (`g = x`, so repeated `mul_by_g` from `g^0 = 1`).
const fn g_pow(k: usize) -> F64 {
    let mut acc = F64::ONE;
    let mut i = 0;
    while i < k {
        acc = mul_by_g(acc);
        i += 1;
    }
    acc
}

// Domain separators (coordinate 0 of every bus tuple).
pub(crate) const SEP_STATE: F64 = g_pow(0);
pub(crate) const SEP_MEM: F64 = g_pow(1);
pub(crate) const SEP_BYTECODE: F64 = g_pow(2);
pub(crate) const SEP_REG: F64 = g_pow(3);

// ---- the clock ---------------------------------------------------------------
//
// A timestamp is the integer `2^40 | cycle << 5 | slot`, read as the K word with those bits (§sec:memchan).
//
// ```text
//   bit   63 .. 42   41     40     39 .. 5    4 .. 0
//         zero       fail   live   cycle      slot
// ```
//
// A row's clock has slot zero, so its access in slot `k` is at `ts ^ k`, a column plus a constant.
// Bit 40 tells a real tuple from a padding row's: a seed and every row of the run have it, a padding row's clock is zero.
// Bit 41 is set only in a failed row's next clock, which no row and no boundary pulls.

/// The bit every real timestamp has.
pub const LIVE_BIT: u32 = 40;
/// The bits a row's clock circuit reads of a timestamp: up to the live bit.
pub const CLOCK_BITS: usize = LIVE_BIT as usize + 1;
/// The low bits of a timestamp, which number a row's access slots.
pub const SLOT_BITS: u32 = 5;
/// One cycle of the clock.
pub const CYCLE: u64 = 1 << SLOT_BITS;
/// The bit of a row's next clock that says one of its accesses is out of order.
pub const FAIL_BIT: u32 = LIVE_BIT + 1;
/// The timestamp every cell is seeded at: cycle zero.
pub const SEED_CLOCK: u64 = 1 << LIVE_BIT;
/// The clock the run starts on: cycle 1, so that every access is strictly after the seeds.
pub const CLOCK_START: u64 = SEED_CLOCK | CYCLE;
/// The cycles a run may take: past them the cycle count would carry into the live bit.
pub const MAX_CYCLES: u64 = (1 << (LIVE_BIT - SLOT_BITS)) - 1;

/// A row's clock slots: `rs1`, `rs2`, then `rd` last, after the RAM access if there is one.
/// A row that skips an access leaves its slot unused.
pub const REG_SLOTS: [u32; 3] = [0, 1, 3];
pub const RAM_SLOT: u32 = 2;
/// A hash row reads its two registers, then accesses its block's words in order.
pub const fn block_slot(k: usize) -> u32 {
    2 + k as u32
}

/// A table's clock circuit, for a row whose accesses are in clock slots `slots`.
///
/// Its ports are the row's clock `ts`, then the previous timestamp of each access, then `step`, the bits the row flips in its clock.
/// The next clock is `ts ^ step`: `ts` one cycle on when the row is live, and `ts` itself on a padding row.
/// Bit 41 of `step` is set when an access is out of order, which leaves the next clock outside every clock a row can pull.
///
/// Access `i` is out of order when its previous timestamp disagrees with `ts` on the live bit, or, on a live row, is not strictly below `ts ^ slots[i]`.
/// Every input reads only the bits up to the live bit, the others being forced zero.
pub fn clock_circuit(slots: &[u32]) -> Circuit {
    let mut c = Builder::new(&vec![CLOCK_BITS; 1 + slots.len()], &[CLOCK_BITS + 1]);
    let ts = c.input(0);
    let live = ts[LIVE_BIT as usize];
    let mut in_order = Vec::with_capacity(slots.len());
    let mut disagree = None;
    for (i, &slot) in slots.iter().enumerate() {
        assert!(slot < 1 << SLOT_BITS, "slot {slot} does not fit its bits");
        let prev = c.input(1 + i);
        // Why: `prev < ts ^ slot` exactly when `(ts ^ slot) + !prev` carries out of bit 39, the two agreeing on bit 40.
        let mut carry = None;
        for (bit, &p) in prev[..LIVE_BIT as usize].iter().enumerate() {
            let not_prev = c.not(p);
            carry = if bit >= SLOT_BITS as usize {
                let (x, y) = (c.xor(ts[bit], carry), c.xor(not_prev, carry));
                let majority = c.and(x, y);
                c.xor(majority, carry)
            } else if slot >> bit & 1 == 1 {
                // The slot's bits are constants, so the carry is an OR or an AND.
                c.or(not_prev, carry)
            } else {
                c.and(not_prev, carry)
            };
        }
        in_order.push(carry);
        let differs = c.xor(prev[LIVE_BIT as usize], live);
        disagree = c.or(disagree, differs);
    }
    let ordered = in_order.into_iter().reduce(|x, y| c.and(x, y)).flatten();
    let unordered = c.not(ordered);
    let late = c.and(live, unordered);
    let fail = c.or(late, disagree);
    // The cycle count advances by `live`: bit `j` of `step` is the carry into bit `j`.
    let mut carry = live;
    c.output(0, SLOT_BITS as usize, carry);
    for bit in SLOT_BITS as usize..LIVE_BIT as usize {
        carry = c.and_output(0, bit + 1, ts[bit], carry);
    }
    c.output(0, FAIL_BIT as usize, fail);
    c.finish()
}

/// What a row's clock circuit computes: the bits the row flips in its clock `ts`, its accesses' previous timestamps being `prev`.
pub fn clock_step(ts: u64, prev: &[u64], slots: &[u32]) -> u64 {
    let read = |t: u64| t & ((1 << CLOCK_BITS) - 1);
    let (ts, live) = (read(ts), ts >> LIVE_BIT & 1);
    let low = (1u64 << LIVE_BIT) - 1;
    let fail = prev.iter().zip(slots).any(|(&p, &slot)| {
        let p = read(p);
        let late = p & low >= (ts & low & !(CYCLE - 1)) | u64::from(slot);
        p >> LIVE_BIT != live || live == 1 && late
    });
    let cycles = ts >> SLOT_BITS;
    let carries = ((cycles + live) ^ cycles) & ((1 << (CLOCK_BITS - SLOT_BITS as usize)) - 1);
    carries << SLOT_BITS | u64::from(fail) << FAIL_BIT
}

// ---- flush builder -----------------------------------------------------------

/// Collects a table's push/pull bus interactions in *local* column indices.
pub struct FlushBuilder {
    pub(crate) push: Vec<Vec<Coord>>,
    pub(crate) pull: Vec<Vec<Coord>>,
}

impl FlushBuilder {
    pub(crate) fn new() -> Self {
        Self {
            push: Vec::new(),
            pull: Vec::new(),
        }
    }

    fn pair(&mut self, push: Vec<Coord>, pull: Vec<Coord>) {
        self.push.push(push);
        self.pull.push(pull);
    }

    /// Pull the current state `(pc, ts)` and push the next: `npc`, which a row DERIVES from its
    /// columns rather than committing, and the clock `ts ^ step` its clock circuit gives.
    fn state(&mut self, pc: usize, ts: usize, step: usize, npc: Coord, exit: Coord) {
        self.pair(
            vec![Const(SEP_STATE), npc, Coord::Sum(vec![Col(ts), Col(step)]), exit],
            vec![Const(SEP_STATE), Col(pc), Col(ts), Const(F64::ZERO)],
        );
    }

    /// A read of a lookup array (§sec:lookup): `tuple` as pulled, `tuple[2]` being
    /// its count column `count`, pushed back with the count advanced by ×g.
    fn counted(&mut self, tuple: Vec<Coord>, count: usize) {
        let mut push = tuple.clone();
        push[2] = GCol(count, 1);
        self.pair(push, tuple);
    }

    /// An access, in clock slot `slot`, to the cell `addr` of the array `sep` (§sec:memchan).
    ///
    /// It pulls the cell as its previous access left it, `(prev, old)`, and pushes it back as `(ts ^ slot, new)`.
    /// The row's clock circuit checks that `prev` is the earlier.
    /// A value the row DERIVES rather than commits is passed as its form (§sec:m3).
    #[allow(clippy::too_many_arguments)]
    fn access(&mut self, sep: F64, addr: Coord, ts: usize, slot: u32, prev: usize, old: Coord, new: Coord) {
        let at = match slot {
            0 => Col(ts),
            _ => Coord::Sum(vec![Col(ts), Const(F64(u64::from(slot)))]),
        };
        self.pair(
            vec![Const(sep), addr.clone(), at, new],
            vec![Const(sep), addr, Col(prev), old],
        );
    }
}

// ---- fill context ------------------------------------------------------------

/// Inputs a table needs to fill its columns.
pub struct FillCtx<'a> {
    pub(crate) trace: &'a Trace,
    pub(crate) program: &'a rv::Program,
    /// This table's height `2^tau`, the length of every window in `out`, and its row
    /// count too (`cpu::filler`).
    pub(crate) rows: usize,
    /// Which local columns [`Self::col`] / [`Self::cols`] have written. A fill that
    /// misses one would leave the stacked witness holding uninitialized slots, so
    /// [`fill_table`] checks the whole set was covered.
    written: Vec<std::sync::atomic::AtomicBool>,
    /// The table's column writers, each over a range of rows.
    ///
    /// They run together in one pass, so each row is read once, from cache.
    writers: std::sync::Mutex<Vec<RowsWriter<'a>>>,
}

/// Writes some of a table's columns for a range of its rows.
type RowsWriter<'a> = Box<dyn Fn(std::ops::Range<usize>) + Send + Sync + 'a>;

/// Rows one task of the fill pass takes.
///
/// # Why this value
///
/// - 1024 rows of the trace are about 220 KiB, which stays in L2.
/// - Every writer of the table reads the same rows while they are there.
const FILL_ROWS: usize = 1 << 10;

/// Where one column's values go: its window in the stacked witness, or a private
/// buffer if the column is virtual.
pub type ColumnOut<'a> = &'a mut [F64];

impl<'a> FillCtx<'a> {
    pub(crate) fn new(trace: &'a Trace, program: &'a rv::Program, rows: usize, n_cols: usize) -> Self {
        Self {
            trace,
            program,
            rows,
            written: (0..n_cols).map(|_| false.into()).collect(),
            writers: std::sync::Mutex::new(Vec::new()),
        }
    }

    /// Write local column `at`: `f` over the trace rows.
    fn col<R: Sync>(&self, out: &mut [ColumnOut], rows: &'a [R], at: usize, f: impl Fn(&R) -> F64 + Send + Sync + 'a) {
        self.cols(out, rows, at, move |r| [f(r)]);
    }

    /// Write the `N` local columns at `at..at + N` from one closure per row.
    fn cols<const N: usize, R: Sync>(
        &self,
        out: &mut [ColumnOut],
        rows: &'a [R],
        at: usize,
        f: impl Fn(&R) -> [F64; N] + Send + Sync + 'a,
    ) {
        self.cols_at(out, rows, std::array::from_fn(|k| at + k), f);
    }

    /// Write the `N` local columns `at` from one closure per row.
    ///
    /// The writes are queued, and happen when the table's fill pass runs.
    fn cols_at<const N: usize, R: Sync>(
        &self,
        out: &mut [ColumnOut],
        rows: &'a [R],
        at: [usize; N],
        f: impl Fn(&R) -> [F64; N] + Send + Sync + 'a,
    ) {
        let n = self.rows;
        let dst: [parallel::SendPtr<F64>; N] = at.map(|c| {
            assert_eq!(out[c].len(), n, "column {c} has the wrong window length");
            self.written[c].store(true, std::sync::atomic::Ordering::Relaxed);
            parallel::SendPtr(out[c].as_mut_ptr())
        });
        // A table's height is its row count (`cpu::filler`), so there is nothing to
        // pad with.
        assert_eq!(rows.len(), n, "a table's rows must fill its cube");
        let writer = move |range: std::ops::Range<usize>| {
            for i in range {
                let v = f(&rows[i]);
                for (k, p) in dst.iter().enumerate() {
                    // SAFETY: distinct `i` write disjoint in-bounds slots of each of the
                    // `N` windows, each exactly once. The windows stay borrowed until the
                    // fill pass that runs this writer has joined.
                    unsafe { p.add(i).write(v[k]) };
                }
            }
        };
        self.writers.lock().expect("no writer panicked").push(Box::new(writer));
    }

    /// Run every queued writer, in one parallel pass over the rows.
    fn run(&self) {
        let writers = std::mem::take(&mut *self.writers.lock().expect("no writer panicked"));
        // One task per block of rows; every writer covers the block while its rows are in cache.
        parallel::for_each(self.rows.div_ceil(FILL_ROWS), |task| {
            let range = task * FILL_ROWS..((task + 1) * FILL_ROWS).min(self.rows);
            for writer in &writers {
                writer(range.clone());
            }
        });
    }
}

/// Fill one table's columns and check that every window was written. The stack is
/// allocated uninitialized, so a column the table forgot would be read as
/// indeterminate bytes rather than caught by a length mismatch.
pub(crate) fn fill_table<'a>(table: &'a ClassTable, ctx: &FillCtx<'a>, out: &mut [ColumnOut]) {
    table.fill(ctx, out);
    ctx.run();
    assert_eq!(ctx.written.len(), table.n_committed_columns());
    let all = ctx.written.iter().all(|w| w.load(std::sync::atomic::Ordering::Relaxed));
    assert!(all, "a table left one of its columns unwritten");
}

// ---- the classes -------------------------------------------------------------

/// A word one of a table's circuits reads or writes, which is a virtual column of the table.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Word {
    /// The row's clock, an input of its clock circuit.
    Clock,
    /// The timestamp access `i` pulls, the previous one of its cell.
    Prev(u8),
    /// The bits the row flips in its clock, which the clock circuit computes.
    Step,
    /// The bytecode's selector bits and immediate.
    Flags,
    Imm,
    /// The two registers read.
    V1,
    V2,
    /// What the class computes.
    Out,
    /// Whether the branch is taken, 0 or 1.
    Taken,
    /// A load's or a store's bus address.
    Address,
    /// Word `k` of the RAM cells the row names, as the row found it: the one cell of
    /// a load or a store, or one of the hash's block ([`Ram::Block`]).
    Cell(u8),
    /// What the row leaves in word `k`.
    CellNew(u8),
    /// What a circuit asserts to be zero: the row puts it in its bytecode tuple, in a
    /// slot where the program holds zero, so the lookup is what makes it zero.
    Bad,
    /// What the prover tells the circuit beyond the row: in its witness, in no column.
    HintQ,
    HintR,
}

/// How a class uses RAM.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Ram {
    None,
    /// One cell read, in clock slot 2, at the address the circuit computes.
    Read,
    /// One cell read and rewritten.
    Write,
    /// The hash's block: word `k` is the cell at `v1 ^ 8k`, in clock slot `2 + k`.
    ///
    /// The result's four words are rewritten.
    Block,
}

/// One instance's `z`, `A·z` and `B·z` from its input words, into zeroed buffers.
pub type InstanceWitness = fn(&[u64], &mut [u64], &mut [u64], &mut [u64]);

/// What specializes the class table to one instruction class.
pub struct ClassSpec {
    pub class: Class,
    pub name: &'static str,
    /// Branches and jumps: the bytecode's `dt`, `link` and `jalr` fields, and the
    /// circuit's `taken` word. Without them the next `pc` is `pc + 4` and `rd`
    /// receives `out`.
    pub control: bool,
    /// Whether the row reads `rs2`, in clock slot 1.
    /// A load decodes with `x0` there, and its circuit takes no `v2`.
    pub reads_rs2: bool,
    /// Whether the row writes `rd`, in clock slot 3.
    /// A store's and a hash's destination is the sink, which nothing reads.
    ///
    /// A row that skips either reads its register number off the entry as a constant.
    pub writes_rd: bool,
    pub ram: Ram,
    pub circuit: fn() -> Circuit,
    /// One instance's witness by word arithmetic, when the class has it.
    ///
    /// It writes what the walk of the circuit's gate list would, which a test pins.
    pub witness: Option<InstanceWitness>,
    /// `log2` of the bits one instance of the circuit occupies. A constant, because
    /// the layout needs it before any circuit is built; [`crate::class_flock`] checks it.
    pub k_log: usize,
    /// The circuit's port words in order, the first `n_inputs` of them its inputs.
    pub ports: &'static [Word],
    pub n_inputs: usize,
    /// `log2` of the bits one instance of the table's clock circuit occupies, checked like `k_log`.
    pub clock_k_log: usize,
}

impl ClassSpec {
    /// The register accesses the row makes, in column order: `rs1`, then `rs2` and `rd` if it makes them.
    ///
    /// Each is an index into the entry's three register cells and into the register slots.
    pub const fn registers(&self) -> &'static [usize] {
        match (self.reads_rs2, self.writes_rd) {
            (true, true) => &[0, 1, 2],
            (true, false) => &[0, 1],
            (false, true) => &[0, 2],
            (false, false) => &[0],
        }
    }

    /// The clock slots of the row's RAM accesses.
    const fn ram_slots(&self) -> std::ops::Range<u32> {
        match self.ram {
            Ram::None => 0..0,
            Ram::Read | Ram::Write => RAM_SLOT..RAM_SLOT + 1,
            Ram::Block => block_slot(0)..block_slot(hash::WORDS),
        }
    }

    /// Accesses per row: the registers', then RAM's.
    pub const fn n_accesses(&self) -> usize {
        let ram = self.ram_slots();
        self.registers().len() + (ram.end - ram.start) as usize
    }

    /// The clock slots of the row's accesses, in the order of their columns.
    pub fn slots(&self) -> Vec<u32> {
        let registers = self.registers().iter().map(|&i| REG_SLOTS[i]);
        registers.chain(self.ram_slots()).collect()
    }

    /// The clock circuit's port words: the clock, each access's previous timestamp, then the step.
    pub fn clock_ports(&self) -> Vec<Word> {
        let prev = (0..self.n_accesses()).map(|i| Word::Prev(i as u8));
        std::iter::once(Word::Clock).chain(prev).chain([Word::Step]).collect()
    }
}

pub static ALU: ClassSpec = ClassSpec {
    class: Class::Alu,
    name: "ALU",
    control: true,
    reads_rs2: true,
    writes_rd: true,
    ram: Ram::None,
    circuit: rv::circuits::alu,
    witness: None,
    k_log: 10,
    ports: &[Word::V1, Word::V2, Word::Imm, Word::Flags, Word::Out, Word::Taken],
    n_inputs: 4,
    clock_k_log: 9,
};
pub static LOAD: ClassSpec = ClassSpec {
    class: Class::Load,
    name: "LOAD",
    control: false,
    reads_rs2: false,
    writes_rd: true,
    ram: Ram::Read,
    circuit: rv::circuits::load,
    witness: None,
    k_log: 10,
    ports: &[
        Word::V1,
        Word::Imm,
        Word::Flags,
        Word::Cell(0),
        Word::Address,
        Word::Out,
    ],
    n_inputs: 4,
    clock_k_log: 9,
};
pub static STORE: ClassSpec = ClassSpec {
    class: Class::Store,
    name: "STORE",
    control: false,
    reads_rs2: true,
    writes_rd: false,
    ram: Ram::Write,
    circuit: rv::circuits::store,
    witness: None,
    k_log: 10,
    ports: &[
        Word::V1,
        Word::V2,
        Word::Imm,
        Word::Flags,
        Word::Cell(0),
        Word::Address,
        Word::CellNew(0),
    ],
    n_inputs: 5,
    clock_k_log: 9,
};

pub static SHIFT: ClassSpec = ClassSpec {
    class: Class::Shift,
    name: "SHIFT",
    control: false,
    reads_rs2: true,
    writes_rd: true,
    ram: Ram::None,
    circuit: rv::circuits::shift,
    witness: None,
    k_log: 10,
    ports: &[Word::V1, Word::V2, Word::Imm, Word::Flags, Word::Out],
    n_inputs: 4,
    clock_k_log: 9,
};
pub static MUL: ClassSpec = ClassSpec {
    class: Class::Mul,
    name: "MUL",
    control: false,
    reads_rs2: true,
    writes_rd: true,
    ram: Ram::None,
    circuit: rv::circuits::mul,
    witness: None,
    k_log: 12,
    ports: &[Word::V1, Word::V2, Word::Flags, Word::Out],
    n_inputs: 3,
    clock_k_log: 9,
};
pub static MULH: ClassSpec = ClassSpec {
    class: Class::Mulh,
    name: "MULH",
    control: false,
    reads_rs2: true,
    writes_rd: true,
    ram: Ram::None,
    circuit: rv::circuits::mulh,
    witness: None,
    k_log: 13,
    ports: &[Word::V1, Word::V2, Word::Flags, Word::Out],
    n_inputs: 3,
    clock_k_log: 9,
};

pub static DIV: ClassSpec = ClassSpec {
    class: Class::Div,
    name: "DIV",
    control: false,
    reads_rs2: true,
    writes_rd: true,
    ram: Ram::None,
    circuit: rv::circuits::div,
    witness: None,
    k_log: 13,
    ports: &[
        Word::V1,
        Word::V2,
        Word::Flags,
        Word::HintQ,
        Word::HintR,
        Word::Out,
        Word::Bad,
    ],
    n_inputs: 5,
    clock_k_log: 9,
};

/// The BLAKE2s precompile ([`hash`]): the counter is `v2`, the finalization word the
/// flags, and the block's words are the row's cells, the result's four rewritten.
pub static HASH: ClassSpec = ClassSpec {
    class: Class::Hash,
    name: "HASH",
    control: false,
    reads_rs2: true,
    writes_rd: false,
    ram: Ram::Block,
    circuit: rv::circuits::blake2s,
    witness: Some(rv::circuits::blake2s_witness),
    k_log: 14,
    ports: &[
        Word::V2,
        Word::Flags,
        Word::Cell(0),
        Word::Cell(1),
        Word::Cell(2),
        Word::Cell(3),
        Word::Cell(8),
        Word::Cell(9),
        Word::Cell(10),
        Word::Cell(11),
        Word::Cell(12),
        Word::Cell(13),
        Word::Cell(14),
        Word::Cell(15),
        Word::CellNew(4),
        Word::CellNew(5),
        Word::CellNew(6),
        Word::CellNew(7),
    ],
    n_inputs: 14,
    clock_k_log: 11,
};

/// The tables, in the order of `row_counts` / `taus` throughout `cpu`. Table `t`'s
/// class tag in the bytecode is `g^t`.
pub const N_TABLES: usize = 8;
pub static CLASSES: [&ClassSpec; N_TABLES] = [&ALU, &LOAD, &STORE, &SHIFT, &MUL, &MULH, &DIV, &HASH];

/// The table running `class`, if it has one yet.
pub fn table_of(class: Class) -> Option<usize> {
    CLASSES.iter().position(|spec| spec.class == class)
}

/// The class tables, in [`CLASSES`] order.
pub fn tables() -> &'static [ClassTable; N_TABLES] {
    static TABLES: std::sync::OnceLock<[ClassTable; N_TABLES]> = std::sync::OnceLock::new();
    TABLES.get_or_init(|| std::array::from_fn(ClassTable::new))
}

/// The slot of a bytecode tuple that holds a row's [`Word::Bad`]: past every field of
/// an entry, where the program is zero.
pub const BAD_SLOT: usize = 13;

/// Bytecode slot binding the exit selector.
pub const EXIT_SLOT: usize = 14;

/// The `rs2` read's columns: the register's number and what it held.
#[derive(Clone, Copy)]
struct Rs2Cols {
    a2: usize,
    v2: usize,
}

/// The register write's columns: the cell written, what it held, and the class's result.
#[derive(Clone, Copy)]
struct RdCols {
    ad: usize,
    vd_old: usize,
    out: usize,
}

/// A branch's or a jump's columns: the bytecode's target offset, link and indirect-jump
/// selectors, the circuit's taken bit, and the exit selector.
#[derive(Clone, Copy)]
struct ControlCols {
    dt: usize,
    link: usize,
    jalr: usize,
    taken: usize,
    exit: usize,
}

/// A load's or a store's columns: the bus address, the cell as the row found it, and
/// what the row leaves there, which for a load is the cell itself.
#[derive(Clone, Copy)]
struct RamCols {
    address: usize,
    cell: usize,
    new: usize,
}

/// The hash's columns: the block's sixteen words as found, then the four it rewrites.
#[derive(Clone, Copy)]
struct BlockCols {
    words: usize,
    out: usize,
}

impl BlockCols {
    /// What the row leaves in word `k` of its block.
    fn left(&self, k: usize) -> usize {
        match k.wrapping_sub(hash::OUT as usize / 8) {
            j if j < 4 => self.out + j,
            _ => self.words + k,
        }
    }
}

/// A class table's local columns: `pc, ts, a1, pc4, v1, flags`, then the optional groups.
///
/// The groups are in the order of the fields below, then come the accesses' previous timestamps, the clock's step and the bytecode read's count.
#[derive(Clone, Copy)]
struct Cols {
    pc: usize,
    ts: usize,
    // The bytecode entry's fields that are no circuit word.
    a1: usize,
    pc4: usize,
    v1: usize,
    flags: usize,
    rs2: Option<Rs2Cols>,
    rd: Option<RdCols>,
    control: Option<ControlCols>,
    /// The immediate, which a hash row has not.
    imm: Option<usize>,
    ram: Option<RamCols>,
    block: Option<BlockCols>,
    bad: Option<usize>,
    /// The first access's previous timestamp, the others following it.
    prev: usize,
    step: usize,
    /// The bytecode read's count, the last column.
    rbc: usize,
}

impl Cols {
    fn new(spec: &ClassSpec) -> Self {
        let mut next = 0;
        let mut take = |n: usize| {
            next += n;
            next - n
        };
        let (pc, ts, a1, pc4, v1, flags) = (take(1), take(1), take(1), take(1), take(1), take(1));
        let rs2 = spec.reads_rs2.then(|| Rs2Cols {
            a2: take(1),
            v2: take(1),
        });
        let rd = spec.writes_rd.then(|| RdCols {
            ad: take(1),
            vd_old: take(1),
            out: take(1),
        });
        let control = spec.control.then(|| ControlCols {
            dt: take(1),
            link: take(1),
            jalr: take(1),
            taken: take(1),
            exit: take(1),
        });
        let imm = spec.ports.contains(&Word::Imm).then(|| take(1));
        let (ram, block) = match spec.ram {
            Ram::None => (None, None),
            Ram::Read | Ram::Write => {
                let (address, cell) = (take(1), take(1));
                let new = if spec.ram == Ram::Write { take(1) } else { cell };
                (Some(RamCols { address, cell, new }), None)
            }
            Ram::Block => {
                let words = take(hash::WORDS);
                (None, Some(BlockCols { words, out: take(4) }))
            }
        };
        let bad = spec.ports.contains(&Word::Bad).then(|| take(1));
        let (prev, step) = (take(spec.n_accesses()), take(1));
        Self {
            pc,
            ts,
            a1,
            pc4,
            v1,
            flags,
            rs2,
            rd,
            control,
            imm,
            ram,
            block,
            bad,
            prev,
            step,
            rbc: take(1),
        }
    }

    /// The word's column, if it has one: a hint has none.
    fn word(&self, word: Word) -> Option<usize> {
        let missing = || -> usize { panic!("the class has no {word:?} word") };
        Some(match word {
            Word::Clock => self.ts,
            Word::Prev(i) => self.prev + i as usize,
            Word::Step => self.step,
            Word::Flags => self.flags,
            Word::Imm => self.imm.unwrap_or_else(missing),
            Word::V1 => self.v1,
            Word::V2 => self.rs2.map_or_else(missing, |r| r.v2),
            Word::Out => self.rd.map_or_else(missing, |rd| rd.out),
            Word::Taken => self.control.map_or_else(missing, |c| c.taken),
            Word::Address => self.ram.map_or_else(missing, |r| r.address),
            Word::Cell(k) => match (self.ram, self.block) {
                (Some(ram), _) => ram.cell,
                (_, Some(block)) => block.words + k as usize,
                _ => missing(),
            },
            Word::CellNew(k) => match (self.ram, self.block) {
                (Some(ram), _) => ram.new,
                (_, Some(block)) => block.left(k as usize),
                _ => missing(),
            },
            Word::Bad => self.bad.unwrap_or_else(missing),
            Word::HintQ | Word::HintR => return None,
        })
    }
}

/// One of the two flock circuits of a table: its class's function, or its clock.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Part {
    Class,
    Clock,
}

/// The table of one instruction class (§sec:tables): the state step, the bytecode read, and the accesses.
/// Its column indices are local (`0..n_committed_columns`).
pub struct ClassTable {
    index: usize,
    spec: &'static ClassSpec,
    cols: Cols,
    clock_ports: Vec<Word>,
}

impl ClassTable {
    fn new(index: usize) -> Self {
        let spec = CLASSES[index];
        let cols = Cols::new(spec);
        // Invariant: a register access exists exactly when its value is a circuit word.
        assert_eq!(
            spec.reads_rs2,
            spec.ports.contains(&Word::V2),
            "{}: rs2 read",
            spec.name
        );
        assert_eq!(
            spec.writes_rd,
            spec.ports.contains(&Word::Out),
            "{}: rd write",
            spec.name
        );
        Self {
            index,
            spec,
            cols,
            clock_ports: spec.clock_ports(),
        }
    }

    /// Number of columns, the virtual ones included.
    pub fn n_committed_columns(&self) -> usize {
        self.cols.rbc + 1
    }

    /// The read-count columns: the `g^{count}` values of the table's lookups into the
    /// bytecode, each with a single-column block of the count side of the bus.
    pub fn count_columns(&self) -> [usize; 1] {
        [self.cols.rbc]
    }

    /// The port words of one of the table's circuits.
    pub fn ports(&self, part: Part) -> &[Word] {
        match part {
            Part::Class => self.spec.ports,
            Part::Clock => &self.clock_ports,
        }
    }

    /// One circuit's words that are columns, as `(port, local column)`.
    pub(crate) fn word_columns(&self, part: Part) -> impl Iterator<Item = (usize, usize)> + '_ {
        let ports = self.ports(part).iter().enumerate();
        ports.filter_map(|(port, &w)| Some((port, self.cols.word(w)?)))
    }

    /// The table's bus interactions, in local column indices.
    pub(crate) fn flushes(&self) -> FlushBuilder {
        let mut f = FlushBuilder::new();
        let c = &self.cols;
        // What the row derives: the next `pc`, `pc4 + taken·dt + jalr·(out + pc4)`, and
        // what `rd` receives, `out + link·(out + pc4)`, each of degree 2 (§sec:m3).
        let (npc, vd, control) = match (c.control, c.rd) {
            (Some(k), Some(rd)) => (
                Coord::Sum(vec![
                    Col(c.pc4),
                    Prod(k.taken, k.dt),
                    Prod(k.jalr, rd.out),
                    Prod(k.jalr, c.pc4),
                ]),
                Some(Coord::Sum(vec![Col(rd.out), Prod(k.link, rd.out), Prod(k.link, c.pc4)])),
                vec![Col(k.dt), Col(k.link), Col(k.jalr)],
            ),
            (_, rd) => (Col(c.pc4), rd.map(|rd| Col(rd.out)), Vec::new()),
        };
        // Only an exit marks its next state, `exit·(ts ^ step)`, which only the final state meets.
        let exit = c.control.map_or(Const(F64::ZERO), |k| {
            Coord::Sum(vec![Prod(k.exit, c.ts), Prod(k.exit, c.step)])
        });
        f.state(c.pc, c.ts, c.step, npc, exit);
        // A row without an `rs2` read, an `rd` write or an immediate reads its constant off the entry.
        // Those constants are `x0`, the sink, and zero.
        let mut entry = vec![
            Const(SEP_BYTECODE),
            Col(c.pc),
            Col(c.rbc),
            Const(g_pow(self.index)),
            Col(c.flags),
            Col(c.a1),
            c.rs2.map_or(Const(F64::ZERO), |r| Col(r.a2)),
            c.rd.map_or(Const(F64(SINK as u64)), |rd| Col(rd.ad)),
            c.imm.map_or(Const(F64::ZERO), Col),
            Col(c.pc4),
        ];
        entry.extend(control);
        if let Some(bad) = c.bad {
            entry.resize(BAD_SLOT, Const(F64::ZERO));
            entry.push(Col(bad));
        }
        entry.resize(EXIT_SLOT, Const(F64::ZERO));
        entry.push(c.control.map_or(Const(F64::ZERO), |k| Col(k.exit)));
        f.counted(entry, c.rbc);
        // The accesses' columns are in the order the row makes them.
        let mut slots = self.spec.slots().into_iter().enumerate();
        let mut access = |f: &mut FlushBuilder, sep: F64, addr: Coord, old: Coord, new: Coord| {
            let (i, slot) = slots.next().expect("one slot per access");
            f.access(sep, addr, c.ts, slot, c.prev + i, old, new);
        };
        access(&mut f, SEP_REG, Col(c.a1), Col(c.v1), Col(c.v1));
        if let Some(r) = c.rs2 {
            access(&mut f, SEP_REG, Col(r.a2), Col(r.v2), Col(r.v2));
        }
        if let (Some(rd), Some(vd)) = (c.rd, vd) {
            access(&mut f, SEP_REG, Col(rd.ad), Col(rd.vd_old), vd);
        }
        // The cell a load or a store names is the circuit's word, so an access outside
        // RAM, or a misaligned one, pulls a tuple nothing pushed.
        if let Some(ram) = c.ram {
            access(&mut f, SEP_MEM, Col(ram.address), Col(ram.cell), Col(ram.new));
        }
        // The hash's block: word `k` at `v1 ^ 8k`, which is `v1 + 8k` in the field.
        if let Some(block) = c.block {
            for k in 0..hash::WORDS {
                let addr = Coord::Sum(vec![Col(c.v1), Const(F64(8 * k as u64))]);
                access(&mut f, SEP_MEM, addr, Col(block.words + k), Col(block.left(k)));
            }
        }
        f
    }

    /// Fill this table's columns from the trace: `out[i]` is local column `i`'s
    /// window, already at its final length. Every window must be written in full,
    /// which `fill_table` checks.
    fn fill<'a>(&'a self, ctx: &FillCtx<'a>, out: &mut [ColumnOut]) {
        let c = &self.cols;
        let rows: &[Row] = &ctx.trace.rows[self.index];
        let p = ctx.program;
        let entry = move |r: &Row| &p.entries[r.index as usize];
        ctx.cols(out, rows, c.pc, move |r| {
            let (e, pc) = (entry(r), p.pc_of(r.index as usize));
            [
                F64(pc),
                F64(r.ts),
                F64(e.a1 as u64),
                F64(pc.wrapping_add(4)),
                F64(r.v1),
                F64(e.flags),
            ]
        });
        if let Some(rs2) = c.rs2 {
            ctx.cols_at(out, rows, [rs2.a2, rs2.v2], move |r| {
                [F64(entry(r).a2 as u64), F64(r.v2)]
            });
        }
        if let Some(rd) = c.rd {
            ctx.cols_at(out, rows, [rd.ad, rd.vd_old, rd.out], move |r| {
                [F64(entry(r).ad as u64), F64(r.vd_old), F64(r.out)]
            });
        }
        if let Some(k) = c.control {
            ctx.cols_at(out, rows, [k.dt, k.link, k.jalr, k.taken, k.exit], move |r| {
                let e = entry(r);
                [
                    F64(p.dt_of(r.index as usize)),
                    F64(e.link as u64),
                    F64(e.jalr as u64),
                    F64(r.taken as u64),
                    F64((e.target == rv::Target::Halt) as u64),
                ]
            });
        }
        if let Some(imm) = c.imm {
            ctx.col(out, rows, imm, move |r| F64(entry(r).imm));
        }
        if let Some(ram) = c.ram {
            ctx.cols_at(out, rows, [ram.address, ram.cell], move |r| {
                [F64(r.ram.address), F64(r.ram.old)]
            });
            if ram.new != ram.cell {
                ctx.col(out, rows, ram.new, move |r| F64(r.ram.new));
            }
        }
        if let Some(block) = c.block {
            fn hash(r: &Row) -> &HashRow {
                r.hash.as_ref().expect("a hash row has its block")
            }
            ctx.cols(out, rows, block.words, move |r| hash(r).block.map(F64));
            ctx.cols(out, rows, block.out, |r| hash(r).out.map(F64));
        }
        if let Some(bad) = c.bad {
            ctx.col(out, rows, bad, move |_| F64::ZERO);
        }
        let n = self.spec.n_accesses();
        for i in 0..n {
            ctx.col(out, rows, c.prev + i, move |r| F64(r.prev()[i]));
        }
        let slots = self.spec.slots();
        ctx.col(out, rows, c.step, move |r| {
            F64(clock_step(r.ts, &r.prev()[..n], &slots))
        });
        ctx.col(out, rows, c.rbc, move |r| r.bytecode_read);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn the_clock_circuit_is_its_reference() {
        // Invariant: the clock circuit computes what the executor and the tables put in its step port.
        //
        // Fixture state: a row at cycle 1000 whose three accesses (slots 0, 1, 3) were last at cycles 999 and 1000.
        // Mutation: every previous timestamp swept around the row's own, the live bit flipped, and a padding row.
        let slots = [0, 1, 3];
        let circuit = clock_circuit(&slots);
        let ts = SEED_CLOCK | (1000 * CYCLE);
        let honest = [ts - CYCLE + 3, ts - CYCLE + 1, ts];
        let mut cases = vec![(ts, honest), (0, [0; 3]), ((MAX_CYCLES * CYCLE) | SEED_CLOCK, honest)];
        for i in 0..3 {
            for delta in [0, 1, 2, 3, 4, CYCLE] {
                for prev in [
                    ts ^ u64::from(slots[i]),
                    ts + delta,
                    ts - delta,
                    (ts - delta) ^ SEED_CLOCK,
                ] {
                    let mut case = honest;
                    case[i] = prev;
                    cases.push((ts, case));
                    cases.push((ts ^ SEED_CLOCK, case));
                }
            }
        }
        let words = (1usize << circuit.k_log()) / 64;
        for (ts, prev) in cases {
            let (mut z, mut az, mut bz) = (vec![0; words], vec![0; words], vec![0; words]);
            let inputs = [ts, prev[0], prev[1], prev[2]];
            circuit.witness_instance(&inputs, &mut z, &mut az, &mut bz);
            assert_eq!(z[4], clock_step(ts, &prev, &slots), "ts {ts:#x}, prev {prev:x?}");
        }
        assert_eq!(
            clock_step(ts, &honest, &slots),
            CYCLE,
            "an honest row advances one cycle"
        );
    }
}
