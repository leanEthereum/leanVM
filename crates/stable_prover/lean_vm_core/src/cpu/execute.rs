//! The write-once interpreter: run the program, with its hints, to the final memory image and the per-opcode
//! [`Trace`]. Its Lean transcription is `formal/Statement/Prover/Execute.lean`: a change here lands there too.

use super::hints::{BitsDest, GPow, MAX_CELLS, MAX_INDEX, QuickMap, RHint, bounded_dlog};
use super::*;
use isa::{pretty_f64, pretty_integer};
use primitives::field::{F64, F128};

/// A run of a program.
pub struct Execution {
    /// The final memory image, a power of two cells.
    pub mem: Memory,
    /// Instructions executed.
    pub cycles: usize,
    /// Cells the run touched, before the pad of `mem`.
    pub mem_used: usize,
    /// Cells an instruction read before anything wrote them, so the value it read was zero here and prover-chosen
    /// in a proof: the bus only forces the accesses to one address to agree, never that it was written. A non-empty
    /// list means a live value came from outside the constraint system: the source read a cell nothing stores, or
    /// the lowering dropped or misplaced a store. A range-check touch, which only links its two cells, and an
    /// arithmetic back-solve, which writes its operand first, read none.
    pub unconstrained_reads: Vec<u32>,
    pub(crate) trace: Trace,
}

impl Execution {
    /// Rows per table: the instructions of each opcode the run executed.
    pub fn rows(&self) -> [usize; crate::tables::N_TABLES] {
        self.trace.row_counts()
    }
}

/// A cell's write state. A cell not `Written` holds zero; a `DEREF` between two
/// unwritten cells links them, and a write to either reaches the other at once.
#[derive(Clone, Copy, PartialEq, Eq)]
enum State {
    Unwritten,
    Linked,
    Written,
}

/// One cell: its word, its access count as an exponent (the column holds `g^count`),
/// and its write state.
#[derive(Clone, Copy)]
pub(crate) struct Cell {
    pub(crate) word: F128,
    pub(crate) count: u32,
    state: State,
}

impl Cell {
    pub(crate) const UNWRITTEN: Self = Self {
        word: F128::ZERO,
        count: 0,
        state: State::Unwritten,
    };
}

/// The write-once data memory: `len` cells, a power of two. Cells past those the run
/// touched are unwritten and never accessed.
pub struct Memory {
    pages: Vec<Vec<Cell>>,
    len: usize,
}

/// `log2` of the cells in a page: the memory grows a page at a time, so growing it never copies it.
const PAGE_LOG: usize = 16;

impl Memory {
    /// Cells in the image, its power-of-two pad included.
    pub fn len(&self) -> usize {
        self.len
    }

    pub fn is_empty(&self) -> bool {
        self.len == 0
    }

    /// The word in cell `i`.
    pub fn word(&self, i: usize) -> F128 {
        self.cell(i).word
    }

    /// Cell `i`.
    pub(crate) fn cell(&self, i: usize) -> Cell {
        self.pages
            .get(i >> PAGE_LOG)
            .map_or(Cell::UNWRITTEN, |page| page[i & ((1 << PAGE_LOG) - 1)])
    }
}

/// Why a run has no execution the interpreter can find: the program, on this public
/// input and advice, asks for something the machine cannot do.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ExecError {
    /// The instruction the run failed at, or whose hints it failed in.
    pub pc: u32,
    /// Its function and source line ([`isa::CompiledProgram::site_at`]).
    pub site: String,
    pub fault: Fault,
}

/// What the run asked for that the machine cannot do.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Fault {
    /// A second value for a written cell: a failed `assert`, two writes that disagree,
    /// or a write to a cell an instruction already read, unwritten, as zero. `hint`
    /// names the hint that wrote it, if one did.
    Conflict {
        cell: u32,
        had: F128,
        new: F128,
        hint: Option<&'static str>,
    },
    /// A `DEREF` whose address, the pointer times `g^o2`, is no g-power below `MAX_CELLS`: a wild
    /// pointer, a failed range check, or an address past any memory a stack can hold.
    WildPointer { value: F128 },
    /// A word that has to be in `K` is not: a `JUMP` operand, or one a hint reads.
    NotInK { what: &'static str, value: F128 },
    /// A word that has to be an address or a count is not a g-power in its range.
    NotAGPower { what: &'static str, value: F64 },
    /// A `MUL` asked to solve `a·x = c` for `x` with `a = 0`.
    BackSolveThroughZero,
    /// The advice does not fit the program: a witness stream is missing, given
    /// twice or exhausted, or an entry has the wrong length.
    Witness(String),
    /// The program allocates or accesses a cell past any memory a stack can hold (`MAX_CELLS`).
    OutOfMemory,
    /// The halt `pc` reached in a frame other than `main`'s.
    HaltOutsideMain { fp: u32 },
    /// Too many instructions: runaway recursion, or a loop that never ends.
    StepLimit,
}

/// The longest run the interpreter executes, the longest a stack can commit: every step is a row
/// of at least `MIN_COMMITTED_COLUMNS` committed columns.
const MAX_STEPS: usize = (1 << verifier::MAX_STACKED_LOG) / crate::tables::MIN_COMMITTED_COLUMNS;
// A row touches at most a `KECCAK` row's cells, so every access count fits the `u32` exponent.
const _: () = assert!(crate::keccak::ROW_CELLS * MAX_STEPS < u32::MAX as usize);

impl ExecError {
    #[cold]
    fn new(program: &Program, pc: u32, fault: Fault) -> Self {
        Self {
            pc,
            site: program.site_at(pc),
            fault,
        }
    }
}

impl std::fmt::Display for ExecError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{} at pc {} (in {})", self.fault, self.pc, self.site)
    }
}

impl std::error::Error for ExecError {}

/// A word as its limbs, most significant first.
fn word(w: F128) -> String {
    format!("{:x}:{:x}", w.c1, w.c0)
}

impl std::fmt::Display for Fault {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Conflict { cell, had, new, hint } => {
                write!(
                    f,
                    "write-once conflict at cell {cell}: had {}, new {}",
                    word(*had),
                    word(*new)
                )?;
                match hint {
                    Some(hint) => write!(f, " (hint {hint})"),
                    None => Ok(()),
                }
            }
            Self::WildPointer { value } => write!(
                f,
                "DEREF address is not a g-power below 2^{}: a wild pointer, a failed range check, or past any memory a stack can hold (pointer {})",
                MAX_CELLS.ilog2(),
                word(*value)
            ),
            Self::NotInK { what, value } => write!(f, "{what} is not a K-valued word ({})", word(*value)),
            Self::NotAGPower { what, value } => write!(f, "{what} is not a g-power in range (0x{:016x})", value.0),
            Self::BackSolveThroughZero => write!(f, "cannot back-solve MUL through a zero operand"),
            Self::Witness(problem) => write!(f, "{problem}"),
            Self::OutOfMemory => write!(
                f,
                "the program reaches past 2^{} cells, more memory than a stack can hold",
                MAX_CELLS.ilog2()
            ),
            Self::HaltOutsideMain { fp } => write!(f, "the halt pc reached in frame {fp}, not main's"),
            Self::StepLimit => write!(f, "step limit of {MAX_STEPS} exceeded (runaway recursion?)"),
        }
    }
}

/// A memory word that has to lie in K, or why it does not.
fn in_k(what: &'static str, v: F128) -> Result<F64, Fault> {
    v.as_base().ok_or(Fault::NotInK { what, value: v })
}

/// A named witness stream and the next entry `hint_witness` pops from it.
struct Stream<'a> {
    name: &'a str,
    entries: Option<&'a [Vec<F128>]>,
    next: usize,
}

impl<'a> Stream<'a> {
    /// Stream `name` of `witness`, at its first entry.
    fn new(witness: &'a [(String, Vec<Vec<F128>>)], name: &'a str) -> Self {
        Self {
            name,
            entries: witness
                .iter()
                .find(|(n, _)| n == name)
                .map(|(_, entries)| entries.as_slice()),
            next: 0,
        }
    }

    /// The next entry, of `len` values.
    fn pop(&mut self, len: u32) -> Result<&'a [F128], Fault> {
        let name = self.name;
        let entries = self
            .entries
            .ok_or_else(|| Fault::Witness(format!("no witness stream `{name}`")))?;
        let entry = entries.get(self.next).ok_or_else(|| {
            Fault::Witness(format!(
                "witness stream `{name}` exhausted (needs entry {}, has {})",
                self.next + 1,
                entries.len()
            ))
        })?;
        if entry.len() != len as usize {
            return Err(Fault::Witness(format!(
                "witness `{name}` entry {} holds {} values, the destination {len}",
                self.next,
                entry.len()
            )));
        }
        self.next += 1;
        Ok(entry)
    }
}

/// The cell `base + offset`, if it lies in the address space.
fn cell_at(base: u32, offset: u32) -> Result<u32, Fault> {
    run_at(base, offset, 1)
}

/// The first of the `len` cells from `base + offset`, if they lie in the address space.
fn run_at(base: u32, offset: u32, len: u32) -> Result<u32, Fault> {
    let start = u64::from(base) + u64::from(offset);
    if start + u64::from(len) <= u64::from(MAX_CELLS) {
        Ok(start as u32)
    } else {
        Err(Fault::OutOfMemory)
    }
}

/// The memory while the program runs: whole pages up to the highest cell reached.
#[derive(Default)]
struct Mem {
    pages: Vec<Vec<Cell>>,
    /// One past the highest cell accessed or reserved.
    used: usize,
    /// The highest access count any cell reached.
    counts: u32,
    /// The cells a `DEREF` linked each cell to.
    links: QuickMap<u32, Vec<u32>>,
    /// Cells an instruction read before anything wrote them.
    unwritten_reads: Vec<u32>,
}

impl Mem {
    /// Cover cell `idx`.
    fn ensure(&mut self, idx: usize) {
        if idx >= self.used {
            self.used = idx + 1;
            while self.pages.len() <= idx >> PAGE_LOG {
                self.pages.push(vec![Cell::UNWRITTEN; 1 << PAGE_LOG]);
            }
        }
    }

    /// Cell `c`, covered.
    fn at(&mut self, c: u32) -> &mut Cell {
        self.ensure(c as usize);
        let c = c as usize;
        &mut self.pages[c >> PAGE_LOG][c & ((1 << PAGE_LOG) - 1)]
    }

    /// Cell `c`, if its page exists.
    fn cell(&self, c: u32) -> Option<&Cell> {
        let c = c as usize;
        (self.pages.get(c >> PAGE_LOG)).map(|page| &page[c & ((1 << PAGE_LOG) - 1)])
    }

    fn written(&self, cell: u32) -> bool {
        self.cell(cell).is_some_and(|c| c.state == State::Written)
    }

    /// A hint's read, which writes nothing: what a hint computes is advice the instructions go on to check.
    fn get(&self, cell: u32) -> F128 {
        self.cell(cell).map_or(F128::ZERO, |c| c.word)
    }

    /// An instruction's read. An unwritten cell reads as zero, which is then written there: the row is filled from
    /// the final image, which has to agree.
    fn read(&mut self, cell: u32) -> F128 {
        let c = self.at(cell);
        let word = c.word;
        if c.state != State::Written {
            c.state = State::Written;
            self.unwritten_reads.push(cell);
        }
        word
    }

    /// Write-once store, carried to every cell linked to this one.
    fn put(&mut self, cell: u32, v: F128) -> Result<(), Fault> {
        if self.store(cell, v)? {
            let mut todo = vec![cell];
            while let Some(c) = todo.pop() {
                for p in self.links.remove(&c).unwrap_or_default() {
                    if self.store(p, v)? {
                        todo.push(p);
                    }
                }
            }
        }
        Ok(())
    }

    /// `put` on one cell; whether it was linked.
    fn store(&mut self, cell: u32, v: F128) -> Result<bool, Fault> {
        let c = self.at(cell);
        let state = c.state;
        if state == State::Written && c.word != v {
            let had = c.word;
            return Err(Fault::Conflict {
                cell,
                had,
                new: v,
                hint: None,
            });
        }
        (c.word, c.state) = (v, State::Written);
        Ok(state == State::Linked)
    }

    fn link(&mut self, a: u32, b: u32) {
        for (x, y) in [(a, b), (b, a)] {
            let c = self.at(x);
            if c.state == State::Unwritten {
                c.state = State::Linked;
            }
            self.links.entry(x).or_default().push(y);
        }
    }

    /// Read the running access count and advance it: the column's `×g`, on the exponent.
    fn bump_access_count(&mut self, cell: u32) -> u32 {
        let c = self.at(cell);
        let count = c.count;
        c.count = count + 1;
        self.counts = self.counts.max(count + 1);
        count
    }
}

/// What the hints keep across the run: the next free cell and each witness stream's next entry.
struct Advice<'a> {
    next_free: u32,
    witness: &'a [(String, Vec<Vec<F128>>)],
    streams: QuickMap<&'a str, Stream<'a>>,
}

impl<'a> Advice<'a> {
    /// Stream `name`, at its next entry.
    fn stream(&mut self, name: &'a str) -> &mut Stream<'a> {
        let witness = self.witness;
        (self.streams.entry(name)).or_insert_with(|| Stream::new(witness, name))
    }
}

/// Reserve `size` fresh cells, the last below `MAX_CELLS`, for the region whose pointer is `cell`: write the region's
/// base `g^{next_free}` there, once, a second value being a conflict.
fn alloc(m: &mut Mem, g: &mut GPow, next_free: &mut u32, cell: u32, size: u32) -> Result<(), Fault> {
    let base = *next_free;
    *next_free = run_at(base, size, 0)?;
    g.grow_to(*next_free as usize);
    // The base is about to become a pointer in memory.
    g.note(base as usize);
    if *next_free > base {
        m.ensure(*next_free as usize - 1);
    }
    m.put(cell, F128::from(g.pow(base as usize)))
}

/// The cell a heap run starts at: the pointer in `cell`, inverted.
fn heap_base(m: &Mem, g: &mut GPow, cell: u32, what: &'static str) -> Result<u32, Fault> {
    let p = in_k(what, m.get(cell))?;
    g.log(p).ok_or(Fault::NotAGPower { what, value: p })
}

/// Where a computed-advice bit buffer of `len` cells starts: a frame run needs no lookup at all, which is the point of
/// having one.
fn bits_base(m: &Mem, g: &mut GPow, fp: u32, dest: BitsDest, len: u32, what: &'static str) -> Result<u32, Fault> {
    match dest {
        BitsDest::Stack(base) => run_at(fp, base, len),
        BitsDest::Heap(ptr) => run_at(heap_base(m, g, cell_at(fp, ptr)?, what)?, 0, len),
    }
}

/// `print`'s line for a cell: small integers and small g-powers overlap (`8 = x^3 = g^3`), so every reading that
/// applies. Only a `K`-valued word can be a g-power.
fn print(label: &str, m: &Mem, cell: u32) {
    if !m.written(cell) {
        return eprintln!("[print] {label} = <unwritten>");
    }
    let v = m.get(cell);
    let k = v.as_base().and_then(|lo| bounded_dlog(lo, MAX_INDEX.ilog2()));
    match (k, v.as_base().is_some_and(|lo| lo.0 < 1 << 32)) {
        (Some(k), true) => eprintln!("[print] {label} = {} (g^{})", pretty_integer(v.c0), pretty_integer(k)),
        (Some(k), false) => eprintln!("[print] {label} = g^{}", pretty_integer(k)),
        (None, true) => eprintln!("[print] {label} = {}", pretty_integer(v.c0)),
        (None, false) => eprintln!("[print] {label} = {:#x}:{:#x}", v.c1, v.c0),
    }
}

/// A hint's name, for the conflict it caused.
#[cold]
fn hint_name(h: &RHint) -> &'static str {
    match h {
        RHint::FrameAddress { .. } => "FrameAddress",
        RHint::AllocFrames { .. } => "AllocFrames",
        RHint::Alloc { .. } => "Alloc",
        RHint::AllocDyn { .. } => "AllocDyn",
        RHint::AllocArm { .. } => "AllocArm",
        RHint::CellAddress { .. } => "CellAddress",
        RHint::WitnessStack { .. } => "WitnessStack",
        RHint::WitnessHeap { .. } => "WitnessHeap",
        RHint::Log2Ceil { .. } => "Log2Ceil",
        RHint::BitDecompose { .. } => "BitDecompose",
        RHint::BitDecomposeExp { .. } => "BitDecomposeExp",
        RHint::DigitDecomposeExp { .. } => "DigitDecomposeExp",
        RHint::WindowsExp { .. } => "WindowsExp",
        RHint::FieldLimbs { .. } => "FieldLimbs",
        RHint::Inverse { .. } => "Inverse",
        RHint::Print { .. } => "Print",
    }
}

/// Run the program in write-once *fill* mode to produce its [`Execution`]: the final memory image and the trace, or
/// why it has none. The public input seeds the first two memory cells `m[0], m[1]` (§sec:e2e-pi), and `witness` names
/// the streams of the program's `hint_witness` calls, each with one entry per call, in the order they are popped, and
/// no two with one name.
pub fn execute(
    program: &Program,
    witness: &[(String, Vec<Vec<F128>>)],
    public_input: [F128; 2],
) -> Result<Execution, ExecError> {
    let ending_pc = (program.prog.len() - 1) as u32; // last bytecode slot, g^{B-1}
    if program.main_frame >= MAX_CELLS {
        return Err(ExecError::new(program, 0, Fault::OutOfMemory));
    }
    if let Some(i) = (1..witness.len()).find(|&i| witness[..i].iter().any(|(name, _)| *name == witness[i].0)) {
        let fault = Fault::Witness(format!("witness stream `{}` given twice", witness[i].0));
        return Err(ExecError::new(program, 0, fault));
    }
    // `g^j` for the pcs, the return targets and the main frame, grown as the run reaches further.
    let mut g = GPow::new((program.prog.len() + 2).max(program.main_frame as usize));
    let mut m = Mem::default();
    m.ensure(program.main_frame.max(2) as usize - 1);
    let fail = |pc, fault| ExecError::new(program, pc, fault);
    m.put(0, public_input[0]).map_err(|f| fail(0, f))?;
    m.put(1, public_input[1]).map_err(|f| fail(0, f))?;
    let mut advice = Advice {
        next_free: program.main_frame,
        witness,
        streams: QuickMap::default(),
    };
    // Each pc's hints, indexed by pc: a map lookup on every step costs more than most steps.
    let mut hints: Vec<&[RHint]> = vec![&[]; program.prog.len()];
    for (&hpc, hs) in &program.hints {
        hints[hpc as usize] = hs;
    }
    // `DBG_PROF=1`: per-pc step counts, for a per-function cycle profile after the run.
    let mut prof: Option<Vec<u64>> = std::env::var("DBG_PROF")
        .is_ok()
        .then(|| vec![0u64; program.prog.len()]);

    let mut bytecode_count: Vec<u32> = vec![0; program.prog.len()];
    let (mut xor, mut mul, mut set, mut deref, mut jump, mut keccak) =
        (Vec::new(), Vec::new(), Vec::new(), Vec::new(), Vec::new(), Vec::new());
    let (mut pc, mut fp) = (0u32, 0u32);
    let mut steps = 0usize;
    loop {
        // The machine halts in the final STATE `(g^{B-1}, g^0)`, the one the state bus pulls (§sec:state).
        if pc == ending_pc && fp == 0 {
            break;
        }
        if pc > ending_pc {
            // The last slot ran in another frame and fell through to `g^B`, no address.
            return Err(fail(ending_pc, Fault::HaltOutsideMain { fp }));
        }
        if steps >= MAX_STEPS {
            return Err(fail(pc, Fault::StepLimit));
        }
        let fail = move |fault| fail(pc, fault);
        let at = move |base, offset| cell_at(base, offset).map_err(fail);
        if let Some(p) = prof.as_mut() {
            p[pc as usize] += 1;
        }
        for h in hints[pc as usize] {
            apply_hint(h, fp, &mut m, &mut g, &mut advice).map_err(|fault| match fault {
                Fault::Conflict { cell, had, new, .. } => fail(Fault::Conflict {
                    cell,
                    had,
                    new,
                    hint: Some(hint_name(h)),
                }),
                fault => fail(fault),
            })?;
        }
        // Cover the g-powers this step may index (g²·pc return target, g^fp).
        g.grow_to((pc as usize + 2).max(fp as usize));
        let bytecode_read = bytecode_count[pc as usize];
        bytecode_count[pc as usize] += 1;

        // Loaded once: the shared Xor/Mul arm needs the discriminant again, and `Op` is wide enough that
        // re-reading it costs a second load.
        let op = program.prog[pc as usize];
        match op {
            Op::Xor { a, b, c } | Op::Mul { a, b, c } => {
                let is_xor = matches!(op, Op::Xor { .. });
                let (aa, ab, ac) = (at(fp, a)?, at(fp, b)?, at(fp, c)?);
                // The row is `m[c] = m[a] op m[b]` over write-once memory. A `MUL` whose result is written and
                // exactly one of whose operands is not back-solves that operand: the range check's complement
                // `y = g^{k-1}·x^{-1}` and the quotient `a / b`, with no hint. An `XOR` does not, as one into a
                // written cell is how `assert a == b` is spelled.
                if !is_xor && m.written(ac) {
                    let (ha, hb) = (m.written(aa), m.written(ab));
                    if ha ^ hb {
                        let known = m.get(if ha { aa } else { ab });
                        if known.is_zero() {
                            return Err(fail(Fault::BackSolveThroughZero));
                        }
                        m.put(if ha { ab } else { aa }, m.get(ac) * known.inv()).map_err(fail)?;
                    }
                }
                let (va, vb) = (m.read(aa), m.read(ab));
                m.put(ac, if is_xor { va + vb } else { va * vb }).map_err(fail)?;
                let row = Xrow {
                    pc,
                    fp,
                    ra: m.bump_access_count(aa),
                    rb: m.bump_access_count(ab),
                    rc: m.bump_access_count(ac),
                    bytecode_read,
                };
                if is_xor {
                    xor.push(row)
                } else {
                    mul.push(row)
                }
                pc += 1;
            }
            Op::Set { o, k } => {
                let a = at(fp, o)?;
                m.put(a, super::from_scalar(k)).map_err(fail)?;
                let r = m.bump_access_count(a);
                set.push(Srow {
                    pc,
                    fp,
                    r,
                    bytecode_read,
                });
                pc += 1;
            }
            Op::Deref { o1, o2, o3, mode } => {
                let a1 = at(fp, o1)?;
                let p = m.read(a1);
                let p_addr = p.as_base().ok_or_else(|| fail(Fault::WildPointer { value: p }))?;
                // The AIR reads the cell at the product `p·g^o2`, so `p` need be no address: the pointer's log when it
                // has one in range (an allocation notes it), else the product's.
                let a2 = match g.log(p_addr).map(|b| u64::from(b) + u64::from(o2)) {
                    Some(c) if c < u64::from(MAX_CELLS) => c as u32,
                    _ => (g.log(p_addr * F64::G.pow(u128::from(o2))))
                        .ok_or_else(|| fail(Fault::WildPointer { value: p }))?,
                };
                let a3 = at(fp, o3)?;
                match mode {
                    // `m[a2] = m[a3]`: carry a written side to the other (`put` checks it when both are), or
                    // link two unwritten sides until either is written. A range-check touch may leave both
                    // unwritten for good: only the validity of `a2` matters there.
                    DerefMode::Cell => {
                        if m.written(a2) {
                            m.put(a3, m.get(a2)).map_err(fail)?;
                        } else if m.written(a3) {
                            m.put(a2, m.get(a3)).map_err(fail)?;
                        } else {
                            m.link(a2, a3);
                        }
                    }
                    // The return target and the frame base are stored as addresses, which JUMP reads back.
                    DerefMode::Pc => {
                        g.note(pc as usize + 2);
                        m.put(a2, F128::from(g.pow(pc as usize + 2))).map_err(fail)?;
                    }
                    DerefMode::Fp => {
                        g.note(fp as usize);
                        m.put(a2, F128::from(g.pow(fp as usize))).map_err(fail)?;
                    }
                }
                deref.push(Drow {
                    pc,
                    fp,
                    r1: m.bump_access_count(a1),
                    r2: m.bump_access_count(a2),
                    r3: m.bump_access_count(a3),
                    bytecode_read,
                });
                pc += 1;
            }
            Op::Jump { oc, od, of } => {
                let (ac, ad, af) = (at(fp, oc)?, at(fp, od)?, at(fp, of)?);
                // The three cells are `K`-valued on every row, taken or not: the table commits one lane each
                // and their memory flushes carry zeros above it (§sec:tab-jump). A guest branches on g-powers,
                // and `assert a != b` takes an inverse hint instead (§sec:prog-div-ne).
                let c = in_k("JUMP condition", m.read(ac)).map_err(fail)?;
                let d = in_k("JUMP target", m.read(ad)).map_err(fail)?;
                let f = in_k("JUMP fp", m.read(af)).map_err(fail)?;
                jump.push(Jrow {
                    pc,
                    fp,
                    rc: m.bump_access_count(ac),
                    rd: m.bump_access_count(ad),
                    rf: m.bump_access_count(af),
                    bytecode_read,
                });
                if c.is_zero() {
                    pc += 1;
                } else {
                    let not_a_g_power = |what, value| fail(Fault::NotAGPower { what, value });
                    pc = (g.log_below(d, program.prog.len())).ok_or_else(|| not_a_g_power("JUMP target", d))?;
                    fp = g.log(f).ok_or_else(|| not_a_g_power("JUMP fp", f))?;
                }
            }
            Op::Keccak { .. } => {
                use crate::keccak::{ROW_CELLS, STATE_CELLS};
                let k = crate::tables::KeccakOp::of(&op);
                // Only the cells accessed need an address: the input and those `out` holds.
                let written = STATE_CELLS + k.out_cells.cells();
                let mut cells = [0; ROW_CELLS];
                for (c, cell) in cells[..written].iter_mut().enumerate() {
                    let (offset, step) = k.cell_parts(c);
                    *cell = at(at(fp, offset)?, step)?;
                }
                // The Keccak reduction proves the output; the run computes it for the later reads.
                let input: [F128; STATE_CELLS] = std::array::from_fn(|c| m.read(cells[c]));
                let mut lanes = crate::keccak::state_of_cells(k.in_odd, |c| input[c]);
                primitives::hash::keccak_f(&mut lanes);
                let output = crate::keccak::cells_of_state(&lanes, k.out_odd);
                for (&cell, &v) in cells[STATE_CELLS..written].iter().zip(&output) {
                    m.put(cell, v).map_err(fail)?;
                }
                // In flush order, so a cell two operands alias pairs each read with its own count. A cell not
                // written keeps count 0.
                let mut r = [0; ROW_CELLS];
                for (count, &cell) in r.iter_mut().zip(&cells[..written]) {
                    *count = m.bump_access_count(cell);
                }
                keccak.push(Krow {
                    pc,
                    fp,
                    r,
                    bytecode_read,
                });
                pc += 1;
            }
        }
        steps += 1;
    }

    if let Some(p) = &prof {
        report_profile(program, p, steps);
    }
    let counts = bytecode_count.iter().copied().max().unwrap_or(0).max(m.counts) as usize + 1;
    let trace = Trace {
        xor,
        mul,
        set,
        deref,
        jump,
        keccak,
        bytecode_count,
        counts,
    };
    // The memory announced: the least power of two covering every cell the run touched.
    Ok(Execution {
        mem: Memory {
            pages: m.pages,
            len: m.used.next_power_of_two(),
        },
        cycles: steps,
        mem_used: m.used,
        unconstrained_reads: m.unwritten_reads,
        trace,
    })
}

/// Apply a hint scheduled before an instruction at frame `fp`.
fn apply_hint<'a>(h: &'a RHint, fp: u32, m: &mut Mem, g: &mut GPow, advice: &mut Advice<'a>) -> Result<(), Fault> {
    let not_a_g_power = |what, value| Fault::NotAGPower { what, value };
    // A runtime size is carried in the exponent: the cell holds `g^k`, allocate `k` cells.
    let dyn_size = |m: &Mem, g: &mut GPow, size: u32| {
        let size = in_k("HeapBuf size", m.get(cell_at(fp, size)?))?;
        g.log(size).ok_or(not_a_g_power("HeapBuf size", size))
    };
    match *h {
        RHint::FrameAddress { offset } => g.note(cell_at(fp, offset)? as usize),
        RHint::CellAddress { ptr, cell } => {
            let cell = cell_at(fp, cell)? as usize;
            g.grow_to(cell);
            let address = g.pow(cell);
            m.put(cell_at(fp, ptr)?, F128::from(address))?;
        }
        // A fresh region: write its base `g^{next_free}` into the pointer cell (once) and reserve `size` cells.
        RHint::Alloc { ptr, size } => alloc(m, g, &mut advice.next_free, cell_at(fp, ptr)?, size)?,
        RHint::AllocDyn { ptr, size } => {
            let cells = dyn_size(m, g, size)?;
            alloc(m, g, &mut advice.next_free, cell_at(fp, ptr)?, cells)?;
        }
        // A dispatched call's frame, sized by the arm `m[fp+sel] = g^k` selects.
        RHint::AllocArm { ptr, sel, ref sizes } => {
            const WHAT: &str = "dispatch selector";
            let x = in_k(WHAT, m.get(cell_at(fp, sel)?))?;
            let k = g.log(x).ok_or(not_a_g_power(WHAT, x))?;
            let cells = *sizes.get(k as usize).ok_or(not_a_g_power(WHAT, x))?;
            alloc(m, g, &mut advice.next_free, cell_at(fp, ptr)?, cells)?;
        }
        RHint::AllocFrames {
            ptr,
            size,
            end,
            start_inverse,
        } => {
            let span = in_k("loop bound", m.get(cell_at(fp, end)?))? * F64(start_inverse.0);
            let n = (!span.is_zero())
                .then(|| g.log(span))
                .flatten()
                .ok_or(not_a_g_power("loop bound", span))?;
            let cells = n.checked_add(1).and_then(|frames| size.checked_mul(frames));
            let cells = cells.ok_or(Fault::OutOfMemory)?;
            alloc(m, g, &mut advice.next_free, cell_at(fp, ptr)?, cells)?;
        }
        RHint::Print { ref label, cell } => print(label, m, cell_at(fp, cell)?),
        RHint::WitnessStack { ref name, base, len } => {
            let base = run_at(fp, base, len)?;
            for (k, &value) in advice.stream(name).pop(len)?.iter().enumerate() {
                m.put(base + k as u32, value)?;
            }
        }
        RHint::WitnessHeap { ref name, ptr, lo, len } => {
            let heap = heap_base(m, g, cell_at(fp, ptr)?, "hint_witness heap pointer")?;
            let base = run_at(heap, lo, len)?;
            for (k, &value) in advice.stream(name).pop(len)?.iter().enumerate() {
                m.put(base + k as u32, value)?;
            }
        }
        RHint::Log2Ceil {
            bits,
            dst,
            nbits,
            floor,
        } => {
            let base = bits_base(m, g, fp, bits, nbits, "log2_ceil pointer")?;
            let word = (0..nbits).fold(0u128, |word, j| word | (u128::from(!m.get(base + j).is_zero()) << j));
            let log = if word <= 1 {
                0
            } else {
                u128::BITS - (word - 1).leading_zeros()
            };
            let dst = cell_at(fp, dst)?;
            m.put(dst, F128::from(primitives::field::g_pow(log.max(floor) as usize)))?;
        }
        RHint::BitDecompose { value, bits, nbits } => {
            assert!(nbits <= 128, "a machine word has 128 bits");
            let v = u128::from(m.get(cell_at(fp, value)?));
            let base = bits_base(m, g, fp, bits, nbits, "decompose pointer")?;
            for j in 0..nbits {
                m.put(base + j, F128::from((v >> j) & 1))?;
            }
        }
        RHint::BitDecomposeExp { value, bits, nbits } => {
            const WHAT: &str = "hint_decompose_bits_exponent value";
            let x = in_k(WHAT, m.get(cell_at(fp, value)?))?;
            let n = bounded_dlog(x, nbits).ok_or(not_a_g_power(WHAT, x))?;
            let base = bits_base(m, g, fp, bits, nbits, "hint_decompose_bits_exponent pointer")?;
            for j in 0..nbits {
                m.put(base + j, F128::new(((n >> j) & 1) as u64, 0))?;
            }
        }
        RHint::WindowsExp {
            value,
            dest,
            at,
            start,
            width,
            count,
        } => {
            assert!(start + width * count <= 128, "a machine word has 128 bits");
            let v = u128::from(m.get(cell_at(fp, value)?));
            let base = bits_base(m, g, fp, dest, at.saturating_add(count), "windows pointer")?;
            for i in 0..count {
                let bit = |j| (((v >> (start + i * width + j)) & 1) as usize) << j;
                let window = (0..width).fold(0, |n, j| n | bit(j));
                m.put(base + at + i, F128::from(primitives::field::g_pow(window)))?;
            }
        }
        RHint::DigitDecomposeExp {
            value,
            dst,
            nbits,
            ndigits,
            digit_bits,
            start,
            start_cell,
        } => {
            const WHAT: &str = "hint_decompose_digits_exponent value";
            let x = in_k(WHAT, m.get(cell_at(fp, value)?))?;
            let n = bounded_dlog(x, nbits).ok_or(not_a_g_power(WHAT, x))?;
            let start = match start_cell {
                None => start,
                Some(c) => {
                    const WHAT: &str = "hint_decompose_digits_exponent start";
                    let y = in_k(WHAT, m.get(cell_at(fp, c)?))?;
                    bounded_dlog(y, 7).ok_or(not_a_g_power(WHAT, y))? as u32
                }
            };
            let base = bits_base(m, g, fp, dst, ndigits, "hint_decompose_digits_exponent pointer")?;
            let mask = (1u128 << digit_bits) - 1;
            for j in 0..ndigits {
                let at = start + digit_bits * j;
                let digit = if at >= 128 { 0 } else { (n >> at) & mask };
                m.put(base + j, F128::from(primitives::field::g_pow(digit as usize)))?;
            }
        }
        RHint::FieldLimbs { value, base, len } => {
            assert!((1..=2).contains(&len), "an F128 value has two K limbs");
            let limbs = m.get(cell_at(fp, value)?).to_limbs();
            let base = run_at(fp, base, len)?;
            for j in 0..len {
                m.put(base + j, F128::new(limbs[j as usize], 0))?;
            }
        }
        RHint::Inverse { value, dst } => {
            let v = m.get(cell_at(fp, value)?);
            m.put(cell_at(fp, dst)?, if v.is_zero() { F128::ZERO } else { v.inv() })?;
        }
    }
    Ok(())
}
/// The `DBG_PROF=1` report: the cycles of each compiled function, from the per-pc counts `p`, and with
/// `DBG_PROF_DUMP=path` the raw per-pc counts plus the function table, so an offline pass can attribute the
/// straight-line cycles of one big function to its source regions (the call sites of the lowered `for`
/// helpers are the landmarks).
fn report_profile(program: &Program, p: &[u64], steps: usize) {
    let mut rows: Vec<(String, u64)> = program
        .fn_ranges
        .iter()
        .map(|(name, entry, len)| {
            let total: u64 = p[*entry as usize..(*entry + *len) as usize].iter().sum();
            (name.clone(), total)
        })
        .collect();
    rows.sort_by_key(|(_, c)| std::cmp::Reverse(*c));
    if let Ok(path) = std::env::var("DBG_PROF_DUMP") {
        let mut out = format!("# steps {steps}\n");
        for (name, entry, len) in &program.fn_ranges {
            out += &format!("F {name} {entry} {len}\n");
        }
        for (pc, c) in p.iter().enumerate() {
            if *c > 0 {
                out += &format!("{pc} {c}\n");
            }
        }
        let path = if std::path::Path::new(&path).exists() {
            format!("{path}.{}", std::process::id())
        } else {
            path
        };
        std::fs::write(&path, out).expect("write DBG_PROF_DUMP");
        eprintln!("== DBG_PROF: per-pc counts written to {path}");
    }
    eprintln!("== DBG_PROF: cycles by function ({} total) ==", pretty_integer(steps));
    for (name, c) in rows.iter().filter(|(_, c)| *c > 0) {
        eprintln!(
            "  {:>13}  {:>7}%  {name}",
            pretty_integer(c),
            pretty_f64(100.0 * *c as f64 / steps as f64)
        );
    }
}
