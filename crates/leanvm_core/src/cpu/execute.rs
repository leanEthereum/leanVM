//! The write-once execution interpreter: run the compiled program to produce
//! the final memory image and the per-opcode [`Trace`].

use std::collections::HashMap;

use super::hints::MAX_CELLS;
use super::*;
use primitives::{
    field::{F64, F192, mul_by_g},
    pretty_f64, pretty_integer,
};

pub struct Execution {
    pub mem: Memory,     // data memory after the run, write-once (size cells, power of two)
    pub cycles: usize,   // number of instructions the run executed (trace length)
    pub mem_used: usize, // cells actually touched, before the power-of-two pad of `mem`
    /// Cells an instruction read before anything wrote them, so the value it read was
    /// ZERO here and prover-chosen in a proof: memory is a committed array and the bus
    /// only forces accesses to one address to *agree*, never that the address was
    /// written. `zkDSL.md` says don't; this is what says whether the
    /// emitted code did. A non-empty list means a live value came from outside the
    /// constraint system, so an `assert` on it is vacuous and a published value is
    /// free: the source read a cell nothing stores, or the lowering dropped or
    /// misplaced a store the source asked for.
    ///
    /// Legitimate unconstrained cells are absent by construction, not by
    /// exemption: a range-check touch only links its two cells, reading neither,
    /// and an arithmetic back-solve writes its operand before reading it.
    pub unconstrained_reads: Vec<u32>,
    pub(crate) trace: Trace, // rows + final access-count columns, emitted in the same walk
    /// `g^0, g^1, ..` as far as the run indexed them: every pc, frame base and cell it reached.
    pub(crate) gpow: Vec<F64>,
}

impl Execution {
    /// Rows per table: the instructions of each opcode the run executed.
    pub fn rows(&self) -> [usize; crate::tables::N_TABLES] {
        self.trace.row_counts()
    }
}

/// `log2` of the cells a [`Memory`] page holds.
const PAGE_LOG: usize = 16;
const PAGE: usize = 1 << PAGE_LOG;
// The padded image is a whole number of pages.
const _: () = assert!(PAGE_LOG <= MIN_LOG_MEM);

/// A cell's write state. A cell not `Written` holds ZERO; a `DEREF` between two
/// unwritten cells links them, and a write to either reaches the other at once.
#[derive(Clone, Copy, PartialEq, Eq)]
#[repr(u8)]
enum State {
    Unwritten = 0,
    Linked,
    Written,
}

/// One cell: its word, its access count as an exponent (the column holds `g^count`),
/// and its write state, side by side so one access touches one line. All zero is an
/// unwritten cell holding ZERO, never accessed.
#[derive(Clone, Copy)]
#[repr(C)]
pub(crate) struct Cell {
    pub(crate) word: F192,
    pub(crate) count: u32,
    state: State,
}

impl Cell {
    pub(crate) const UNWRITTEN: Self = Self {
        word: F192::ZERO,
        count: 0,
        state: State::Unwritten,
    };
}

/// The write-once data memory: `len` cells, a power of two, in pages, so that the
/// image grows without moving what it holds. Cells past the last page are unwritten
/// and never accessed.
pub struct Memory {
    pages: Vec<Box<[Cell]>>,
    len: usize,
}

impl Memory {
    /// Cells in the image, its power-of-two pad included.
    pub fn len(&self) -> usize {
        self.len
    }

    pub fn is_empty(&self) -> bool {
        self.len == 0
    }

    /// The word in cell `i`.
    pub fn word(&self, i: usize) -> F192 {
        self.page(i >> PAGE_LOG).map_or(F192::ZERO, |p| p[i & (PAGE - 1)].word)
    }

    /// Page `p`'s cells, `None` past the last one.
    pub(crate) fn page(&self, p: usize) -> Option<&[Cell]> {
        self.pages.get(p).map(|p| &p[..])
    }

    pub(crate) fn page_log() -> usize {
        PAGE_LOG
    }
}

/// Why a run has no execution the interpreter can find: the program, on this public
/// input and advice, asks for something the machine cannot do.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ExecError {
    /// The instruction the run failed at, or whose hints it failed in.
    pub pc: u32,
    /// Its function and source line ([`Program::site_at`]).
    pub site: String,
    pub fault: Fault,
}

/// What the run asked for that the machine cannot do.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Fault {
    /// A second value for a written cell: a failed `assert`, two writes that disagree,
    /// or a write to a cell an instruction already read, unwritten, as ZERO. `hint`
    /// names the hint that wrote it, if one did.
    Conflict {
        cell: u32,
        had: F192,
        new: F192,
        hint: Option<&'static str>,
    },
    /// A `DEREF` through a word that is no small g-power: a wild pointer, or a failed
    /// range check.
    WildPointer { value: F192 },
    /// A word that has to be in `K` is not: a `JUMP` operand, or one a hint reads.
    NotInK { what: &'static str, value: F192 },
    /// A word that has to be an address or a count is not a g-power in its range.
    NotAGPower { what: &'static str, value: F64 },
    /// A `KECCAK` input cell outside the 128-bit embedding.
    NotCanonical { cell: usize, value: F192 },
    /// A `MUL` asked to solve `a·x = c` for `x` with `a = 0`.
    BackSolveThroughZero,
    /// The advice does not fit the program: a witness stream is missing or
    /// exhausted, or an entry has the wrong length.
    Witness(String),
    /// The program allocates past the address space.
    OutOfMemory,
    /// The halt `pc` reached in a frame other than `main`'s.
    HaltOutsideMain { fp: u32 },
    /// Too many instructions: runaway recursion, or a loop that never ends.
    StepLimit,
}

/// The longest run the interpreter executes.
const MAX_STEPS: usize = 100_000_000;

impl ExecError {
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
fn word(w: F192) -> String {
    format!("{:x}:{:x}:{:x}", w.c2, w.c1, w.c0)
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
                "DEREF pointer is not a small g-power: a wild pointer, or a failed range check (value {})",
                word(*value)
            ),
            Self::NotInK { what, value } => write!(f, "{what} is not a K-valued word ({})", word(*value)),
            Self::NotAGPower { what, value } => write!(f, "{what} is not a g-power in range (0x{:016x})", value.0),
            Self::NotCanonical { cell, value } => write!(
                f,
                "KECCAK input cell {cell} is not a canonical 128-bit embedding ({})",
                word(*value)
            ),
            Self::BackSolveThroughZero => write!(f, "cannot back-solve MUL through a zero operand"),
            Self::Witness(problem) => write!(f, "{problem}"),
            Self::OutOfMemory => write!(f, "the program allocates past 2^{} cells", MAX_CELLS.ilog2()),
            Self::HaltOutsideMain { fp } => write!(f, "the halt pc reached in frame {fp}, not main's"),
            Self::StepLimit => write!(f, "step limit of {MAX_STEPS} exceeded (runaway recursion?)"),
        }
    }
}

/// A memory word interpreted as a K-valued address: valid only when both
/// extension limbs are zero (every g-power is a K-element).
fn as_addr(v: F192) -> Option<F64> {
    (v.c1 == 0 && v.c2 == 0).then_some(F64(v.c0))
}

/// [`as_addr`], or why the word is none.
fn in_k(what: &'static str, v: F192) -> Result<F64, Fault> {
    as_addr(v).ok_or(Fault::NotInK { what, value: v })
}

/// A named witness stream and the next entry `hint_witness` pops from it. Resolved
/// once per run, so a pop indexes it rather than hashing its name.
struct Stream<'a> {
    name: &'a str,
    entries: Option<&'a [Vec<F192>]>,
    next: usize,
}

impl<'a> Stream<'a> {
    fn pop(&mut self, len: u32) -> Result<&'a [F192], Fault> {
        let name = self.name;
        let entries = self
            .entries
            .ok_or_else(|| Fault::Witness(format!("no witness stream `{name}` (Program::set_witness)")))?;
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

impl Program {
    /// Run the program in write-once *fill* mode to produce its [`Execution`]:
    /// the final memory image and the step count, or why it has none. The public
    /// input seeds the first two memory cells `m[0], m[1]` (§sec:e2e-pi).
    /// Compilation yields the `Program`; executing it (here) and proving it are
    /// separate later phases.
    pub fn execute(&self, public_input: [F192; 2]) -> Result<Execution, ExecError> {
        self.execute_with(public_input, &mut |_| {})
    }

    /// [`Self::execute`], handing `keccak_step` the lanes each `KECCAK` row reads, in row order
    /// and as the row runs.
    pub(crate) fn execute_with(
        &self,
        public_input: [F192; 2],
        keccak_step: &mut dyn FnMut(&[u64; primitives::hash::STATE_LANES]),
    ) -> Result<Execution, ExecError> {
        use super::hints::{BitsDest, GPow, RHint};

        let ending_pc = (self.prog.len() - 1) as u32; // last bytecode slot, g^{B-1}

        // g^j and its reverse index g^j ↦ j, seeded for the pcs and return targets,
        // the main frame and the range-check floor, then grown by each reservation.
        let seed = (self.prog.len() + 2)
            .max(self.main_frame as usize)
            .max(1 << MIN_LOG_MEM);
        let mut g = GPow::new(seed);

        // The write-once data memory, each cell's access count and write state with its word.
        let n0 = self.main_frame.max(2) as usize;
        let mut m = Mem {
            pages: Vec::new(),
            used: 0,
            counts: 0,
            links: HashMap::new(),
            unwritten_reads: Vec::new(),
            program: self,
            dbg_pc: 0,
            dbg_hint: None,
        };
        m.ensure(n0 - 1);
        // Seed the public input into m[0], m[1] (addresses g^0, g^1, §sec:e2e-pi).
        m.put(0, public_input[0])?;
        m.put(1, public_input[1])?;

        // Per-pc bytecode execution count, as an exponent of `g`.
        let mut bytecode_count: Vec<u32> = vec![0; self.prog.len()];

        let mut next_free = self.main_frame;
        let (mut pc, mut fp) = (0u32, 0u32);
        let mut steps = 0usize;
        // Witness streams, resolved by name once so a pop indexes one.
        let mut streams: Vec<Stream> = Vec::new();
        let mut stream_of: HashMap<&str, u32> = HashMap::new();
        // Per-pc hint index. `self.hints` is keyed by pc, so probing it each step
        // costs a hash of the counter for what is almost always a miss; the
        // program has one bytecode slot per pc, so flatten the map into a dense
        // table: 0 = no hints, otherwise the 1-based index into `hint_lists`, whose
        // entries pair a pc's hints with where their streams start in `hint_streams`.
        let mut hint_at = vec![0u32; self.prog.len()];
        let mut hint_lists: Vec<(&[RHint], usize)> = Vec::with_capacity(self.hints.len());
        let mut hint_streams: Vec<u32> = Vec::new();
        for (&hpc, hs) in &self.hints {
            hint_lists.push((hs.as_slice(), hint_streams.len()));
            hint_at[hpc as usize] = hint_lists.len() as u32;
            for h in hs {
                let (RHint::WitnessStack { name, .. } | RHint::WitnessHeap { name, .. }) = h else {
                    hint_streams.push(u32::MAX);
                    continue;
                };
                let s = *stream_of.entry(name).or_insert_with(|| {
                    streams.push(Stream {
                        name,
                        entries: self.witness.get(name).map(Vec::as_slice),
                        next: 0,
                    });
                    streams.len() as u32 - 1
                });
                hint_streams.push(s);
            }
        }
        // `DBG_PROF=1`: per-pc step counts, printed as a per-function cycle
        // profile after the run (needs `fn_ranges`, i.e. a compiled program).
        let mut prof: Option<Vec<u64>> = std::env::var("DBG_PROF").is_ok().then(|| vec![0u64; self.prog.len()]);

        // Baby-step table for `hint_decompose_bits_exponent`, built on first use.
        let mut dlog_cache: Option<(GPow, F64)> = None;

        // Per-opcode trace rows, accumulated during the walk and assembled into the
        // `Trace` once the run finishes (alongside the final count columns).
        let mut xor: Rows<Xrow> = Rows::new();
        let mut mul: Rows<Xrow> = Rows::new();
        let mut set: Rows<Srow> = Rows::new();
        let mut deref: Rows<Drow> = Rows::new();
        let mut jump: Rows<Jrow> = Rows::new();
        let mut keccak: Rows<Krow> = Rows::new();

        // The memory's pages, grown as the run reaches them. Every method on the hot
        // path is `#[inline(always)]`: they sit in the interpreter's opcode loop.
        struct Mem<'a> {
            pages: Vec<Box<[Cell]>>,
            /// One past the highest cell accessed or reserved: every cell below it is
            /// in a page.
            used: usize,
            /// The highest access count any cell reached.
            counts: u32,
            /// The cells a `DEREF` linked each cell to.
            links: HashMap<u32, Vec<u32>>,
            /// Cells an instruction read before anything wrote them.
            unwritten_reads: Vec<u32>,
            /// To name where a conflict happened.
            program: &'a Program,
            /// The pc of the currently executing instruction, and the name of the
            /// computed-advice hint if the write comes from one, so a write-once
            /// conflict can report where it happened. Plain fields rather than
            /// thread-locals: this is written on every step, and a thread-local
            /// costs a lazy-init check each time.
            dbg_pc: u32,
            dbg_hint: Option<&'static str>,
        }
        impl Mem<'_> {
            // Cover cell `idx`. All accessed cells satisfy cell < next_free after
            // their frame's allocation, so this only ever extends.
            #[inline(always)]
            fn ensure(&mut self, idx: usize) {
                if idx >= self.used {
                    self.grow(idx);
                }
            }
            #[cold]
            #[inline(never)]
            fn grow(&mut self, idx: usize) {
                self.used = idx + 1;
                while self.pages.len() <= idx >> PAGE_LOG {
                    // SAFETY: all zero is a valid `Cell`, the unwritten one.
                    self.pages
                        .push(unsafe { Box::<[Cell]>::new_zeroed_slice(PAGE).assume_init() });
                }
            }
            /// Cell `c`, which `ensure` has covered.
            #[inline(always)]
            fn at(&mut self, c: u32) -> &mut Cell {
                let c = c as usize;
                &mut self.pages[c >> PAGE_LOG][c & (PAGE - 1)]
            }
            #[inline(always)]
            fn covered(&self, c: u32) -> Option<&Cell> {
                let c = c as usize;
                (c < self.used).then(|| &self.pages[c >> PAGE_LOG][c & (PAGE - 1)])
            }
            #[inline(always)]
            fn written(&self, cell: u32) -> bool {
                self.covered(cell).is_some_and(|c| c.state == State::Written)
            }
            // A hint's read, which writes nothing: what a hint computes is advice the
            // instructions go on to check.
            #[inline(always)]
            fn get(&self, cell: u32) -> F192 {
                self.covered(cell).map_or(F192::ZERO, |c| c.word)
            }
            // An instruction's read. An unwritten cell reads as ZERO, which is then written
            // there: the row is filled from the final image, which has to agree.
            #[inline(always)]
            fn read(&mut self, cell: u32) -> F192 {
                self.ensure(cell as usize);
                let c = self.at(cell);
                let word = c.word;
                if c.state != State::Written {
                    c.state = State::Written;
                    self.unwritten_reads.push(cell);
                }
                word
            }
            // Write-once store, carried to every cell linked to this one.
            #[inline(always)]
            fn put(&mut self, cell: u32, v: F192) -> Result<(), ExecError> {
                if self.store(cell, v)? {
                    self.spread(cell, v)?;
                }
                Ok(())
            }
            // `put` on one cell; whether it was linked.
            #[inline(always)]
            fn store(&mut self, cell: u32, v: F192) -> Result<bool, ExecError> {
                self.ensure(cell as usize);
                let c = self.at(cell);
                let s = c.state;
                if s == State::Written && c.word != v {
                    return Err(self.conflict(cell, v));
                }
                c.word = v;
                c.state = State::Written;
                Ok(s == State::Linked)
            }
            #[cold]
            fn spread(&mut self, cell: u32, v: F192) -> Result<(), ExecError> {
                let mut todo = vec![cell];
                while let Some(c) = todo.pop() {
                    for p in self.links.remove(&c).unwrap_or_default() {
                        if self.store(p, v)? {
                            todo.push(p);
                        }
                    }
                }
                Ok(())
            }
            fn link(&mut self, a: u32, b: u32) {
                for (x, y) in [(a, b), (b, a)] {
                    self.ensure(x as usize);
                    let c = self.at(x);
                    if c.state == State::Unwritten {
                        c.state = State::Linked;
                    }
                    self.links.entry(x).or_default().push(y);
                }
            }
            #[cold]
            fn conflict(&self, cell: u32, v: F192) -> ExecError {
                let fault = Fault::Conflict {
                    cell,
                    had: self.get(cell),
                    new: v,
                    hint: self.dbg_hint,
                };
                ExecError::new(self.program, self.dbg_pc, fault)
            }
            // Read the running access count and advance it: the column's `×g`, on the
            // exponent. A run makes fewer than `2^32` accesses in all, so it cannot wrap.
            #[inline(always)]
            fn bump_access_count(&mut self, cell: u32) -> u32 {
                self.ensure(cell as usize);
                let c = self.at(cell);
                let count = c.count;
                c.count = count + 1;
                self.counts = self.counts.max(count + 1);
                count
            }
        }
        // Bounded discrete log for `hint_decompose_bits_exponent`: find n < 2^nbits
        // with g^n = x, by baby-step giant-step (baby table g^j for j < 2^17,
        // built once per run; giant step ×g^(-2^17)). Prover-side only: the
        // guest re-verifies the hinted bits in-circuit.
        fn bounded_dlog(cache: &mut Option<(GPow, F64)>, x: F64, nbits: u32) -> Option<u128> {
            const LOG_BABY: u32 = 17;
            let (baby, giant) = cache.get_or_insert_with(|| {
                let baby = GPow::new((1usize << LOG_BABY) - 1);
                // g^(2^17), one past the table; its inverse is the giant step.
                let giant = mul_by_g(baby.pow((1usize << LOG_BABY) - 1)).inv();
                (baby, giant)
            });
            let mut y = x;
            let max_giant = if nbits > LOG_BABY {
                1u64 << (nbits - LOG_BABY)
            } else {
                1
            };
            for a in 0..max_giant {
                if let Some(j) = baby.log(y) {
                    return Some((a as u128) << LOG_BABY | j as u128);
                }
                y *= *giant;
            }
            None
        }

        // A runtime count (a loop's frame span, a `HeapBuf` size) as the exponent of
        // a g-power: the address table when it covers it, else a bounded discrete log.
        fn count(g: &mut GPow, dlog: &mut Option<(GPow, F64)>, x: F64) -> Option<u32> {
            g.log(x)
                .or_else(|| bounded_dlog(dlog, x, MAX_CELLS.ilog2()).map(|n| n as u32))
        }

        // The cell a heap run starts at: read the pointer back out of memory and
        // invert it. Shared by every hint that writes through one.
        fn heap_base(m: &Mem<'_>, g: &mut GPow, cell: u32, what: &'static str) -> Result<u32, Fault> {
            let p = in_k(what, m.get(cell))?;
            g.log(p).ok_or(Fault::NotAGPower { what, value: p })
        }

        // Where a computed-advice bit buffer starts: a frame run needs no lookup
        // at all, which is the point of having one.
        fn bits_base(m: &Mem<'_>, g: &mut GPow, fp: u32, dest: BitsDest, what: &'static str) -> Result<u32, Fault> {
            match dest {
                BitsDest::Stack(base) => Ok(fp + base),
                BitsDest::Heap(ptr) => heap_base(m, g, fp + ptr, what),
            }
        }

        loop {
            if pc == ending_pc {
                if fp != 0 {
                    return Err(ExecError::new(self, pc, Fault::HaltOutsideMain { fp }));
                }
                break;
            }
            if steps >= MAX_STEPS {
                return Err(ExecError::new(self, pc, Fault::StepLimit));
            }
            m.dbg_pc = pc;
            let fail = move |fault| ExecError::new(self, pc, fault);
            if let Some(p) = prof.as_mut() {
                p[pc as usize] += 1;
            }

            // Apply the hints scheduled before this instruction.
            if hint_at[pc as usize] != 0 {
                let (hs, first) = hint_lists[hint_at[pc as usize] as usize - 1];
                for (h, &stream) in hs.iter().zip(&hint_streams[first..]) {
                    m.dbg_hint = Some(match h {
                        RHint::FrameAddress { .. } => "FrameAddress",
                        RHint::AllocFrames { .. } => "AllocFrames",
                        RHint::Alloc { .. } => "Alloc",
                        RHint::AllocDyn { .. } => "AllocDyn",
                        RHint::WitnessStack { .. } => "WitnessStack",
                        RHint::WitnessHeap { .. } => "WitnessHeap",
                        RHint::Log2Ceil { .. } => "Log2Ceil",
                        RHint::BitDecompose { .. } => "BitDecompose",
                        RHint::BitDecomposeExp { .. } => "BitDecomposeExp",
                        RHint::FieldLimbs { .. } => "FieldLimbs",
                        RHint::Inverse { .. } => "Inverse",
                        RHint::Print { .. } => "Print",
                    });
                    match h {
                        RHint::FrameAddress { offset } => {
                            g.note((fp + offset) as usize);
                        }
                        // A fresh region: write its base `g^{next_free}` into the
                        // pointer cell (once) and reserve `size` cells. `AllocDyn`
                        // reads the size from a cell at runtime.
                        RHint::Alloc { .. } | RHint::AllocDyn { .. } | RHint::AllocFrames { .. } => {
                            let (ptr, size) = match *h {
                                RHint::Alloc { ptr, size } => (ptr, size),
                                RHint::AllocFrames {
                                    ptr,
                                    size,
                                    end,
                                    start_inverse,
                                } => {
                                    let span = in_k("loop bound", m.get(fp + end)).map_err(fail)? * start_inverse;
                                    if span.is_zero() {
                                        return Err(fail(Fault::NotAGPower {
                                            what: "loop bound",
                                            value: span,
                                        }));
                                    }
                                    let n = count(&mut g, &mut dlog_cache, span)
                                        .ok_or_else(|| fail(Fault::OutOfMemory))?
                                        + 1;
                                    (ptr, size.checked_mul(n).ok_or_else(|| fail(Fault::OutOfMemory))?)
                                }
                                // A runtime size is carried in the exponent:
                                // the cell holds g^k, allocate k cells.
                                RHint::AllocDyn { ptr, size } => {
                                    let sz = in_k("HeapBuf size", m.get(fp + size)).map_err(fail)?;
                                    let cells = count(&mut g, &mut dlog_cache, sz).ok_or_else(|| {
                                        fail(Fault::NotAGPower {
                                            what: "HeapBuf size",
                                            value: sz,
                                        })
                                    })?;
                                    (ptr, cells)
                                }
                                _ => unreachable!(),
                            };
                            let cell = fp + ptr;
                            if !m.written(cell) {
                                let base = next_free;
                                next_free = base
                                    .checked_add(size)
                                    .filter(|&end| end < MAX_CELLS)
                                    .ok_or_else(|| fail(Fault::OutOfMemory))?;
                                g.grow_to((base + size) as usize);
                                // The base is about to become a pointer in memory.
                                g.note(base as usize);
                                m.ensure(next_free as usize);
                                m.put(cell, F192::from(g.pow(base as usize)))?;
                            }
                        }
                        RHint::Print { label, cell } => {
                            let c = fp + cell;
                            if m.written(c) {
                                let v = m.get(c);
                                // Small integers and small g-powers overlap (8 = x^3
                                // = g^3): show every reading that applies. Only a
                                // K-valued word (extension limbs 0) can be a g-power.
                                let k = as_addr(v).and_then(|lo| g.log(lo));
                                let small = v.c2 == 0 && v.c1 == 0 && v.c0 < 1 << 32;
                                match (k, small) {
                                    (Some(k), true) => eprintln!(
                                        "[print] {label} = {} (g^{})",
                                        pretty_integer(v.c0),
                                        pretty_integer(k)
                                    ),
                                    (Some(k), false) => {
                                        eprintln!("[print] {label} = g^{}", pretty_integer(k))
                                    }
                                    (None, true) => {
                                        eprintln!("[print] {label} = {}", pretty_integer(v.c0))
                                    }
                                    (None, false) => {
                                        eprintln!("[print] {label} = {:#x}:{:#x}:{:#x}", v.c2, v.c1, v.c0)
                                    }
                                }
                            } else {
                                eprintln!("[print] {label} = <unwritten>");
                            }
                        }
                        RHint::WitnessStack { base, len, .. } => {
                            let values = streams[stream as usize].pop(*len).map_err(fail)?;
                            for (k, &value) in values.iter().enumerate() {
                                m.put(fp + base + k as u32, value)?;
                            }
                        }
                        RHint::WitnessHeap { ptr, lo, len, .. } => {
                            let b = heap_base(&m, &mut g, fp + ptr, "hint_witness heap pointer").map_err(fail)?;
                            let values = streams[stream as usize].pop(*len).map_err(fail)?;
                            for (k, &value) in values.iter().enumerate() {
                                m.put(b + lo + k as u32, value)?;
                            }
                        }
                        RHint::Log2Ceil {
                            bits,
                            dst,
                            nbits,
                            floor,
                        } => {
                            let b = bits_base(&m, &mut g, fp, *bits, "log2_ceil pointer").map_err(fail)?;
                            let mut word: u128 = 0;
                            for j in 0..*nbits {
                                if !m.get(b + j).is_zero() {
                                    word |= 1u128 << j;
                                }
                            }
                            let cl = if word <= 1 {
                                0
                            } else {
                                u128::BITS - (word - 1).leading_zeros()
                            };
                            let mu = cl.max(*floor);
                            m.put(fp + dst, F192::from(primitives::field::g_pow(mu as usize)))?;
                        }
                        RHint::BitDecompose {
                            value,
                            bits,
                            nbits,
                            start,
                        } => {
                            assert!(start + nbits <= 192, "a machine word has 192 bits");
                            let v = m.get(fp + value);
                            let limbs = [v.c0, v.c1, v.c2];
                            let bb = bits_base(&m, &mut g, fp, *bits, "decompose pointer").map_err(fail)?;
                            for j in 0..*nbits {
                                let at = start + j;
                                let bit = (limbs[at as usize / 64] >> (at % 64)) & 1;
                                m.put(bb + j, F192::new(bit, 0, 0))?;
                            }
                        }
                        RHint::BitDecomposeExp { value, bits, nbits } => {
                            const WHAT: &str = "hint_decompose_bits_exponent value";
                            let x = in_k(WHAT, m.get(fp + value)).map_err(fail)?;
                            let n = bounded_dlog(&mut dlog_cache, x, *nbits)
                                .ok_or_else(|| fail(Fault::NotAGPower { what: WHAT, value: x }))?;
                            let bb = bits_base(&m, &mut g, fp, *bits, "hint_decompose_bits_exponent pointer")
                                .map_err(fail)?;
                            for j in 0..*nbits {
                                let bit = ((n >> j) & 1) as u64;
                                m.put(bb + j, F192::new(bit, 0, 0))?;
                            }
                        }
                        RHint::FieldLimbs { value, base, len } => {
                            assert!((1..=3).contains(len), "an F192 value has three K limbs");
                            let v = m.get(fp + value);
                            let limbs = [v.c0, v.c1, v.c2];
                            for j in 0..*len {
                                m.put(fp + base + j, F192::new(limbs[j as usize], 0, 0))?;
                            }
                        }
                        RHint::Inverse { value, dst } => {
                            let v = m.get(fp + value);
                            m.put(fp + dst, if v.is_zero() { F192::ZERO } else { v.inv() })?;
                        }
                    }
                    m.dbg_hint = None;
                }
            }
            // Cover the g-powers this step may index (g²·pc return target, g^fp).
            // Guarded so the steady state is a length compare, not a call.
            let need = (pc as usize + 2).max(fp as usize);
            if g.covered() <= need {
                g.grow_to(need);
            }

            let bytecode_read = {
                let v = bytecode_count[pc as usize];
                bytecode_count[pc as usize] = v + 1;
                v
            };

            // Loaded once: the shared Xor/Mul arm needs the discriminant again,
            // and `Op` is wide enough that re-reading it costs a second load.
            let op = self.prog[pc as usize];
            match op {
                Op::Xor { a, b, c } | Op::Mul { a, b, c } => {
                    let is_xor = matches!(op, Op::Xor { .. });
                    let (aa, ab, ac) = (fp + a, fp + b, fp + c);
                    // The row is the equality `m[c] = m[a] op m[b]` over write-once
                    // memory. Normally the operands are known and the result is
                    // computed forward; for a `MUL` whose result is already written
                    // and exactly one of whose operands is not, the runner
                    // back-solves that operand, which is what produces the
                    // range-check complement `y = g^{k-1}·x^{-1}` from
                    // `MUL x·y = g^{k-1}`, and the quotient of `a / b`, with no
                    // dedicated hint.
                    //
                    // `XOR` deliberately does NOT deduce. Nothing asks it to (both
                    // users are `MUL`), and an `XOR` into an already-written cell is
                    // how `assert a == b` is spelled, so deducing there would define
                    // the operand the assert exists to check instead of failing on it.
                    if !is_xor && m.written(ac) {
                        let (ha, hb) = (m.written(aa), m.written(ab));
                        if ha ^ hb {
                            let vk = m.get(if ha { aa } else { ab });
                            if vk.is_zero() {
                                return Err(fail(Fault::BackSolveThroughZero));
                            }
                            m.put(if ha { ab } else { aa }, m.get(ac) * vk.inv())?;
                        }
                    }
                    let va = m.read(aa);
                    let vb = m.read(ab);
                    let vc = if is_xor { va + vb } else { va * vb };
                    m.put(ac, vc)?;
                    let ra = m.bump_access_count(aa);
                    let rb = m.bump_access_count(ab);
                    let rc = m.bump_access_count(ac);
                    let row = Xrow {
                        pc,
                        fp,
                        ra,
                        rb,
                        rc,
                        bytecode_read,
                    };
                    if is_xor {
                        xor.push(row);
                    } else {
                        mul.push(row);
                    }
                    pc += 1;
                }
                Op::Set { o, k } => {
                    let a = fp + o;
                    m.put(a, k)?;
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
                    let a1 = fp + o1;
                    let p = m.read(a1);
                    let p_addr = as_addr(p).ok_or_else(|| fail(Fault::WildPointer { value: p }))?;
                    let base = g.log(p_addr).ok_or_else(|| fail(Fault::WildPointer { value: p }))?;
                    let a2 = base + o2;
                    let a3 = fp + o3;
                    match mode {
                        // Equality m[a2] == m[a3]: carry a written side to the other
                        // (`put` checks it when both are), or link two unwritten sides
                        // until either is written. A range-check touch may leave both
                        // unwritten for good: only the validity of `a2` matters there.
                        DerefMode::Cell => {
                            if m.written(a2) {
                                m.put(a3, m.get(a2))?;
                            } else if m.written(a3) {
                                m.put(a2, m.get(a3))?;
                            } else {
                                m.link(a2, a3);
                            }
                        }
                        DerefMode::Pc => {
                            // The return target and the frame base are stored as
                            // addresses, and JUMP reads them back.
                            g.note(pc as usize + 2);
                            let v = F192::from(g.pow(pc as usize + 2));
                            m.put(a2, v)?;
                        }
                        DerefMode::Fp => {
                            g.note(fp as usize);
                            let v = F192::from(g.pow(fp as usize));
                            m.put(a2, v)?;
                        }
                    }
                    let r1 = m.bump_access_count(a1);
                    let r2 = m.bump_access_count(a2);
                    let r3 = m.bump_access_count(a3);
                    deref.push(Drow {
                        pc,
                        fp,
                        r1,
                        r2,
                        r3,
                        bytecode_read,
                    });
                    pc += 1;
                }
                Op::Jump { oc, od, of } => {
                    let (ac, ad, af) = (fp + oc, fp + od, fp + of);
                    // All three cells are K-valued on EVERY row, taken or not: the
                    // table commits one lane each and their memory flushes carry
                    // literal zeros above it (§sec:tab-jump), which the bus would
                    // otherwise not balance. A guest branches on g-powers; the one
                    // idiom that once branched on a word, `assert a != b`, takes an
                    // inverse hint instead (§sec:prog-div-ne).
                    let c = in_k("JUMP condition", m.read(ac)).map_err(fail)?;
                    let d = in_k("JUMP target", m.read(ad)).map_err(fail)?;
                    let f = in_k("JUMP fp", m.read(af)).map_err(fail)?;
                    // The is-nonzero witness `w = c⁻¹` is never used for control
                    // flow, only recorded as a witness column, so it is not
                    // computed here at all: `JumpTable::fill` batch-inverts every
                    // row's condition at once (§the trace rows in `cpu::trace`).
                    let rc = m.bump_access_count(ac);
                    let rd = m.bump_access_count(ad);
                    let rf = m.bump_access_count(af);
                    let taken = !c.is_zero();
                    jump.push(Jrow {
                        pc,
                        fp,
                        rc,
                        rd,
                        rf,
                        bytecode_read,
                    });
                    if taken {
                        pc = g.log(d).filter(|&t| (t as usize) < self.prog.len()).ok_or_else(|| {
                            fail(Fault::NotAGPower {
                                what: "JUMP target",
                                value: d,
                            })
                        })?;
                        fp = g.log(f).ok_or_else(|| {
                            fail(Fault::NotAGPower {
                                what: "JUMP fp",
                                value: f,
                            })
                        })?;
                    } else {
                        pc += 1;
                    }
                }
                Op::Keccak { in_odd, out_odd, .. } => {
                    use crate::keccak::{ROW_CELLS, STATE_CELLS};
                    let cells = crate::tables::keccak_cells(&self.prog, pc, fp);
                    let input: [F192; STATE_CELLS] = std::array::from_fn(|c| m.read(cells[c]));
                    // The table reads every cell with a literal zero top limb, so anything
                    // else could not balance the bus.
                    for (cell, &value) in input.iter().enumerate() {
                        if value.c2 != 0 {
                            return Err(fail(Fault::NotCanonical { cell, value }));
                        }
                    }
                    // No table constraint covers the output (the relation is proven
                    // by the Keccak reduction, §keccak); the interpreter still computes it so
                    // the output cells are consistent for any later read.
                    let mut lanes = crate::keccak::state_of_cells(&input, in_odd);
                    keccak_step(&lanes);
                    primitives::hash::keccak_f(&mut lanes);
                    let output = crate::keccak::cells_of_state(&lanes, out_odd);
                    for (c, &v) in output.iter().enumerate() {
                        m.put(cells[STATE_CELLS + c], v)?;
                    }
                    // In flush order, so a cell two operands alias still pairs each
                    // read with its own count.
                    let r: [u32; ROW_CELLS] = std::array::from_fn(|c| m.bump_access_count(cells[c]));
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
            let mut rows: Vec<(String, u64)> = self
                .fn_ranges
                .iter()
                .map(|(name, entry, len)| {
                    let total: u64 = p[*entry as usize..(*entry + *len) as usize].iter().sum();
                    (name.clone(), total)
                })
                .collect();
            rows.sort_by_key(|(_, c)| std::cmp::Reverse(*c));
            // `DBG_PROF_DUMP=path`: also write the raw per-pc counts plus the
            // function table, so an offline pass can attribute the straight-line
            // cycles of one big function to its source regions (the call sites of
            // the lowered `for` helpers are the landmarks).
            if let Ok(path) = std::env::var("DBG_PROF_DUMP") {
                let mut out = format!("# steps {steps}\n");
                for (name, entry, len) in &self.fn_ranges {
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
        // Pad memory to a power of two (the boundary tables read a dense image), at
        // least 2^MIN_LOG_MEM cells (doc §Memory), doubled until the stacked witness
        // reaches `min_log_committed`.
        let mem_used = m.used;
        let mut cells = mem_used.next_power_of_two().max(1 << MIN_LOG_MEM);
        let taus = super::layout::table_logs(trace.row_counts());
        let log_bytecode = crate::log2_strict_usize(self.prog.len());
        while super::layout::committed_log(crate::log2_strict_usize(cells), log_bytecode, taus) < self.min_log_committed
        {
            cells *= 2;
        }
        assert!(cells <= 1 << MAX_LOG_MEM, "data memory exceeds 2^{MAX_LOG_MEM} cells");
        Ok(Execution {
            mem: Memory {
                pages: m.pages,
                len: cells,
            },
            cycles: steps,
            mem_used,
            unconstrained_reads: m.unwritten_reads,
            trace,
            gpow: g.into_powers(),
        })
    }
}
