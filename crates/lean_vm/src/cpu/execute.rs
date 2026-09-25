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
    pub mem: Vec<F192>,  // data memory after the run, write-once (size cells, power of two)
    pub cycles: usize,   // number of instructions the run executed (trace length)
    pub mem_used: usize, // cells actually touched, before the power-of-two pad of `mem`
    /// Rows per table before the fill blocks ran: the work the program itself does, as
    /// against the power-of-two heights that get proven. Cost measurements want this one.
    pub base_counts: [usize; crate::tables::N_TABLES],
    /// Cells an instruction read before anything wrote them, up to the halt, so the
    /// value it read was ZERO here and prover-chosen in a proof: memory is a committed
    /// array and the bus only forces accesses to one address to *agree*, never that
    /// the address was written. `zkDSL.md` says don't; this is what says whether the
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
    /// A `BLAKE2s` operand outside the 128-bit embedding.
    NotCanonical { operand: &'static str, value: F192 },
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
            Self::NotCanonical { operand, value } => write!(
                f,
                "BLAKE2s {operand} cell is not a canonical 128-bit embedding: top limb 0x{:016x}",
                value.c2
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

fn pop_witness<'a>(
    witness: &'a HashMap<String, Vec<Vec<F192>>>,
    positions: &mut HashMap<&'a str, usize>,
    name: &'a str,
    len: u32,
) -> Result<&'a [F192], Fault> {
    let entries = witness
        .get(name)
        .ok_or_else(|| Fault::Witness(format!("no witness stream `{name}` (Program::set_witness)")))?;
    let position = positions.entry(name).or_default();
    let entry = entries.get(*position).ok_or_else(|| {
        Fault::Witness(format!(
            "witness stream `{name}` exhausted (needs entry {}, has {})",
            *position + 1,
            entries.len()
        ))
    })?;
    if entry.len() != len as usize {
        return Err(Fault::Witness(format!(
            "witness `{name}` entry {} holds {} values, the destination {len}",
            *position,
            entry.len()
        )));
    }
    *position += 1;
    Ok(entry)
}

impl Program {
    /// Run the program in write-once *fill* mode to produce its [`Execution`]:
    /// the final memory image and the step count, or why it has none. The public
    /// input seeds the first two memory cells `m[0], m[1]` (§sec:e2e-pi), and the
    /// fill blocks bring every table to a power of two, growing one until the
    /// witness reaches [`Program::min_log_committed`]. Compilation yields the
    /// `Program`; executing it (here) and proving it are separate later phases.
    pub fn execute(&self, public_input: [F192; 2]) -> Result<Execution, ExecError> {
        // One interpretation of the program, then the fill. The blocks that bring every
        // table to a power of two are cycles no program code enters (`cpu::filler`), so
        // they run after the chain has halted, by which point the program's own row
        // counts are final; a traversal costs exactly its block's size plus its closing
        // jump, so the solve is exact and no second run is needed to correct it.
        use super::hints::{BitsDest, GPow, RHint};

        let ending_pc = (self.prog.len() - 1) as u32; // last bytecode slot, g^{B-1}

        // g^j and its reverse index g^j ↦ j, seeded for the program counters and
        // return targets and grown on demand past that.
        let mut g = GPow::new(self.prog.len() + 2);

        // Dense write-once data memory (read path stays a vector for speed), the
        // per-cell access count (g^{count}, default g^0 = 1), and each cell's state.
        let n0 = self.main_frame.max(2) as usize;
        let mut m = Mem {
            cells: vec![F192::ZERO; n0],
            state: vec![State::Unwritten; n0],
            count: vec![F64::ONE; n0],
            links: HashMap::new(),
            unwritten_reads: Vec::new(),
            program: self,
            dbg_pc: 0,
            dbg_hint: None,
        };
        // Seed the public input into m[0], m[1] (addresses g^0, g^1, §sec:e2e-pi).
        m.put(0, public_input[0])?;
        m.put(1, public_input[1])?;

        // Per-pc bytecode execution count (g^{count}).
        let mut bytecode_count: Vec<F64> = vec![F64::ONE; self.prog.len()];

        let mut next_free = self.main_frame;
        let (mut pc, mut fp) = (0u32, 0u32);
        let mut steps = 0usize;
        // Per-pc hint index. `self.hints` is keyed by pc, so probing it each step
        // costs a hash of the counter for what is almost always a miss; the
        // program has one bytecode slot per pc, so flatten the map into a dense
        // table: 0 = no hints, otherwise the 1-based index into `hint_lists`.
        let mut hint_at = vec![0u32; self.prog.len()];
        let mut hint_lists: Vec<&[RHint]> = Vec::with_capacity(self.hints.len());
        for (&hpc, hs) in &self.hints {
            hint_lists.push(hs.as_slice());
            hint_at[hpc as usize] = hint_lists.len() as u32;
        }
        // `DBG_PROF=1`: per-pc step counts, printed as a per-function cycle
        // profile after the run (needs `fn_ranges`, i.e. a compiled program).
        let mut prof: Option<Vec<u64>> = std::env::var("DBG_PROF").is_ok().then(|| vec![0u64; self.prog.len()]);

        // Per-stream cursor into the named witness data (`hint_witness` pops
        // sequentially).
        let mut witness_positions: HashMap<&str, usize> = HashMap::new();
        // Baby-step table for `hint_decompose_bits_exponent`, built on first use.
        let mut dlog_cache: Option<(GPow, F64)> = None;

        // Rows per table before the fill runs, and the cells the program read unwritten,
        // both captured when the chain halts: the fill's rows exist to reach a
        // power-of-two height and are soundness-neutral (doc §Filling the tables), so
        // they read cells nobody writes as a matter of course.
        let mut base_counts: Option<[usize; crate::tables::N_TABLES]> = None;
        let mut unconstrained_reads: Vec<u32> = Vec::new();

        // Per-opcode trace rows, accumulated during the walk and assembled into the
        // `Trace` once the run finishes (alongside the final count columns).
        let mut xor: Vec<Xrow> = Vec::new();
        let mut mul: Vec<Xrow> = Vec::new();
        let mut set: Vec<Srow> = Vec::new();
        let mut deref: Vec<Drow> = Vec::new();
        let mut jump: Vec<Jrow> = Vec::new();
        let mut blake2s: Vec<Brow> = Vec::new();

        // A cell that is not `Written` holds ZERO. A `DEREF` between two unwritten cells
        // links them, and a write to either reaches the other at once.
        #[derive(Clone, Copy, PartialEq, Eq)]
        enum State {
            Unwritten,
            Linked,
            Written,
        }

        // The three dense per-cell vectors, kept in lockstep. Every method on the hot
        // path is `#[inline(always)]`: they sit in the interpreter's opcode loop.
        struct Mem<'a> {
            cells: Vec<F192>,
            state: Vec<State>,
            count: Vec<F64>,
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
            // Grow the dense vectors so `idx` is in range. All accessed cells
            // satisfy cell < next_free after their frame's allocation, so this
            // only ever extends.
            #[inline(always)]
            fn ensure(&mut self, idx: usize) {
                if idx >= self.cells.len() {
                    let n = idx + 1;
                    self.cells.resize(n, F192::ZERO);
                    self.state.resize(n, State::Unwritten);
                    self.count.resize(n, F64::ONE);
                }
            }
            #[inline(always)]
            fn written(&self, cell: u32) -> bool {
                self.state.get(cell as usize) == Some(&State::Written)
            }
            // A hint's read, which pins nothing: what a hint computes is advice the
            // instructions go on to check.
            #[inline(always)]
            fn get(&self, cell: u32) -> F192 {
                self.cells.get(cell as usize).copied().unwrap_or(F192::ZERO)
            }
            // An instruction's read. An unwritten cell reads as ZERO, which is then written
            // there: the row is filled from the final image, which has to agree.
            #[inline(always)]
            fn read(&mut self, cell: u32) -> F192 {
                let c = cell as usize;
                self.ensure(c);
                if self.state[c] != State::Written {
                    self.state[c] = State::Written;
                    self.unwritten_reads.push(cell);
                }
                self.cells[c]
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
                let c = cell as usize;
                self.ensure(c);
                let s = self.state[c];
                if s == State::Written && self.cells[c] != v {
                    return Err(self.conflict(cell, v));
                }
                self.cells[c] = v;
                self.state[c] = State::Written;
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
                    if self.state[x as usize] == State::Unwritten {
                        self.state[x as usize] = State::Linked;
                    }
                    self.links.entry(x).or_default().push(y);
                }
            }
            #[cold]
            fn conflict(&self, cell: u32, v: F192) -> ExecError {
                let fault = Fault::Conflict {
                    cell,
                    had: self.cells[cell as usize],
                    new: v,
                    hint: self.dbg_hint,
                };
                ExecError::new(self.program, self.dbg_pc, fault)
            }
            // Read the running access count and advance it by ×g (the free increment).
            // ×g is ×x, i.e. `mul_by_g`, a shift+fold rather than a PMULL; this runs on every
            // memory access (several million per run), so the cheap form matters.
            #[inline(always)]
            fn bump_access_count(&mut self, cell: u32) -> F64 {
                self.ensure(cell as usize);
                let cell_idx = cell as usize;
                let count = self.count[cell_idx];
                self.count[cell_idx] = mul_by_g(count);
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

        // The program's own chain runs to the halt sentinel; the fill blocks then run, one
        // cycle at a time. A cycle is entered at its block's first instruction, in a frame
        // of its own, and traversed for the rows `filler::plan` asks of it, always a whole
        // number of traversals, so the state tuples it pushes are exactly the ones it pulls
        // (doc §Filling the tables). `left` is the rows still to run in the current cycle,
        // and `None` while the chain runs.
        let mut cycles: std::vec::IntoIter<(u32, u32, usize)> = Vec::new().into_iter();
        let mut left: Option<usize> = None;
        loop {
            // The chain reached the sentinel, or a cycle has run its rows.
            let switch = match left {
                None => pc == ending_pc,
                Some(n) => n == 0,
            };
            if switch {
                if left.is_none() {
                    if fp != 0 {
                        return Err(ExecError::new(self, pc, Fault::HaltOutsideMain { fp }));
                    }
                    let counts = [xor.len(), mul.len(), set.len(), deref.len(), jump.len(), blake2s.len()];
                    base_counts = Some(counts);
                    unconstrained_reads = std::mem::take(&mut m.unwritten_reads);
                    use super::filler::{self, frame as fr};
                    let mut runs: Vec<(u32, u32, usize)> = Vec::new();
                    // A hand-assembled program carries no blocks and has to land on
                    // powers of two by itself, which `Layout` checks.
                    if !self.filler.is_empty() {
                        // A whole frame per cycle, past every cell the program touched, so
                        // the memory the fill leaves is known before it runs and the plan
                        // reaching `min_log_committed` is solved for here, once.
                        let start = m.cells.len();
                        let log_bytecode = crate::log2_strict_usize(self.prog.len());
                        let plan = filler::plan(counts, self.min_log_committed, |plan| {
                            let cells = start + filler::frames(plan) * fr::CELLS as usize;
                            super::layout::committed_log(
                                crate::log2_strict_usize(cells.next_power_of_two().max(1 << MIN_LOG_MEM)),
                                log_bytecode,
                                filler::filled(counts, plan).map(crate::log2_strict_usize),
                            )
                        });
                        let mut frame = start as u32;
                        for (block_pc, size, n) in filler::cycles(&self.filler, &plan) {
                            g.grow_to(frame as usize);
                            g.note(frame as usize);
                            m.ensure((frame + fr::CELLS - 1) as usize);
                            // What the closing jump reads: back to the block's own first
                            // instruction, in this same frame. Then the pointer the `DEREF`
                            // dummy follows, memory cell `0`.
                            m.put(frame + fr::DEST, F192::from(g.pow(block_pc as usize)))?;
                            m.put(frame + fr::NEXT_FP, F192::from(g.pow(frame as usize)))?;
                            m.put(frame + fr::PTR, F192::ONE)?;
                            runs.push((block_pc, frame, n * (size as usize + 1)));
                            frame += fr::CELLS;
                        }
                    }
                    cycles = runs.into_iter();
                }
                match cycles.next() {
                    Some((p, f, rows)) => {
                        pc = p;
                        fp = f;
                        left = Some(rows);
                    }
                    None => break,
                }
            }
            if let Some(n) = &mut left {
                *n -= 1;
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
                let hs = hint_lists[hint_at[pc as usize] as usize - 1];
                for h in hs {
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
                                    let max_frames = u64::from(MAX_CELLS.saturating_sub(next_free)) / u64::from(size);
                                    let max_span = max_frames.saturating_sub(1) as usize;
                                    let mut exponent = g.log(span);
                                    while exponent.is_none() && g.covered() <= max_span {
                                        g.grow_to((2 * g.covered()).min(max_span));
                                        exponent = g.log(span);
                                    }
                                    let n = exponent.ok_or_else(|| fail(Fault::OutOfMemory))? + 1;
                                    (ptr, size.checked_mul(n).ok_or_else(|| fail(Fault::OutOfMemory))?)
                                }
                                // A runtime size is carried in the exponent:
                                // the cell holds g^k, allocate k cells (reverse
                                // g-power lookup, growing the index if needed).
                                RHint::AllocDyn { ptr, size } => {
                                    let sz = in_k("HeapBuf size", m.get(fp + size)).map_err(fail)?;
                                    let cells = match g.log(sz) {
                                        Some(cells) => cells,
                                        None => {
                                            g.grow_to(1 << 20);
                                            g.log(sz).ok_or_else(|| {
                                                fail(Fault::NotAGPower {
                                                    what: "HeapBuf size",
                                                    value: sz,
                                                })
                                            })?
                                        }
                                    };
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
                                let v = m.cells[c as usize];
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
                        RHint::WitnessStack { name, base, len } => {
                            let values =
                                pop_witness(&self.witness, &mut witness_positions, name, *len).map_err(fail)?;
                            for (k, &value) in values.iter().enumerate() {
                                m.put(fp + base + k as u32, value)?;
                            }
                        }
                        RHint::WitnessHeap { name, ptr, lo, len } => {
                            let b = heap_base(&m, &mut g, fp + ptr, "hint_witness heap pointer").map_err(fail)?;
                            let values =
                                pop_witness(&self.witness, &mut witness_positions, name, *len).map_err(fail)?;
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
                        RHint::BitDecompose { value, bits, nbits } => {
                            assert!(*nbits <= 192, "a machine word has 192 bits");
                            let v = m.get(fp + value);
                            let limbs = [v.c0, v.c1, v.c2];
                            let bb = bits_base(&m, &mut g, fp, *bits, "decompose pointer").map_err(fail)?;
                            for j in 0..*nbits {
                                let bit = (limbs[j as usize / 64] >> (j % 64)) & 1;
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
                bytecode_count[pc as usize] = mul_by_g(v);
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
                    let base = match g.log(p_addr) {
                        Some(b) => b,
                        None => {
                            // Not indexed yet: grow the g-power index to the minimum
                            // memory size, since range-check touches point anywhere below
                            // their bound (≤ 2^MIN_LOG_MEM), not just at allocated
                            // frames/buffers. A value still absent is no valid
                            // pointer: a wild deref, or a failed range check
                            // (`assert log _ < _`) surfacing honestly.
                            g.grow_to(1 << MIN_LOG_MEM);
                            g.log(p_addr).ok_or_else(|| fail(Fault::WildPointer { value: p }))?
                        }
                    };
                    let a2 = base + o2;
                    let a3 = fp + o3;
                    match mode {
                        // Equality m[a2] == m[a3]: carry a written side to the other
                        // (`put` checks it when both are), or link two unwritten sides
                        // until either is written. A range-check touch may leave both
                        // unwritten for good: only the validity of `a2` matters there.
                        DerefMode::Cell => {
                            if m.written(a2) {
                                m.put(a3, m.cells[a2 as usize])?;
                            } else if m.written(a3) {
                                m.put(a2, m.cells[a3 as usize])?;
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
                Op::Blake2s { ins, cv, out, md } => {
                    // Four independently-addressed 128-bit message chunks, each a
                    // single cell; the chaining value and the output each span two
                    // consecutive cells; the metadata is one more cell.
                    let (aa0, aa1, ab0, ab1) = (fp + ins[0], fp + ins[1], fp + ins[2], fp + ins[3]);
                    let acv = fp + cv;
                    let ac = fp + out;
                    let amd = fp + md;
                    let words = [aa0, aa1, ab0, ab1, acv, acv + 1, amd].map(|a| m.read(a));
                    // Naming the operand and the line matters most for the metadata,
                    // the one a guest builds with field arithmetic rather than reads.
                    if let Some((i, &value)) = words.iter().enumerate().find(|(_, w)| w.c2 != 0) {
                        const CELLS: [&str; 7] = ["m0", "m1", "m2", "m3", "cv0", "cv1", "md"];
                        return Err(fail(Fault::NotCanonical {
                            operand: CELLS[i],
                            value,
                        }));
                    }
                    let va = [F64(words[0].c0), F64(words[0].c1), F64(words[1].c0), F64(words[1].c1)];
                    let vb = [F64(words[2].c0), F64(words[2].c1), F64(words[3].c0), F64(words[3].c1)];
                    let vcv = [F64(words[4].c0), F64(words[4].c1), F64(words[5].c0), F64(words[5].c1)];
                    let metadata = words[6];
                    // Compress the 64 message bytes to the 32-byte result, then
                    // write it to c's two cells. No table constraint covers the
                    // digest (the relation is proven by flock, §hash_flock); the
                    // interpreter still computes the definite digest so the output
                    // cells are consistent for any later read.
                    let vc = blake2s_compress(va, vb, vcv, metadata);
                    let outputs = [F192::new(vc[0].0, vc[1].0, 0), F192::new(vc[2].0, vc[3].0, 0)];
                    m.put(ac, outputs[0])?;
                    m.put(ac + 1, outputs[1])?;
                    let ra = [m.bump_access_count(aa0), m.bump_access_count(aa1)];
                    let rb = [m.bump_access_count(ab0), m.bump_access_count(ab1)];
                    let rcv = [m.bump_access_count(acv), m.bump_access_count(acv + 1)];
                    let rc = [m.bump_access_count(ac), m.bump_access_count(ac + 1)];
                    // Last, matching the flush order, so an md cell aliasing another
                    // operand still pairs each read with its own count.
                    let rmd = m.bump_access_count(amd);
                    blake2s.push(Brow {
                        pc,
                        fp,
                        ra,
                        rb,
                        rcv,
                        rc,
                        rmd,
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

        // Pad memory to a power of two (the boundary tables read a dense image),
        // at least 2^MIN_LOG_MEM cells (doc §Memory).
        let mem_used = m.cells.len();
        let cells = m.cells.len().next_power_of_two().max(1 << MIN_LOG_MEM);
        assert!(cells <= 1 << MAX_LOG_MEM, "data memory exceeds 2^{MAX_LOG_MEM} cells");
        m.cells.resize(cells, F192::ZERO);
        m.count.resize(cells, F64::ONE);
        let trace = Trace {
            xor,
            mul,
            set,
            deref,
            jump,
            blake2s,
            mem_count: m.count,
            bytecode_count,
        };
        Ok(Execution {
            mem: m.cells,
            cycles: steps,
            mem_used,
            // Taken when the chain halted, which every run does before it can leave the
            // loop at all.
            base_counts: base_counts.expect("the run halted, so its own counts were taken"),
            unconstrained_reads,
            trace,
        })
    }
}
