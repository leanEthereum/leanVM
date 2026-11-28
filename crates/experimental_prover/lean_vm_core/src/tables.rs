//! The six instruction tables (`doc/leanvm/body/07-instruction-tables.tex`). Their columns and links are the
//! verifier's ([`verifier::layout::tables`]), read here with their forms over [`F128`] ([`Links`]); each table adds how
//! to fill its columns from the trace and, for `JUMP`, its identities as one [`Form`]. Column indices are local
//! (`0..n_committed_columns`); `cpu` offsets them by the verifier's [`GLOBAL_COLUMN_BASES`].
//!
//! Columns are `K`-valued (`F64`); a machine word is 128-bit (`E = F128`), two `K` lanes. Nothing a row derives is a
//! column, and neither is anything it only reads where one of its pointers points: those are [`Read`]s, weighed on
//! the side of the link that holds them. Every table's pointer columns hold one-hot words ([`Chunks`]).

use crate::cpu::from_scalar;
use crate::cpu::{Memory, Op, Row, Rows, Trace};
use crate::form::Form;
use crate::link::pointer::Chunks;
use primitives::field::{F64, F128, g_pow};
use std::sync::OnceLock;
use std::sync::atomic::{AtomicBool, Ordering::Relaxed};

pub use verifier::layout::{
    GLOBAL_COLUMN_BASES, N_TABLES, OP_DEREF, OP_JUMP, OP_KECCAK, OP_MUL, OP_SET, OP_XOR, TABLE_LOG_FLOORS, TABLE_WIDTHS,
};
const _: () = assert!(crate::keccak::MIN_STEPS == 1 << TABLE_LOG_FLOORS[OP_KECCAK]);

/// The verifier's tables, built once: what this tree reads its columns and links from.
pub fn layout_tables() -> &'static [verifier::layout::Table] {
    static TABLES: OnceLock<Vec<verifier::layout::Table>> = OnceLock::new();
    TABLES.get_or_init(verifier::layout::tables)
}

// ---- links -------------------------------------------------------------------

/// A row's step of the state chain: its cycle pointer, its `(pc, fp)`, and the successor state, affine in its columns.
#[derive(Clone, Debug)]
pub struct StateLink {
    pub cycle: usize,
    pub pc: usize,
    pub fp: usize,
    pub next: [Form; 2],
}

/// A row's read of the program: its pointer, its `pc`, its opcode, and each operand equation `Σ_{s ∈ slots} BC_s =
/// form` it checks against its instruction, weighed by the first slot's challenge (`verifier::layout::BytecodeLink`).
#[derive(Clone, Debug)]
pub struct BytecodeLink {
    pub pointer: usize,
    pub pc: usize,
    pub opcode: usize,
    pub operands: Vec<(Vec<usize>, Form)>,
}

/// A term of an access's word that the row reads where one of its pointers points, rather than from its columns
/// (`verifier::layout::Read`).
#[derive(Clone, Debug)]
pub enum Read {
    /// `scale·word(σ)`, the word in the cell the pointer column `pointer` names; `scale` is affine.
    Word { pointer: usize, scale: Form },
    /// `scale·BC_slot(σ_bc)`, a slot of the row's instruction.
    Slot { slot: usize, scale: F128 },
    /// `scale·fp·BC_slot(σ_bc)`.
    Frame { slot: usize, scale: F128 },
    /// `scale·pc·BC_slot(σ_bc)`, where `pc = g^{σ_bc}`.
    Pc { slot: usize, scale: F128 },
}

/// A row's memory access (`verifier::layout::Access`): its pointer and how far past the pointer's cell it reads, the
/// column gating it if any, the address and the word `lo + y·hi`. The address is `address + g^e·fp·BC_slot(σ_bc)` for
/// `frame = Some((slot, e))`, and the word is `value + Σ reads`.
#[derive(Clone, Debug)]
pub struct Access {
    pub pointer: usize,
    pub shift: usize,
    pub gate: Option<usize>,
    pub address: Form,
    pub frame: Option<(usize, u64)>,
    pub value: Form,
    pub reads: Vec<Read>,
}

/// Everything a table links, in local column indices: the verifier's links, their forms over [`F128`].
#[derive(Clone, Debug)]
pub struct Links {
    pub state: StateLink,
    pub bytecode: BytecodeLink,
    pub memory: Vec<Access>,
    pointers: Vec<usize>,
}

impl Links {
    /// The verifier's links of a table of `n_cols` columns.
    pub fn of(links: &verifier::layout::Links, n_cols: usize) -> Self {
        let form = |f: &verifier::layout::Form| Form::from_verifier(f, n_cols);
        let state = links.state();
        let bytecode = links.bytecode_link();
        let read = |r: &verifier::layout::Read| match *r {
            verifier::layout::Read::Word { pointer, ref scale } => Read::Word {
                pointer,
                scale: form(scale),
            },
            verifier::layout::Read::Slot { slot, scale } => Read::Slot {
                slot,
                scale: from_scalar(scale),
            },
            verifier::layout::Read::Frame { slot, scale } => Read::Frame {
                slot,
                scale: from_scalar(scale),
            },
            verifier::layout::Read::Pc { slot, scale } => Read::Pc {
                slot,
                scale: from_scalar(scale),
            },
        };
        Self {
            state: StateLink {
                cycle: state.cycle,
                pc: state.pc,
                fp: state.fp,
                next: state.next.each_ref().map(form),
            },
            bytecode: BytecodeLink {
                pointer: bytecode.pointer,
                pc: bytecode.pc,
                opcode: bytecode.opcode,
                operands: (bytecode.operands.iter())
                    .map(|(slots, f)| (slots.clone(), form(f)))
                    .collect(),
            },
            memory: (links.memory.iter())
                .map(|a| Access {
                    pointer: a.pointer,
                    shift: a.shift,
                    gate: a.gate,
                    address: form(&a.address),
                    frame: a.frame,
                    value: form(&a.value),
                    reads: a.reads.iter().map(read).collect(),
                })
                .collect(),
            pointers: links.pointers(),
        }
    }

    /// The pointer columns, in the order Hotwire numbers them: the cycle, the bytecode, then each access's pointer in
    /// order of first use.
    pub fn pointers(&self) -> &[usize] {
        &self.pointers
    }

    /// The largest shift any access takes.
    pub fn max_shift(&self) -> usize {
        self.memory.iter().map(|a| a.shift).max().unwrap_or(0)
    }
}

// ---- fill context ------------------------------------------------------------

/// Inputs a table needs to fill its columns: the trace rows, the final memory
/// image (for read values), and `g^0..` for O(1) address/operand lookups.
pub struct FillCtx<'a> {
    pub(crate) trace: &'a Trace,
    pub(crate) mem: &'a Memory,
    pub(crate) gpow: &'a [F64],
    pub(crate) prog: &'a [Op],
    /// The pointer layout every pointer column is written in.
    chunks: &'a Chunks,
    /// This table's height `2^tau`, the length of every window in `out`. Rows past the
    /// trace's are padding rows, each holding `padding` ([`Table::padding`]).
    height: usize,
    padding: Vec<F64>,
    /// Whether [`Self::runs`], which writes every column, ran: a fill that skipped it would leave the stacked witness
    /// holding uninitialized slots, so [`fill_table`] checks it.
    filled: AtomicBool,
}

/// Where one column's values go: its window in the stacked witness, or a
/// private buffer if the column is virtual.
pub(crate) type ColumnOut<'a> = crate::witness::ColMut<'a>;

/// Rows a fill gathers before streaming them out: whole cache lines of each column.
const RUN: usize = 32;

impl<'a> FillCtx<'a> {
    pub(crate) fn new(
        trace: &'a Trace,
        mem: &'a Memory,
        gpow: &'a [F64],
        prog: &'a [Op],
        chunks: &'a Chunks,
        height: usize,
        padding: Vec<F64>,
    ) -> Self {
        Self {
            trace,
            mem,
            gpow,
            prog,
            chunks,
            height,
            padding,
            filled: AtomicBool::new(false),
        }
    }

    fn g_at(&self, i: u32) -> F64 {
        self.gpow[i as usize]
    }

    /// The one-hot word of pointer `sigma`.
    fn ptr(&self, sigma: u32) -> F64 {
        F64(self.chunks.encode(sigma as usize))
    }

    /// The three frame offsets of an `XOR`/`MUL` row, read back from the bytecode: a row records only its `(pc, fp)`
    /// (`cpu::trace`).
    fn ternary_operands(&self, pc: u32) -> (u32, u32, u32) {
        match self.prog[pc as usize] {
            Op::Xor { a, b, c } | Op::Mul { a, b, c } => (a, b, c),
            op => unreachable!("a three-operand row's pc {pc} holds {op:?}"),
        }
    }

    /// [`Self::runs`] from one closure per row, which returns the row's local columns.
    fn cols<const N: usize, R: Sync>(&self, out: &mut [ColumnOut], rows: &Rows<R>, f: impl Fn(&R) -> [F64; N] + Sync) {
        self.runs(out, rows.len(), |start, len, buf: &mut [_; N]| {
            for j in 0..len {
                for (column, v) in buf.iter_mut().zip(f(rows.get(start + j))) {
                    column[j] = v;
                }
            }
        });
    }

    /// Write all `N` local columns in one pass, so a row, its instruction and the words it names are read once:
    /// `f(start, len, buf)` writes trace rows `start..start + len` of column `c` to `buf[c][..len]`, and each column
    /// holds its padding value to the end of its window. A column with no window is held elsewhere (a KECCAK input
    /// lane, by `q_keccak`) and is not written.
    fn runs<const N: usize>(
        &self,
        out: &mut [ColumnOut],
        n_rows: usize,
        f: impl Fn(usize, usize, &mut [[F64; RUN]; N]) + Sync,
    ) {
        let n = self.height;
        assert_eq!(out.len(), N, "a fill writes every column of its table");
        assert!(n_rows <= n, "a table's rows must fit its cube");
        let dst: [Option<&ColumnOut>; N] = std::array::from_fn(|c| {
            (!out[c].is_empty()).then(|| {
                assert_eq!(out[c].len(), n, "column {c} has the wrong window length");
                &out[c]
            })
        });
        self.filled.store(true, Relaxed);
        let padding: [[F64; RUN]; N] = std::array::from_fn(|c| [self.padding[c]; RUN]);
        // A run of rows is gathered column by column, then streamed out: the
        // stack is read by a later pass, so its lines need not be fetched.
        parallel::for_each_chunk(n.div_ceil(RUN), |first, end| {
            let stream = primitives::stream::Stream::new();
            for b in first..end {
                let start = b * RUN;
                let len = RUN.min(n - start);
                let mut buf = padding;
                if start < n_rows {
                    f(start, len.min(n_rows - start), &mut buf);
                }
                for (window, column) in dst.iter().zip(&buf) {
                    if let Some(window) = window {
                        // SAFETY: block `b` writes rows `start..start + len` of each window, in bounds and disjoint
                        // from every other block's, and the dispatch blocks until every write is finished.
                        unsafe { window.write(&stream, start, &column[..len]) };
                    }
                }
            }
        });
    }

    /// The two `K`-lanes of the 128-bit word in memory cell `addr`.
    fn limbs(&self, addr: u32) -> [F64; 2] {
        self.mem.word(addr as usize).to_limbs().map(F64)
    }
}

/// Fill one table's columns and check that every window was written. The stack is
/// allocated uninitialized, so a table that wrote nothing would be read as
/// indeterminate bytes rather than caught by a length mismatch.
pub(crate) fn fill_table(table: &dyn Table, ctx: &FillCtx, out: &mut [ColumnOut]) {
    table.fill(ctx, out);
    assert!(ctx.filled.load(Relaxed), "a table left columns unwritten");
}

// ---- the trait ---------------------------------------------------------------

/// One instruction table, over its local columns.
///
/// Every table's last column is its cycle pointer.
pub trait Table: Sync {
    /// Its opcode, which is also its index in [`tables`] and in the verifier's.
    fn opcode(&self) -> usize;
    /// Number of committed columns (local indices `0..n_committed_columns`).
    fn n_committed_columns(&self) -> usize {
        TABLE_WIDTHS[self.opcode()]
    }
    /// The row a padding row holds, past the rows the program executed (§sec:e2e-pad): the verifier's.
    fn padding(&self) -> Vec<F64> {
        (layout_tables()[self.opcode()].padding.iter())
            .map(|e| {
                assert_eq!(e.c1, 0, "a padding value is K-valued");
                F64(e.c0)
            })
            .collect()
    }
    /// How many identities [`constraint`](Table::constraint) folds. Defaults to none, which is every table but
    /// `JUMP`: a value a row derives is a form its links carry, which needs no identity to tie it.
    fn n_constraints(&self) -> usize {
        0
    }
    /// The table's identities as one degree-2 form over its columns, in local order (e.g. `jump::V_COND`), identity
    /// `i` weighted by `pows[i]`, the link's challenges for them. The form vanishes on every valid row. The slice is
    /// exactly [`n_constraints`](Table::n_constraints) long: an identity indexed past its end panics. The default is
    /// the constraint-free case; a table that declares constraints and forgets to state them trips the assert
    /// instead of dropping them.
    fn constraint(&self, pows: &[F128]) -> Form {
        assert!(pows.is_empty(), "a table with constraints must state them");
        Form::new(self.n_committed_columns())
    }
    /// The table's links, the verifier's.
    fn links(&self) -> Links {
        Links::of(&layout_tables()[self.opcode()].links, self.n_committed_columns())
    }
    /// Fill this table's columns from the trace: `out[i]` is local column `i`'s
    /// window, already at its padded length. Every window must be written in full, by
    /// one `FillCtx::runs` or `FillCtx::cols` over all the columns.
    fn fill(&self, ctx: &FillCtx, out: &mut [ColumnOut]);
}

/// The tables in opcode order `[XOR, MUL, SET, DEREF, JUMP, KECCAK]`, the order of `row_counts` and `taus`.
pub fn tables() -> [&'static dyn Table; N_TABLES] {
    [
        &Arith { is_xor: true },
        &Arith { is_xor: false },
        &SetTable,
        &DerefTable,
        &JumpTable,
        &KeccakTable,
    ]
}

/// What each cell a `KECCAK` row touches is addressed by, in link order (the four `m` cells, the
/// four `tail` cells, `b8`, the four `cap` cells, then the thirteen output cells): the offset
/// operand it follows, in the order of their bytecode slots ([`KeccakOp`]), and how far.
const KECCAK_CELLS: [(usize, u32); crate::keccak::ROW_CELLS] = {
    let mut t = [(0, 0); crate::keccak::ROW_CELLS];
    let mut c = 0;
    while c < t.len() {
        t[c] = match c {
            0..4 => (c, 0),
            4..8 => (4, c as u32 - 4),
            8 => (5, 0),
            9..13 => (6, c as u32 - 9),
            _ => (7, c as u32 - 13),
        };
        c += 1;
    }
    t
};

/// A `KECCAK` instruction: its offset operands `m`, `tail`, `b8`, `cap` and `out` in the order of
/// their bytecode slots, its two layout flags, and the output cells it writes.
#[derive(Clone, Copy)]
pub(crate) struct KeccakOp {
    offsets: [u32; 8],
    pub(crate) in_odd: bool,
    pub(crate) out_odd: bool,
    pub(crate) out_cells: crate::cpu::OutCells,
}

impl KeccakOp {
    pub(crate) fn of(op: &Op) -> Self {
        match *op {
            Op::Keccak {
                m,
                tail,
                b8,
                cap,
                out,
                in_odd,
                out_odd,
                out_cells,
            } => Self {
                offsets: [m[0], m[1], m[2], m[3], tail, b8, cap, out],
                in_odd,
                out_odd,
                out_cells,
            },
            op => unreachable!("not a KECCAK: {op:?}"),
        }
    }

    /// Cell `c` (in link order) of a row at frame `fp`.
    pub(crate) fn cell(&self, fp: u32, c: usize) -> u32 {
        let (offset, step) = self.cell_parts(c);
        fp + offset + step
    }

    /// Cell `c` of a row at frame `fp` is `fp + offset + step`.
    pub(crate) fn cell_parts(&self, c: usize) -> (u32, u32) {
        let (operand, step) = KECCAK_CELLS[c];
        (self.offsets[operand], step)
    }
}

/// The one limb of a row's read cells that holds no lane, `(cell, high)`, in the even layout and
/// in the odd one.
const FREE_LIMB: [(usize, bool); 2] = [free_limb(false), free_limb(true)];

const fn free_limb(odd: bool) -> (usize, bool) {
    let lanes = verifier::layout::keccak_cell_lanes(odd);
    let mut c = 0;
    loop {
        match lanes[c] {
            (None, _) => return (c, false),
            (_, None) => return (c, true),
            _ => c += 1,
        }
    }
}

// ---- XOR / MUL ---------------------------------------------------------------

/// `XOR` and `MUL_NATIVE`. Neither commits its result: the destination's word is linear in the words its pointers
/// read, `v_A + v_B` for `XOR` and `v_A·v_B` for `MUL`, so it is a sum of reads (§sec:link-row). `XOR` commits no word at
/// all; `MUL` commits `v_A`, the coefficient of its read of `v_B`. The three addresses are `fp` times the
/// instruction's offsets, read from its slots 4, 5, 6.
struct Arith {
    is_xor: bool,
}

impl Table for Arith {
    fn opcode(&self) -> usize {
        if self.is_xor { OP_XOR } else { OP_MUL }
    }
    fn fill(&self, ctx: &FillCtx, out: &mut [ColumnOut]) {
        let rows = if self.is_xor { &ctx.trace.xor } else { &ctx.trace.mul };
        if self.is_xor {
            ctx.cols(out, rows, |r| {
                let (a, b, c) = ctx.ternary_operands(r.pc);
                [
                    ctx.g_at(r.pc),
                    ctx.g_at(r.fp),
                    ctx.ptr(r.fp + a),
                    ctx.ptr(r.fp + b),
                    ctx.ptr(r.fp + c),
                    ctx.ptr(r.pc),
                    ctx.ptr(r.step),
                ]
            });
        } else {
            ctx.cols(out, rows, |r| {
                let (a, b, c) = ctx.ternary_operands(r.pc);
                let va = ctx.limbs(r.fp + a);
                [
                    ctx.g_at(r.pc),
                    ctx.g_at(r.fp),
                    va[0],
                    va[1],
                    ctx.ptr(r.fp + a),
                    ctx.ptr(r.fp + b),
                    ctx.ptr(r.fp + c),
                    ctx.ptr(r.pc),
                    ctx.ptr(r.step),
                ]
            });
        }
    }
}

// ---- SET ---------------------------------------------------------------------

struct SetTable;

impl Table for SetTable {
    fn opcode(&self) -> usize {
        OP_SET
    }
    fn fill(&self, ctx: &FillCtx, out: &mut [ColumnOut]) {
        let rows = &ctx.trace.set;
        ctx.cols(out, rows, |r| {
            let o = match ctx.prog[r.pc as usize] {
                Op::Set { o, .. } => o,
                op => unreachable!("a SET row's pc {} holds {op:?}", r.pc),
            };
            [
                ctx.g_at(r.pc),
                ctx.g_at(r.fp),
                ctx.ptr(r.fp + o),
                ctx.ptr(r.pc),
                ctx.ptr(r.step),
            ]
        });
    }
}

// ---- DEREF -------------------------------------------------------------------

/// `DEREF`. Its pointer word is one `K` lane, so the memory read carries a literal zero above it, and it addresses
/// the store target `ptr·o2`; `s = f_pc + f_fp` is 1 exactly when the store takes a `K`-valued source rather than the
/// local word.
struct DerefTable;

impl Table for DerefTable {
    fn opcode(&self) -> usize {
        OP_DEREF
    }
    fn fill(&self, ctx: &FillCtx, out: &mut [ColumnOut]) {
        let rows = &ctx.trace.deref;
        ctx.cols(out, rows, |r| {
            let (o1, o2, o3, mode) = match ctx.prog[r.pc as usize] {
                Op::Deref { o1, o2, o3, mode } => (o1, o2, o3, mode),
                op => unreachable!("a DEREF row's pc {} holds {op:?}", r.pc),
            };
            let p = ctx.mem.word((r.fp + o1) as usize);
            debug_assert!(p.as_base().is_some(), "deref pointer must be K-valued");
            [
                ctx.g_at(r.pc),
                ctx.g_at(r.fp),
                F64(p.c0),
                ctx.g_at(o2),
                F64(u64::from(mode.f_pc() || mode.f_fp())),
                ctx.ptr(r.fp + o1),
                ctx.ptr(r.store),
                ctx.ptr(r.fp + o3),
                ctx.ptr(r.pc),
                ctx.ptr(r.step),
            ]
        });
    }
}

// ---- JUMP --------------------------------------------------------------------

struct JumpTable;

pub(crate) mod jump {
    pub const PC: usize = 0;
    pub const FP: usize = 1;
    // The condition, destination and frame words are all K-valued on every row, taken or not, so each is a SINGLE
    // lane whose memory read carries a literal zero above it: the memory link holds only if the stored word is in K,
    // exactly as for the DEREF pointer. `assert_in_k(a, b)` is an untaken jump that relies on it. A guest branches
    // on g-powers, never on an arbitrary word: `assert a != b` takes an inverse hint instead of a branch
    // (§sec:prog-div-ne). The three cells sit at `fp` times the instruction's slots 4, 5, 6.
    pub const V_COND: usize = 2;
    pub const V_PC: usize = 3;
    pub const V_FP: usize = 4;
    // The successor state, committed so that the state link stays affine: `b·(v_pc, v_fp) + (b+1)·(g·pc, fp)`.
    pub const PC_NEXT: usize = 5;
    pub const FP_NEXT: usize = 6;
    // Committed columns no link reads: the inverse hint `w = c⁻¹` and the taken indicator `b = [c ≠ 0]` it
    // certifies (the `JUMP` table in `doc/leanvm/body/07-instruction-tables.tex`). Both are single K lanes. The
    // pointers follow.
    pub const W: usize = 7;
    pub const B: usize = 8;
    pub const N: usize = 14;
}

impl Table for JumpTable {
    fn opcode(&self) -> usize {
        OP_JUMP
    }
    fn n_constraints(&self) -> usize {
        4
    }
    /// `b = cond·w` and `cond·(b+1) = 0` (§sec:tab-jump), then `pc' = b·v_pc + (b+1)·g·pc` and
    /// `fp' = b·v_fp + (b+1)·fp`, weighted `pows[0..4]` (`verifier::layout`'s `jump_constraints`).
    ///
    /// The first two force `b = [cond ≠ 0]`: when `cond ≠ 0` the second gives `b = 1` (and the first
    /// `w = cond⁻¹`); when `cond = 0` the first gives `b = 0`. The last two fix the successor.
    fn constraint(&self, pows: &[F128]) -> Form {
        use jump::*;
        let mut form = Form::new(N);
        let g_pc = pows[2].mul_base(g_pow(1));
        form.coeffs[B] = pows[0];
        form.coeffs[V_COND] = pows[1];
        form.coeffs[PC_NEXT] = pows[2];
        form.coeffs[PC] = g_pc;
        form.coeffs[FP_NEXT] = pows[3];
        form.coeffs[FP] = pows[3];
        form.prods = vec![
            (V_COND, W, pows[0]),
            (V_COND, B, pows[1]),
            (B, V_PC, pows[2]),
            (B, PC, g_pc),
            (B, V_FP, pows[3]),
            (B, FP, pows[3]),
        ];
        form
    }
    fn fill(&self, ctx: &FillCtx, out: &mut [ColumnOut]) {
        use jump::*;
        let rows = &ctx.trace.jump;
        let ins = |r: &Row| match ctx.prog[r.pc as usize] {
            Op::Jump { oc, od, of } => (oc, od, of),
            op => unreachable!("a JUMP row's pc {} holds {op:?}", r.pc),
        };
        let cell = |r: &Row, o: u32| ctx.mem.word((r.fp + o) as usize);
        ctx.runs(out, rows.len(), |start, len, buf: &mut [_; N]| {
            // The is-nonzero witness `w = c⁻¹` (0 where c = 0) by one batched Montgomery inversion per run: column
            // `W` first holds the running product `acc` of the nonzero conditions before its row, and `acc` ends as
            // their full product (nonzero, hence invertible). The conditions lie in K, a subfield, so the inversion
            // runs in K.
            let mut acc = F64::ONE;
            for j in 0..len {
                let r = rows.get(start + j);
                let (oc, od, of) = ins(r);
                // The three cells are K-valued on every row, taken or not (`cpu::execute` rejects anything else),
                // so each is one lane and the memory link carries literal zeros above it.
                let c = cell(r, oc);
                debug_assert!(c.as_base().is_some(), "a JUMP condition outside K at pc {}", r.pc);
                let c = F64(c.c0);
                let (d, f) = (F64(cell(r, od).c0), F64(cell(r, of).c0));
                let (pc_next, fp_next) = if c.is_zero() {
                    (ctx.g_at(r.pc) * F64::G, ctx.g_at(r.fp))
                } else {
                    (d, f)
                };
                let row = [
                    ctx.g_at(r.pc),
                    ctx.g_at(r.fp),
                    c,
                    d,
                    f,
                    pc_next,
                    fp_next,
                    acc,
                    F64(u64::from(!c.is_zero())),
                    ctx.ptr(r.fp + oc),
                    ctx.ptr(r.fp + od),
                    ctx.ptr(r.fp + of),
                    ctx.ptr(r.pc),
                    ctx.ptr(r.step),
                ];
                for (column, v) in buf.iter_mut().zip(row) {
                    column[j] = v;
                }
                if !c.is_zero() {
                    acc *= c;
                }
            }
            let mut inv = acc.inv();
            for j in (0..len).rev() {
                let c = buf[V_COND][j];
                if c.is_zero() {
                    buf[W][j] = F64::ZERO;
                } else {
                    buf[W][j] *= inv;
                    inv *= c;
                }
            }
        });
    }
}

// ---- KECCAK ---------------------------------------------------------------------

/// `KECCAK` (“KECCAK” in `doc/leanvm/body/07-instruction-tables.tex`): the Keccak-f\[1600\]
/// permutation of a state in memory. The four `m` cells and `b8` are addressed *independently*
/// at `fp·o_i` (`o_i = g^{m[i]}`), so a caller hashing e.g. `(tweak, pp)` need not copy them into
/// adjacent cells; the four `tail` cells, the four `cap` cells and the thirteen output cells are
/// consecutive runs based at `fp·o_T`, `fp·o_C` and `fp·o_O`. No address is committed: each is an
/// access's form, the product `fp·o_X·g^k`. The permutation relating output lanes to input
/// lanes carries no table constraint either: it is proven by the Keccak reduction over
/// `q_keccak` ([`crate::keccak`]), which leaves this table with no identity of its own.
///
/// The cells read and written hold the lanes in the layout their flag names
/// ([`verifier::layout::keccak_cell_lanes`]), the flags bound by the bytecode read, so a cell's limb is the
/// form `a + flag·(a + b)` of its lane in either layout, of degree two. The one limb of a read
/// cell that holds no lane is the column `FREE`; written, it is zero. The fifty lanes are
/// value columns, listed in `n_committed_columns` (they need a local index for the links), but
/// `cpu` treats them as VIRTUAL ([`crate::cpu::keccak_value`]): the input lanes are `q_keccak`'s
/// slots, which hold those words, so their claims route there and the fill leaves them alone,
/// and the output lanes' claims are the Keccak reduction's claim on the output.
struct KeccakTable;

pub(crate) mod keccakt {
    pub const PC: usize = 0;
    pub const FP: usize = 1;
    pub const O_OUT: usize = 2; // the g-power of the output run's offset; the seven read offsets are the instruction's
    pub const IN_ODD: usize = O_OUT + 1; // the layout read …
    pub const OUT_ODD: usize = IN_ODD + 1; // … and the layout written
    pub const OUT_TWO: usize = OUT_ODD + 1; // whether output cell 1 is written …
    pub const OUT_ALL: usize = OUT_TWO + 1; // … and cells 2..13
    pub const FREE: usize = OUT_ALL + 1; // the read limb that holds no lane
    pub const V_IN: usize = verifier::layout::KECCAK_IN; // the 25 input lanes, in lane order …
    pub const V_OUT: usize = verifier::layout::KECCAK_OUT; // … and the 25 output lanes
    pub const R0: usize = verifier::layout::KECCAK_IX; // one pointer per offset operand, at the cell it names
    pub const RBC: usize = R0 + 8;
    pub const CYC: usize = RBC + 1;
    pub const N: usize = CYC + 1;
}

impl Table for KeccakTable {
    fn opcode(&self) -> usize {
        OP_KECCAK
    }
    /// Every column but the input lanes, which are `q_keccak`'s and have no window here. The output lanes are the
    /// input permuted again, since a row writes only the output cells its bytecode requests.
    fn fill(&self, ctx: &FillCtx, out: &mut [ColumnOut]) {
        use crate::keccak::state_of_cells;
        use keccakt::*;
        let rows = &ctx.trace.keccak;
        let flag = |b: bool| F64(u64::from(b));
        ctx.cols(out, rows, |r| {
            let k = KeccakOp::of(&ctx.prog[r.pc as usize]);
            let (two, all) = k.out_cells.flags();
            let (cell, high) = FREE_LIMB[usize::from(k.in_odd)];
            let free = ctx.mem.word(k.cell(r.fp, cell) as usize);
            let mut lanes = state_of_cells(k.in_odd, |c| ctx.mem.word(k.cell(r.fp, c) as usize));
            primitives::hash::keccak_f(&mut lanes);
            let mut v = [F64::ZERO; N];
            v[PC] = ctx.g_at(r.pc);
            v[FP] = ctx.g_at(r.fp);
            v[O_OUT] = ctx.g_at(k.offsets[7]);
            [v[IN_ODD], v[OUT_ODD], v[OUT_TWO], v[OUT_ALL]] = [k.in_odd, k.out_odd, two, all].map(flag);
            v[FREE] = F64(if high { free.c1 } else { free.c0 });
            v[V_OUT..R0].copy_from_slice(&lanes.map(F64));
            v[R0..RBC].copy_from_slice(&k.offsets.map(|o| ctx.ptr(r.fp + o)));
            v[RBC] = ctx.ptr(r.pc);
            v[CYC] = ctx.ptr(r.step);
            v
        });
    }
}

/// The fewest committed columns of a table's row: a run of `n` steps commits at least `n` times it, which bounds the
/// steps of a provable run (the interpreter's step limit).
pub(crate) const MIN_COMMITTED_COLUMNS: usize = {
    let mut min = TABLE_WIDTHS[0];
    let mut t = 1;
    while t < N_TABLES {
        if TABLE_WIDTHS[t] < min {
            min = TABLE_WIDTHS[t];
        }
        t += 1;
    }
    min
};

// The fills' columns are the verifier's (`tests::fills_write_the_verifier_columns`).
const _: () = assert!(
    jump::N == TABLE_WIDTHS[OP_JUMP] && keccakt::N == TABLE_WIDTHS[OP_KECCAK] && keccakt::V_IN == keccakt::FREE + 1
);

#[cfg(test)]
mod tests {
    use super::*;
    use primitives::field::powers;

    /// Each fill writes the verifier's columns in its order.
    #[test]
    fn fills_write_the_verifier_columns() {
        let names = |t: usize| layout_tables()[t].columns.clone();
        assert_eq!(names(OP_XOR), ["pc", "fp", "ix_a", "ix_b", "ix_c", "ix_bc", "ix_cycle"]);
        let mul = ["pc", "fp", "a_0", "a_1", "ix_a", "ix_b", "ix_c", "ix_bc", "ix_cycle"];
        assert_eq!(names(OP_MUL), mul);
        assert_eq!(names(OP_SET), ["pc", "fp", "ix", "ix_bc", "ix_cycle"]);
        let deref = [
            "pc",
            "fp",
            "ptr",
            "o2",
            "s",
            "ix_ptr",
            "ix_target",
            "ix_local",
            "ix_bc",
            "ix_cycle",
        ];
        assert_eq!(names(OP_DEREF), deref);
        let jump = names(OP_JUMP);
        for (c, name) in [
            (jump::PC, "pc"),
            (jump::FP, "fp"),
            (jump::V_COND, "v_cond"),
            (jump::V_PC, "v_pc"),
            (jump::V_FP, "v_fp"),
            (jump::PC_NEXT, "pc_next"),
            (jump::FP_NEXT, "fp_next"),
            (jump::W, "w"),
            (jump::B, "b"),
            (9, "ix_c"),
            (10, "ix_d"),
            (11, "ix_f"),
            (12, "ix_bc"),
            (13, "ix_cycle"),
        ] {
            assert_eq!(jump[c], name);
        }
        let keccak = names(OP_KECCAK);
        for (c, name) in [
            (keccakt::PC, "pc"),
            (keccakt::FP, "fp"),
            (keccakt::O_OUT, "o_out"),
            (keccakt::IN_ODD, "odd_in"),
            (keccakt::OUT_ODD, "odd_out"),
            (keccakt::OUT_TWO, "out_two"),
            (keccakt::OUT_ALL, "out_all"),
            (keccakt::FREE, "free"),
            (keccakt::V_IN, "in_0"),
            (keccakt::V_OUT, "out_0"),
            (keccakt::R0, "ix_m0"),
            (keccakt::RBC, "ix_bc"),
            (keccakt::CYC, "ix_cycle"),
        ] {
            assert_eq!(keccak[c], name);
        }
    }

    /// `JUMP`'s identities vanish on an honest row, taken or not, and an untaken row that jumps fails them.
    #[test]
    fn jump_identities_vanish_on_an_honest_row() {
        use jump::*;
        let pows = powers(F128::new(0x9e37_79b9_7f4a_7c15, 0x1234_5678_9abc_def0), 4);
        let (pc, fp) = (g_pow(17), g_pow(40));
        // The condition is K-valued (a single lane on its read, §sec:tab-jump), so `w = c⁻¹` is in K too.
        for cond in [F64::ZERO, F64(0x9e37_79b9_7f4a_7c15)] {
            let mut row = vec![F64::ZERO; N];
            row[PC] = pc;
            row[FP] = fp;
            row[V_COND] = cond;
            row[W] = cond.inv();
            row[B] = if cond.is_zero() { F64::ZERO } else { F64::ONE };
            (row[V_PC], row[V_FP]) = (g_pow(3), g_pow(90));
            (row[PC_NEXT], row[FP_NEXT]) = if cond.is_zero() {
                (pc * F64::G, fp)
            } else {
                (row[V_PC], row[V_FP])
            };
            let eval = |row: &[F64]| {
                let row: Vec<F128> = row.iter().copied().map(F128::from).collect();
                JumpTable.constraint(&pows).eval(&row, false)
            };
            assert_eq!(eval(&row), F128::ZERO, "cond = {cond:?}");
            if cond.is_zero() {
                row[PC_NEXT] = row[V_PC];
                assert_ne!(eval(&row), F128::ZERO, "an untaken jump that jumps");
            }
        }
    }
}
