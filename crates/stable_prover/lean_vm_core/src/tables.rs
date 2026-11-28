//! The six instruction tables (`doc/leanvm/body/07-instruction-tables.tex`). Their columns and links are the
//! verifier's ([`verifier::layout::tables`]), read here with their forms over [`F128`] ([`Links`]); each table adds how
//! to fill its columns from the trace and, for `JUMP`, its identities as one [`Form`]. Column indices are local
//! (`0..n_committed_columns`); `cpu`'s layout offsets them by the verifier's [`GLOBAL_COLUMN_BASES`].
//!
//! Columns are `K`-valued (`F64`); a machine word is 128-bit (`E = F128`), two `K` lanes. Nothing a row derives is a
//! column, and neither is anything it only reads where one of its pointers points: those are [`Read`]s, weighed on
//! the side of the link that holds them. Every table's pointer columns hold one-hot words ([`Chunks`]).

use crate::cpu::from_scalar;
use crate::cpu::{Memory, Op, Trace};
use crate::form::Form;
use crate::link::pointer::Chunks;
use primitives::field::{F64, F128};
use std::sync::OnceLock;

pub use verifier::layout::{
    GLOBAL_COLUMN_BASES, N_TABLES, OP_DEREF, OP_JUMP, OP_KECCAK, OP_MUL, OP_SET, OP_XOR, TABLE_LOG_FLOORS, TABLE_WIDTHS,
};
const _: () = assert!(crate::keccak::MIN_STEPS == 1 << TABLE_LOG_FLOORS[OP_KECCAK]);

/// The verifier's tables, built once: what this tree reads its columns and links from.
pub fn layout_tables() -> &'static [verifier::layout::Table] {
    static TABLES: OnceLock<Vec<verifier::layout::Table>> = OnceLock::new();
    TABLES.get_or_init(verifier::layout::tables)
}

/// The local index of table `t`'s column `name`.
pub fn column(t: usize, name: &str) -> usize {
    (layout_tables()[t].columns.iter())
        .position(|c| c == name)
        .unwrap_or_else(|| panic!("table {t} has no column {name}"))
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

/// What a table's fill reads: the trace rows, the final memory image, `g^0..` for the pcs, frames and offsets, the
/// program, and the pointer layout.
pub struct FillCtx<'a> {
    pub(crate) trace: &'a Trace,
    pub(crate) mem: &'a Memory,
    pub(crate) gpow: &'a [F64],
    pub(crate) prog: &'a [Op],
    pub(crate) chunks: &'a Chunks,
    /// This table's height `2^tau`, every column's length. Rows past the trace's hold [`Table::padding`].
    pub(crate) height: usize,
    pub(crate) padding: Vec<F64>,
}

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
        }
    }

    /// `g^i`.
    pub(crate) fn g_at(&self, i: u32) -> F64 {
        self.gpow[i as usize]
    }

    /// The one-hot word of pointer `sigma`.
    pub(crate) fn ptr(&self, sigma: u32) -> F64 {
        F64(self.chunks.encode(sigma as usize))
    }

    /// The two `K` lanes of the word in cell `addr`.
    pub(crate) fn limbs(&self, addr: u32) -> [F64; 2] {
        self.mem.word(addr as usize).to_limbs().map(F64)
    }

    /// Write every column of a table with these trace rows: row `u` is `row(&rows[u])`, a padding row past them.
    fn fill_rows<const N: usize, R: Sync>(
        &self,
        out: &mut [&mut [F64]],
        rows: &[R],
        row: impl Fn(&R) -> [F64; N] + Sync,
    ) {
        assert!(rows.len() <= self.height, "a table's rows fit its height");
        let padding: [F64; N] = self.padding.clone().try_into().expect("a padding value per column");
        write_rows(out, self.height, |u| rows.get(u).map_or(padding, &row));
    }
}

/// Rows a task of [`write_rows`] writes at most.
const ROW_BLOCK: usize = 512;

/// Write `height` rows to the columns `out`, row `u` being `row(u)`, in parallel over blocks of rows. A column with no
/// rows is held elsewhere and not written.
pub(crate) fn write_rows<const N: usize>(
    out: &mut [&mut [F64]],
    height: usize,
    row: impl Fn(usize) -> [F64; N] + Sync,
) {
    assert_eq!(out.len(), N, "a value per column");
    assert!(
        out.iter().all(|c| c.is_empty() || c.len() == height),
        "every column written is the table's height"
    );
    let block = height.min(ROW_BLOCK);
    if block == 0 {
        return;
    }
    // `blocks[b][c]`: column `c`'s rows `b·block..(b + 1)·block`, empty for a column not written.
    let mut blocks: Vec<Vec<&mut [F64]>> = (0..height / block).map(|_| Vec::with_capacity(N)).collect();
    for column in out.iter_mut() {
        if column.is_empty() {
            blocks.iter_mut().for_each(|b| b.push(&mut []));
        }
        for (b, run) in blocks.iter_mut().zip(column.chunks_mut(block)) {
            b.push(run);
        }
    }
    parallel::chunks_mut(&mut blocks, 1, |b, columns| {
        for j in 0..block {
            for (column, value) in columns[0].iter_mut().zip(row(b * block + j)) {
                if let Some(slot) = column.get_mut(j) {
                    *slot = value;
                }
            }
        }
    });
}

/// The local indices of table `t`'s columns `names`.
fn columns<const N: usize>(t: usize, names: [&str; N]) -> [usize; N] {
    names.map(|name| column(t, name))
}

// ---- the trait ---------------------------------------------------------------

/// One instruction table, over its local columns.
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
    /// How many identities [`constraint`](Table::constraint) weighs.
    fn n_constraints(&self) -> usize {
        0
    }
    /// The table's identities as one degree-2 form over its local columns, identity `i` weighed by `coefs[i]`. It
    /// vanishes on every valid row and every padding row.
    fn constraint(&self, coefs: &[F128]) -> Form {
        assert!(coefs.is_empty(), "a table with constraints must state them");
        Form::new(self.n_committed_columns())
    }
    /// The table's links, the verifier's.
    fn links(&self) -> Links {
        Links::of(&layout_tables()[self.opcode()].links, self.n_committed_columns())
    }
    /// Fill the table's columns from the trace: `out[c]` is local column `c`'s rows, `FillCtx::height` of them, to
    /// be written in full, its padding value past the trace's rows. A column with no rows is held elsewhere (a
    /// `KECCAK` input lane, by `q_keccak`) and is not written.
    fn fill(&self, ctx: &FillCtx, out: &mut [&mut [F64]]);
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
const _: () = assert!(MIN_COMMITTED_COLUMNS == 5, "SET's five columns");

// ---- KECCAK's cells ----------------------------------------------------------

/// What each cell a `KECCAK` row touches is addressed by, in link order (the four `m` cells, the four `tail` cells,
/// `b8`, the four `cap` cells, then the thirteen output cells): the offset operand it follows, in the order of their
/// bytecode slots ([`KeccakOp`]), and how far.
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

/// A `KECCAK` instruction: its offset operands `m`, `tail`, `b8`, `cap` and `out` in the order of their bytecode
/// slots, its two layout flags, and the output cells it writes.
#[derive(Clone, Copy)]
pub(crate) struct KeccakOp {
    pub(crate) offsets: [u32; 8],
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

/// The one limb of a row's read cells that holds no lane, `(cell, high)`, in the even layout and in the odd one.
pub(crate) const FREE_LIMB: [(usize, bool); 2] = [free_limb(false), free_limb(true)];

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

// ---- the tables --------------------------------------------------------------

/// `XOR` and `MUL`: neither commits its result, the destination's word being linear in the words its pointers read.
/// `MUL` commits its first word, the coefficient of its read of the second.
struct Arith {
    is_xor: bool,
}

impl Table for Arith {
    fn opcode(&self) -> usize {
        if self.is_xor { OP_XOR } else { OP_MUL }
    }
    fn fill(&self, ctx: &FillCtx, out: &mut [&mut [F64]]) {
        let operands = |pc: u32| match ctx.prog[pc as usize] {
            Op::Xor { a, b, c } | Op::Mul { a, b, c } => (a, b, c),
            op => unreachable!("a three-operand row's pc {pc} holds {op:?}"),
        };
        if self.is_xor {
            debug_assert_eq!(
                layout_tables()[OP_XOR].columns,
                ["pc", "fp", "ix_a", "ix_b", "ix_c", "ix_bc", "ix_cycle"]
            );
            ctx.fill_rows(out, &ctx.trace.xor, |r| {
                let (a, b, c) = operands(r.pc);
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
            debug_assert_eq!(
                layout_tables()[OP_MUL].columns,
                ["pc", "fp", "a_0", "a_1", "ix_a", "ix_b", "ix_c", "ix_bc", "ix_cycle"]
            );
            ctx.fill_rows(out, &ctx.trace.mul, |r| {
                let (a, b, c) = operands(r.pc);
                let [a_0, a_1] = ctx.limbs(r.fp + a);
                [
                    ctx.g_at(r.pc),
                    ctx.g_at(r.fp),
                    a_0,
                    a_1,
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

/// `SET`: the immediate is read from the instruction.
struct SetTable;

impl Table for SetTable {
    fn opcode(&self) -> usize {
        OP_SET
    }
    fn fill(&self, ctx: &FillCtx, out: &mut [&mut [F64]]) {
        debug_assert_eq!(layout_tables()[OP_SET].columns, ["pc", "fp", "ix", "ix_bc", "ix_cycle"]);
        ctx.fill_rows(out, &ctx.trace.set, |r| {
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

/// `DEREF`: its pointer word is committed, one `K` lane, and addresses the store at `ptr·o2`.
struct DerefTable;

impl Table for DerefTable {
    fn opcode(&self) -> usize {
        OP_DEREF
    }
    /// The target is the cell `ptr·g^{o2}` names, which the run recorded (`Drow::store`).
    fn fill(&self, ctx: &FillCtx, out: &mut [&mut [F64]]) {
        debug_assert_eq!(
            layout_tables()[OP_DEREF].columns,
            [
                "pc",
                "fp",
                "ptr",
                "o2",
                "s",
                "ix_ptr",
                "ix_target",
                "ix_local",
                "ix_bc",
                "ix_cycle"
            ]
        );
        ctx.fill_rows(out, &ctx.trace.deref, |r| {
            let (o1, o2, o3, mode) = match ctx.prog[r.pc as usize] {
                Op::Deref { o1, o2, o3, mode } => (o1, o2, o3, mode),
                op => unreachable!("a DEREF row's pc {} holds {op:?}", r.pc),
            };
            let [ptr, high] = ctx.limbs(r.fp + o1);
            debug_assert_eq!(high, F64::ZERO, "a DEREF pointer is K-valued");
            [
                ctx.g_at(r.pc),
                ctx.g_at(r.fp),
                ptr,
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

/// `JUMP`: its three words are committed, one `K` lane each, and so is its successor, which its identities tie to
/// the jump.
struct JumpTable;

impl Table for JumpTable {
    fn opcode(&self) -> usize {
        OP_JUMP
    }
    fn n_constraints(&self) -> usize {
        4
    }
    /// `b + cond·w` and `cond·(b + 1)` (§sec:tab-jump), then `pc' + b·v_pc + (b + 1)·g·pc` and
    /// `fp' + b·v_fp + (b + 1)·fp`, weighed by `coefs` (`verifier::layout`'s `jump_constraints`).
    ///
    /// The first two force `b = [cond ≠ 0]`: when `cond ≠ 0` the second gives `b = 1` (and the first `w = cond⁻¹`);
    /// when `cond = 0` the first gives `b = 0`. The last two fix the successor.
    fn constraint(&self, coefs: &[F128]) -> Form {
        let col = |name| column(OP_JUMP, name);
        let [pc, fp, cond, dest, frame, pc_next, fp_next, w, b] =
            ["pc", "fp", "v_cond", "v_pc", "v_fp", "pc_next", "fp_next", "w", "b"].map(col);
        let g = coefs[2].mul_base(primitives::field::g_pow(1));
        let mut form = Form::new(self.n_committed_columns());
        for (c, k) in [
            (b, coefs[0]),
            (cond, coefs[1]),
            (pc_next, coefs[2]),
            (pc, g),
            (fp_next, coefs[3]),
            (fp, coefs[3]),
        ] {
            form.coeffs[c] += k;
        }
        let products = [
            (cond, w, coefs[0]),
            (cond, b, coefs[1]),
            (b, dest, coefs[2]),
            (b, pc, g),
            (b, frame, coefs[3]),
            (b, fp, coefs[3]),
        ];
        form.prods = products.iter().map(|&(x, y, k)| (x.min(y), x.max(y), k)).collect();
        form
    }
    /// The three words are `K`-valued on every row, taken or not (`cpu::execute` rejects anything else). `b = [cond ≠
    /// 0]`, `w = cond⁻¹` (zero when `cond` is), and the successor is the jump's when `b = 1`, the next instruction's
    /// in the same frame otherwise.
    fn fill(&self, ctx: &FillCtx, out: &mut [&mut [F64]]) {
        debug_assert_eq!(
            layout_tables()[OP_JUMP].columns,
            [
                "pc", "fp", "v_cond", "v_pc", "v_fp", "pc_next", "fp_next", "w", "b", "ix_c", "ix_d", "ix_f", "ix_bc",
                "ix_cycle"
            ]
        );
        ctx.fill_rows(out, &ctx.trace.jump, |r| {
            let (oc, od, of) = match ctx.prog[r.pc as usize] {
                Op::Jump { oc, od, of } => (oc, od, of),
                op => unreachable!("a JUMP row's pc {} holds {op:?}", r.pc),
            };
            let word = |o: u32| {
                let [lo, hi] = ctx.limbs(r.fp + o);
                debug_assert_eq!(hi, F64::ZERO, "a JUMP word outside K at pc {}", r.pc);
                lo
            };
            let (cond, dest, frame) = (word(oc), word(od), word(of));
            let taken = !cond.is_zero();
            let (pc_next, fp_next) = if taken {
                (dest, frame)
            } else {
                (ctx.g_at(r.pc) * F64::G, ctx.g_at(r.fp))
            };
            [
                ctx.g_at(r.pc),
                ctx.g_at(r.fp),
                cond,
                dest,
                frame,
                pc_next,
                fp_next,
                if taken { cond.inv() } else { F64::ZERO },
                F64(u64::from(taken)),
                ctx.ptr(r.fp + oc),
                ctx.ptr(r.fp + od),
                ctx.ptr(r.fp + of),
                ctx.ptr(r.pc),
                ctx.ptr(r.step),
            ]
        });
    }
}

/// `KECCAK`: the permutation of a state in memory, proven by the Keccak reduction over `q_keccak` (§annex:keccak). Its
/// fifty lane columns are virtual (`cpu::keccak_value`): the input lanes are `q_keccak`'s slots, and the output lanes'
/// claims are the reduction's claim on the output.
struct KeccakTable;

impl Table for KeccakTable {
    fn opcode(&self) -> usize {
        OP_KECCAK
    }
    /// The input lanes are `q_keccak`'s and have no rows here. The output lanes are the input permuted, whichever
    /// output cells the row writes. Each operand's pointer names its first cell: the later cells of the `tail`, `cap`
    /// and `out` runs are shifted reads of it.
    fn fill(&self, ctx: &FillCtx, out: &mut [&mut [F64]]) {
        use verifier::layout::{KECCAK_IN, KECCAK_IX, KECCAK_OUT};
        const N: usize = TABLE_WIDTHS[OP_KECCAK];
        let [pc, fp, o_out, odd_in, odd_out, out_two, out_all, free] = columns(
            OP_KECCAK,
            ["pc", "fp", "o_out", "odd_in", "odd_out", "out_two", "out_all", "free"],
        );
        let [ix_bc, ix_cycle] = columns(OP_KECCAK, ["ix_bc", "ix_cycle"]);
        debug_assert_eq!(column(OP_KECCAK, "ix_m0"), KECCAK_IX);
        let flag = |b: bool| F64(u64::from(b));
        ctx.fill_rows(out, &ctx.trace.keccak, |r| {
            let k = KeccakOp::of(&ctx.prog[r.pc as usize]);
            let word = |c: usize| ctx.mem.word(k.cell(r.fp, c) as usize);
            let (two, all) = k.out_cells.flags();
            let (free_cell, high) = FREE_LIMB[usize::from(k.in_odd)];
            let input = crate::keccak::state_of_cells(k.in_odd, word);
            let mut output = input;
            primitives::hash::keccak_f(&mut output);
            let mut v = [F64::ZERO; N];
            (v[pc], v[fp], v[o_out]) = (ctx.g_at(r.pc), ctx.g_at(r.fp), ctx.g_at(k.offsets[7]));
            [v[odd_in], v[odd_out], v[out_two], v[out_all]] = [k.in_odd, k.out_odd, two, all].map(flag);
            v[free] = F64(if high { word(free_cell).c1 } else { word(free_cell).c0 });
            v[KECCAK_IN..KECCAK_OUT].copy_from_slice(&input.map(F64));
            v[KECCAK_OUT..KECCAK_IX].copy_from_slice(&output.map(F64));
            for (i, &offset) in k.offsets.iter().enumerate() {
                v[KECCAK_IX + i] = ctx.ptr(r.fp + offset);
            }
            (v[ix_bc], v[ix_cycle]) = (ctx.ptr(r.pc), ctx.ptr(r.step));
            v
        });
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use primitives::test_rng::Rng;

    /// `JUMP`'s form is the verifier's identities, weighed.
    #[test]
    fn jump_constraint_is_the_verifiers() {
        let mut rng = Rng::new(0x1a);
        let table = &layout_tables()[OP_JUMP];
        for _ in 0..8 {
            let coefs = rng.ext_vec(4);
            let row = rng.ext_vec(table.width());
            let row_e: Vec<verifier::E> = row.iter().map(|v| verifier::E::new(v.c0, v.c1)).collect();
            let theirs: F128 = (table.constraints)(&row_e)
                .into_iter()
                .zip(&coefs)
                .map(|(i, &c)| from_scalar(i) * c)
                .sum();
            assert_eq!(JumpTable.constraint(&coefs).evaluate(&row), theirs);
        }
        assert_eq!(JumpTable.n_constraints(), table.n_constraints());
    }

    /// Every table's links are the verifier's: the same columns, slots, shifts and gates, and every form the same
    /// polynomial at random rows. The padding row satisfies the identities.
    #[test]
    fn links_match_the_verifier() {
        use verifier::layout::Read as V;
        let mut rng = Rng::new(0x11);
        for (t, table) in tables().into_iter().enumerate() {
            let theirs = &layout_tables()[t];
            assert_eq!((table.opcode(), table.n_committed_columns()), (t, theirs.width()));
            let (ours, theirs) = (table.links(), &theirs.links);
            assert_eq!(ours.pointers(), theirs.pointers());
            assert_eq!(ours.max_shift(), theirs.max_shift());
            for _ in 0..4 {
                let row = rng.ext_vec(table.n_committed_columns());
                let row_e: Vec<verifier::E> = row.iter().map(|v| verifier::E::new(v.c0, v.c1)).collect();
                let same = |ours: &Form, theirs: &verifier::layout::Form| {
                    assert_eq!(ours.evaluate(&row), from_scalar(theirs.evaluate(&row_e)), "table {t}");
                };
                let (s, their_s) = (&ours.state, theirs.state());
                assert_eq!((s.cycle, s.pc, s.fp), (their_s.cycle, their_s.pc, their_s.fp));
                s.next.iter().zip(&their_s.next).for_each(|(a, b)| same(a, b));
                let (b, their_b) = (&ours.bytecode, theirs.bytecode_link());
                assert_eq!(
                    (b.pointer, b.pc, b.opcode),
                    (their_b.pointer, their_b.pc, their_b.opcode)
                );
                assert_eq!(b.operands.len(), their_b.operands.len());
                for ((slots, form), (their_slots, their_form)) in b.operands.iter().zip(&their_b.operands) {
                    assert_eq!(slots, their_slots);
                    same(form, their_form);
                }
                assert_eq!(ours.memory.len(), theirs.memory.len());
                for (a, their_a) in ours.memory.iter().zip(&theirs.memory) {
                    assert_eq!(
                        (a.pointer, a.shift, a.gate, a.frame),
                        (their_a.pointer, their_a.shift, their_a.gate, their_a.frame)
                    );
                    same(&a.address, &their_a.address);
                    same(&a.value, &their_a.value);
                    assert_eq!(a.reads.len(), their_a.reads.len());
                    for (r, their_r) in a.reads.iter().zip(&their_a.reads) {
                        match (r, their_r) {
                            (Read::Word { pointer, scale }, V::Word { pointer: p, scale: q }) => {
                                assert_eq!(pointer, p);
                                same(scale, q);
                            }
                            (Read::Slot { slot, scale }, V::Slot { slot: s, scale: q })
                            | (Read::Frame { slot, scale }, V::Frame { slot: s, scale: q })
                            | (Read::Pc { slot, scale }, V::Pc { slot: s, scale: q }) => {
                                assert_eq!((slot, *scale), (s, from_scalar(*q)));
                            }
                            _ => panic!("table {t}: {r:?} is not {their_r:?}"),
                        }
                    }
                }
            }
            let padding: Vec<F128> = table.padding().into_iter().map(F128::from).collect();
            let coefs = vec![F128::new(3, 5); table.n_constraints()];
            assert_eq!(table.constraint(&coefs).evaluate(&padding), F128::ZERO);
        }
    }
}
