//! Per-instruction tables (`doc/leanvm/body/07-instruction-tables.tex`). Each opcode's section declares, in one
//! place, its committed columns, how to fill them from the trace, its bus
//! interactions (flushes), the read-count columns that feed the count channel,
//! and its degree-2 constraint; `Table` names them. Column indices here are *local* (`0..n_committed_columns`);
//! `cpu` offsets them by the verifier's `GLOBAL_COLUMN_BASES` to global witness columns.
//!
//! Columns are `K`-valued (`F64`). The pc/fp, operands, counts, opcodes and
//! separators are single `K`-columns; a machine word (memory value) is
//! 128-bit (`E = F128`), committed as two `K`-lane columns. Nothing a row
//! derives is a column at all: an operand address `fp·o`, an `XOR`/`MUL` result,
//! the `DEREF` store, the `JUMP` successors are each written out as the degree-2
//! bus coordinate that carries them (§sec:m3), which leaves `JUMP`'s is-nonzero
//! indicator as the one identity any table has. Every identity is `K`-valued,
//! so a relation on machine words is written out lane by lane. A table hands its
//! identities to the table sumcheck as a degree-2 form (`Table::constraint`).

use crate::constraints::Form;
use crate::cpu::{Memory, Op, Trace, row_len};
use crate::leaf::Coord::{self, Col, Const, GCol, Prod};
use primitives::field::{F64, F128, mul_by_g};
use primitives::hash::STATE_LANES;
use std::ops::Range;
use verifier::layout::TABLE_WIDTHS;

// ---- the identities ----------------------------------------------------------
//
// Every identity is `K`-valued, like the columns it reads and like the bus
// coordinates (§sec:air). A relation between machine words is therefore written out
// lane by lane, with the tower multiplication unrolled by hand (`MUL`'s result),
// rather than assembled into one `E` equation.

// ---- shared bus vocabulary ---------------------------------------------------

/// `g^k` by repeated `mul_by_g` from `g^0 = 1` (`g = x`): at compile time, or for a small `k`.
pub(crate) const fn g_pow(k: usize) -> F64 {
    let mut acc = F64::ONE;
    let mut i = 0;
    while i < k {
        acc = mul_by_g(acc);
        i += 1;
    }
    acc
}

// Domain separators (coordinate 0 of every bus tuple) and opcodes (coordinate 3 of a bytecode tuple), the verifier's.
pub(crate) const SEP_STATE: F64 = F64(verifier::layout::SEP_STATE.c0);
pub(crate) const SEP_MEM: F64 = F64(verifier::layout::SEP_MEM.c0);
pub(crate) const SEP_BYTECODE: F64 = F64(verifier::layout::SEP_BYTECODE.c0);
pub(crate) const OP_XOR: F64 = g_pow(verifier::layout::OP_XOR);
pub(crate) const OP_MUL: F64 = g_pow(verifier::layout::OP_MUL);
pub(crate) const OP_SET: F64 = g_pow(verifier::layout::OP_SET);
pub(crate) const OP_DEREF: F64 = g_pow(verifier::layout::OP_DEREF);
pub(crate) const OP_JUMP: F64 = g_pow(verifier::layout::OP_JUMP);
pub(crate) const OP_KECCAK: F64 = g_pow(verifier::layout::OP_KECCAK);

// ---- flush builder -----------------------------------------------------------

/// Collects a table's push/pull bus interactions in *local* column indices. The
/// push/pull of a memory-checked entry differ only by one coordinate carrying the
/// post-increment `g·count` (`GCol`) instead of the pre-increment (`Col`); these
/// helpers encode that pairing so each table reads declaratively.
pub(crate) struct FlushBuilder {
    pub(crate) push: Vec<Vec<Coord>>,
    pub(crate) pull: Vec<Vec<Coord>>,
    /// The global index of the table's local column 0.
    base: usize,
}

impl FlushBuilder {
    pub(crate) fn new(base: usize) -> Self {
        Self {
            push: Vec::new(),
            pull: Vec::new(),
            base,
        }
    }

    fn pair(&mut self, push: Vec<Coord>, pull: Vec<Coord>) {
        self.push.push(push);
        self.pull.push(pull);
    }

    /// Declare `flushes`, in a table's local columns.
    fn declare(&mut self, flushes: &[Flush]) {
        for flush in flushes {
            let push: Vec<Coord> = flush.push[..flush.len].iter().map(|c| c.coord(self.base)).collect();
            let mut pull = push.clone();
            for &(at, c) in &flush.pull {
                pull[at] = c.coord(self.base);
            }
            self.pair(push, pull);
        }
    }
}

/// A [`Coord`] of a table's in a static declaration.
#[derive(Clone, Copy)]
enum C {
    K(F64),
    Col(usize),
    G(usize, u32),
    P(usize, usize, u32),
    S(&'static [C]),
}

impl C {
    /// The coordinate, its columns offset by `base`.
    fn coord(self, base: usize) -> Coord {
        match self {
            C::K(v) => Const(v),
            C::Col(i) => Col(base + i),
            C::G(i, k) => GCol(base + i, k),
            C::P(i, j, k) => Prod(base + i, base + j, k),
            C::S(cs) => Coord::Sum(cs.iter().map(|c| c.coord(base)).collect()),
        }
    }
}

/// A table's bus interaction, declared in its local columns, `pc` and `fp` columns 0 and 1: the push's tuple, its
/// first `len` slots, and the pull's, which is the push's but in the two slots `pull` sets.
#[derive(Clone, Copy)]
struct Flush {
    push: [C; 1 << verifier::layout::BUS_BITS],
    len: usize,
    pull: [(usize, C); 2],
}

const fn flush(tuple: &[C], pull: [(usize, C); 2]) -> Flush {
    let mut push = [ZERO; 1 << verifier::layout::BUS_BITS];
    let mut i = 0;
    while i < tuple.len() {
        push[i] = tuple[i];
        i += 1;
    }
    Flush {
        push,
        len: tuple.len(),
        pull,
    }
}

/// Fall-through state step: the next pc is `g·pc`, fp unchanged.
const STEP: Flush = flush(&[C::K(SEP_STATE), C::G(0, 1), C::Col(1)], [(1, C::Col(0)); 2]);

/// Explicit state transition (JUMP): push the next state, which the row derives from its columns rather than
/// committing, and pull `(pc, fp)`.
const fn derived(npc: C, nfp: C) -> Flush {
    flush(&[C::K(SEP_STATE), npc, nfp], [(1, C::Col(0)), (2, C::Col(1))])
}

/// Bytecode read at `pc`: the program tuple (opcode and operand slots), with the per-pc execution count, column
/// `count`, advanced by ×g on the push side.
const fn code(count: usize, opcode: F64, operands: &[C]) -> Flush {
    let mut tuple = [ZERO; 1 << verifier::layout::BUS_BITS];
    (tuple[0], tuple[1], tuple[2], tuple[3]) = (C::K(SEP_BYTECODE), C::Col(0), C::G(count, 1), C::K(opcode));
    let mut i = 0;
    while i < operands.len() {
        tuple[OPERAND_SLOT + i] = operands[i];
        i += 1;
    }
    flush(tuple.split_at(OPERAND_SLOT + operands.len()).0, [(2, C::Col(count)); 2])
}

/// The shape every memory interaction shares: the word at `addr` carried as two value coordinates, with the cell's
/// access count advanced by ×g on the push side. A value the row derives rather than commits (an `XOR`/`MUL` result, a
/// `DEREF` store) is passed here as its form: the cell then holds whatever the form says, with no value column and no
/// identity to tie one (§sec:m3).
const fn mem(addr: C, count: usize, [lo, hi]: [C; 2]) -> Flush {
    flush(&[C::K(SEP_MEM), addr, C::G(count, 1), lo, hi], [(2, C::Col(count)); 2])
}

/// A literal zero: an unused bytecode slot, or the high limb of a `K`-valued word, which the bus then forces the
/// stored word's to be.
const ZERO: C = C::K(F64::ZERO);

// ---- fill context ------------------------------------------------------------

/// Inputs a table needs to fill its columns: the trace rows, the final memory
/// image (for read values), `g^0..` for O(1) address lookups, and the program.
pub(crate) struct FillCtx<'a> {
    pub(crate) trace: &'a Trace,
    pub(crate) mem: &'a Memory,
    pub(crate) gpow: &'a [F64],
    pub(crate) program: &'a isa::Program,
}

impl FillCtx<'_> {
    /// Fill `table`'s columns from the trace: `out[i]` is local column `i`'s window of `height` rows, those past the
    /// trace's padding rows ([`Table::padding`]), but for `KECCAK`'s input lanes, which are `q_keccak`'s and have no
    /// window here. `outputs` are the `KECCAK` rows' output lanes ([`keccak_outputs`]).
    pub(crate) fn fill(&self, table: Table, height: usize, out: &mut [&mut [F64]], outputs: &[[u64; STATE_LANES]]) {
        /// Rows per task.
        const CHUNK: usize = 1 << 12;
        /// Rows staged at a time. A row's values go to windows a power of two apart, which share cache sets, so they
        /// are written a column's run at a time rather than a row at a time.
        const STAGE: usize = 64;
        let skip = if table == Table::Keccak {
            keccakt::V_IN..keccakt::V_OUT
        } else {
            0..0
        };
        let padding = table.padding();
        let n_rows = self.trace.row_counts()[table as usize];
        assert!(n_rows <= height, "a table's rows must fit its cube");
        let width = out.len() - skip.len();
        let (head, rest) = out.split_at_mut(skip.start);
        // Every column's chunk for each task, split up front, so that the tasks write disjoint slices.
        let mut tasks: Vec<Vec<&mut [F64]>> = (0..height.div_ceil(CHUNK)).map(|_| Vec::with_capacity(width)).collect();
        for column in head.iter_mut().chain(&mut rest[skip.len()..]) {
            assert_eq!(column.len(), height, "a column's window is the table's height");
            for (task, chunk) in tasks.iter_mut().zip(column.chunks_mut(CHUNK)) {
                task.push(chunk);
            }
        }
        // All the columns in one pass, each row's values computed once.
        parallel::chunks_mut(&mut tasks, 1, |task, chunks| {
            let chunks = &mut chunks[0];
            let mut staged = vec![F64::ZERO; STAGE * width];
            for stage in 0..chunks[0].len().div_ceil(STAGE) {
                let start = stage * STAGE;
                let len = STAGE.min(chunks[0].len() - start);
                for (i, values) in staged.chunks_mut(width).take(len).enumerate() {
                    let row = task * CHUNK + start + i;
                    if row < n_rows {
                        self.row(table, outputs, row, values);
                    } else {
                        let (head, tail) = values.split_at_mut(skip.start);
                        head.copy_from_slice(&padding[..skip.start]);
                        tail.copy_from_slice(&padding[skip.end..]);
                    }
                }
                for (k, column) in chunks.iter_mut().enumerate() {
                    for (slot, values) in column[start..start + len].iter_mut().zip(staged.chunks(width)) {
                        *slot = values[k];
                    }
                }
            }
        });
    }

    /// The values of row `i`'s columns ([`Self::fill`]'s), `outputs` being `KECCAK`'s permutations.
    fn row(&self, table: Table, outputs: &[[u64; STATE_LANES]], i: usize, v: &mut [F64]) {
        let r = &self.trace.rows[table as usize][row_len(table) * i..][..row_len(table)];
        let (pc, fp) = (r[0], r[1]);
        let g = |k: u32| self.gpow[k as usize];
        (v[0], v[1]) = (g(pc), g(fp));
        // The operands are the instruction's bytecode tuple's, which the stacked bytecode holds: they are read back
        // rather than copied into every row (`cpu::trace`).
        for (j, slot) in v[table.operands()].iter_mut().enumerate() {
            *slot = F64(self.program.stacked_bytecode()[(OPERAND_SLOT + j) * self.program.prog.len() + pc as usize]);
        }
        // `KECCAK`'s input lanes, before its counts, have no window here.
        let counts = table.count_columns();
        let skip = if table == Table::Keccak { STATE_LANES } else { 0 };
        for (slot, &k) in v[counts.start - skip..counts.end - skip].iter_mut().zip(&r[2..]) {
            *slot = g(k);
        }
        let word = |cell: u32| self.mem.word(cell as usize);
        let op = &self.program.prog[pc as usize];
        match table {
            Table::Set => {}
            Table::Keccak => {
                use keccakt::*;
                let k = KeccakOp::of(op);
                let (cell, high) = FREE_LIMB[usize::from(k.in_odd)];
                let free = word(k.cell(fp, cell));
                v[FREE] = F64(if high { free.c1 } else { free.c0 });
                for (slot, &w) in v[V_IN..V_IN + STATE_LANES].iter_mut().zip(&outputs[i]) {
                    *slot = F64(w);
                }
            }
            _ => {
                let offsets = match *op {
                    Op::Xor { a, b, c } | Op::Mul { a, b, c } => [a, b, c],
                    Op::Deref { o1, o2, o3, .. } => [o1, o2, o3],
                    Op::Jump { oc, od, of } => [oc, od, of],
                    op => unreachable!("a row's pc {pc} holds {op:?}"),
                };
                // The words read, `(operand, column, both limbs)`: a `K`-valued one commits its low limb alone.
                let reads: &[(usize, usize, bool)] = match table {
                    Table::Deref => &[(0, deref::P, false), (2, deref::V3_LO, true)],
                    Table::Jump => &[(0, jump::V_COND, false), (1, jump::V_PC, false), (2, jump::V_FP, false)],
                    _ => &[(0, arith::VA_LO, true), (1, arith::VB_LO, true)],
                };
                for &(k, col, both) in reads {
                    let w = word(fp + offsets[k]);
                    v[col] = F64(w.c0);
                    if both {
                        v[col + 1] = F64(w.c1);
                    }
                }
                if table == Table::Jump {
                    // The is-nonzero witness `w = c⁻¹` (0 where c = 0) and the taken indicator `b = [c ≠ 0]`. The
                    // conditions lie in K, a subfield, so the inversion runs in K.
                    let cond = v[jump::V_COND];
                    (v[jump::W], v[jump::B]) = (cond.inv(), F64(u64::from(!cond.is_zero())));
                }
            }
        }
    }
}

/// Where a bytecode tuple's operands start: after its tag, pc, read count and opcode ([`code`]).
const OPERAND_SLOT: usize = 4;

// ---- the tables --------------------------------------------------------------

/// The tables in fixed order `[XOR, MUL, SET, DEREF, JUMP, KECCAK]`, the
/// order of `row_counts` / `taus` throughout `cpu`.
pub use verifier::layout::N_TABLES;

/// One instruction table. Indices in [`flushes`](Table::flushes) and
/// [`count_columns`](Table::count_columns) are local to this table.
#[derive(Clone, Copy, PartialEq, Eq)]
pub(crate) enum Table {
    Xor,
    Mul,
    Set,
    Deref,
    Jump,
    Keccak,
}

pub(crate) fn tables() -> [Table; N_TABLES] {
    [
        Table::Xor,
        Table::Mul,
        Table::Set,
        Table::Deref,
        Table::Jump,
        Table::Keccak,
    ]
}

impl Table {
    /// Number of committed columns (local indices `0..n_committed_columns`).
    pub(crate) fn n_committed_columns(self) -> usize {
        TABLE_WIDTHS[self as usize]
    }

    /// Local indices of this table's read-count columns, one contiguous run: the `g^{count}` of each accessed cell
    /// (and the pc), each of which gets its own single-column count bus block.
    pub(crate) fn count_columns(self) -> Range<usize> {
        match self {
            Table::Xor | Table::Mul => arith::RA..arith::RBC + 1,
            Table::Set => set::R..set::RBC + 1,
            Table::Deref => deref::R1..deref::RBC + 1,
            Table::Jump => jump::RC..jump::RBC + 1,
            Table::Keccak => keccakt::R0..keccakt::RBC + 1,
        }
    }

    /// Local indices of this table's operand columns, from 2: its bytecode tuple's operands, in slot order.
    pub(crate) fn operands(self) -> Range<usize> {
        match self {
            Table::Xor | Table::Mul => arith::OA..arith::OC + 1,
            Table::Set => set::O..set::K_HI + 1,
            Table::Deref => deref::O1..deref::FFP + 1,
            Table::Jump => jump::OC..jump::OF + 1,
            Table::Keccak => keccakt::O_M0..keccakt::OUT_ALL + 1,
        }
    }

    /// The row a padding row holds, past the rows the program executed (§sec:e2e-pad): public, and satisfying the
    /// table's constraint. All zeros but for `KECCAK` ([`keccak_padding`]).
    #[inline(never)]
    pub(crate) fn padding(self) -> Vec<F64> {
        match self {
            Table::Keccak => keccak_padding(),
            _ => vec![F64::ZERO; self.n_committed_columns()],
        }
    }

    /// How many identities [`constraint`](Table::constraint) folds, the length of this table's range of `xi`-powers
    /// (§sec:air). None but for `JUMP`'s two: a value that rides the bus as a coordinate needs no identity (§sec:m3).
    pub(crate) fn n_constraints(self) -> usize {
        if self == Table::Jump { 2 } else { 0 }
    }

    /// The table's identities as one degree-2 form over its local columns, identity `i` weighted by `pows[i]`, this
    /// table's [`n_constraints`](Table::n_constraints) `xi`-powers. It vanishes on every valid row (§sec:air).
    pub(crate) fn constraint(self, pows: &[F128]) -> Form {
        assert_eq!(pows.len(), self.n_constraints(), "one power per identity");
        match self {
            Table::Jump => jump_constraint(pows),
            _ => Form::new(self.n_committed_columns()),
        }
    }

    /// Declare the table's bus interactions.
    pub(crate) fn flushes(self, f: &mut FlushBuilder) {
        match self {
            Table::Keccak => f.declare(&KECCAK_FLUSHES),
            _ => f.declare([XOR, MUL, SET, DEREF, JUMP][self as usize]),
        }
    }
}

/// Each table's least log height: 0, but the Keccak reduction's block of steps for `KECCAK`.
pub use verifier::layout::TABLE_LOG_FLOORS;
const _: () = assert!(crate::keccak::MIN_STEPS == 1 << TABLE_LOG_FLOORS[verifier::layout::OP_KECCAK]);

/// What each cell a `KECCAK` row touches is addressed by, in flush order (the four `m` cells, the
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

    /// Cell `c` (in flush order) of a row at frame `fp`.
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

mod arith {
    // Column 0 is `pc`.
    pub const FP: usize = 1;
    pub const OA: usize = 2;
    pub const OB: usize = 3;
    pub const OC: usize = 4;
    // No absolute-address columns: the memory bus carries `fp·o` as a product
    // coordinate (§sec:m3), which is why there is no address binding below.
    // The two read words, two K-limbs each. The third word (the result) is derived.
    pub const VA_LO: usize = 5;
    pub const VA_HI: usize = 6;
    pub const VB_LO: usize = 7;
    pub const VB_HI: usize = 8;
    pub const RA: usize = 9;
    pub const RB: usize = 10;
    pub const RC: usize = 11;
    pub const RBC: usize = 12;
    pub const N: usize = 13;
}

/// `XOR` and `MUL_NATIVE` share their column layout, flushes, and fill; they
/// differ only in the opcode tag and in how the destination cell's value rides
/// the bus (`v_A + v_B` for `XOR`, `v_A·v_B` in `E = K[y]/(y²+x·y+1)` for `MUL`).
/// Neither commits that value and neither has an identity: the destination's
/// memory flush carries the result as a degree-≤2 coordinate over the operand
/// lanes, so bus balance is the assertion (§sec:m3).
const fn arith(opcode: F64, result: [C; 2]) -> [Flush; 5] {
    use arith::*;
    [
        STEP,
        code(RBC, opcode, &[C::Col(OA), C::Col(OB), C::Col(OC), ZERO, ZERO]),
        mem(C::P(FP, OA, 0), RA, [C::Col(VA_LO), C::Col(VA_HI)]),
        mem(C::P(FP, OB, 0), RB, [C::Col(VB_LO), C::Col(VB_HI)]),
        mem(C::P(FP, OC, 0), RC, result),
    ]
}

/// `XOR`'s result is the lane-wise sum.
const XOR: &[Flush] = &arith(
    OP_XOR,
    [
        C::S(&[C::Col(arith::VA_LO), C::Col(arith::VB_LO)]),
        C::S(&[C::Col(arith::VA_HI), C::Col(arith::VB_HI)]),
    ],
);

/// `MUL`'s result is the tower product: `c0 = x0y0 + x1y1` and `c1 = x0y1 + x1y0 + g·x1y1`.
const MUL: &[Flush] = &arith(OP_MUL, MUL_RESULT);
const MUL_RESULT: [C; 2] = {
    use arith::*;
    [
        C::S(&[C::P(VA_LO, VB_LO, 0), C::P(VA_HI, VB_HI, 0)]),
        C::S(&[C::P(VA_LO, VB_HI, 0), C::P(VA_HI, VB_LO, 0), C::P(VA_HI, VB_HI, 1)]),
    ]
};

// ---- SET ---------------------------------------------------------------------

mod set {
    // Column 0 is `pc`.
    pub const FP: usize = 1;
    pub const O: usize = 2;
    // The stored immediate's two K-limbs ride the bytecode's spare slots.
    pub const K_LO: usize = 3;
    pub const K_HI: usize = 4;
    pub const R: usize = 5;
    pub const RBC: usize = 6;
    pub const N: usize = 7;
}

/// The immediate's two limbs occupy bytecode operand slots o2, o3 (as `isa::Program`'s encoding lays out a SET),
/// and are the stored word.
const SET: &[Flush] = {
    use set::*;
    &[
        STEP,
        code(RBC, OP_SET, &[C::Col(O), C::Col(K_LO), C::Col(K_HI), ZERO, ZERO]),
        mem(C::P(FP, O, 0), R, [C::Col(K_LO), C::Col(K_HI)]),
    ]
};

// ---- DEREF -------------------------------------------------------------------

mod deref {
    pub const PC: usize = 0;
    pub const FP: usize = 1;
    pub const O1: usize = 2;
    pub const O2: usize = 3;
    pub const O3: usize = 4;
    pub const FPC: usize = 5;
    pub const FFP: usize = 6;
    // The pointer word is a single K-lane, so its extension limbs are provably
    // zero: they are not committed, and the memory read carries literal zeros
    // there. Being a column is what puts it in K, and the pointer-relative
    // address it forms on the bus, `p·o2`, is a K product for the same reason.
    pub const P: usize = 7;
    // The local cell, a full 128-bit word. The store target is derived from it,
    // the two flags, `pc` and `fp`, so it is no column.
    pub const V3_LO: usize = 8;
    pub const V3_HI: usize = 9;
    pub const R1: usize = 10;
    pub const R2: usize = 11;
    pub const R3: usize = 12;
    pub const RBC: usize = 13;
    pub const N: usize = 14;
}

/// The pointer cell and the local cell are frame-relative; the store target is pointer-relative, so its address is
/// `p·o2`, and its value is the flag-selected source rather than a column: its two K-lanes as forms,
/// `v_2 = (1+f_pc+f_fp)·v_3 + f_pc·(g²·pc) + f_fp·fp` (§sec:tab-deref). The `pc` source is the virtual return target
/// `g²·pc`, a free `×g²` on the product coordinate. Only the low lane takes the two K-valued sources; the high one is
/// the gated local lane alone.
const DEREF: &[Flush] = {
    use deref::*;
    &[
        STEP,
        code(
            RBC,
            OP_DEREF,
            &[C::Col(O1), C::Col(O2), C::Col(O3), C::Col(FPC), C::Col(FFP)],
        ),
        mem(C::P(FP, O1, 0), R1, [C::Col(P), ZERO]),
        mem(
            C::P(P, O2, 0),
            R2,
            [
                C::S(&[
                    C::Col(V3_LO),
                    C::P(FPC, V3_LO, 0),
                    C::P(FFP, V3_LO, 0),
                    C::P(FPC, PC, 2),
                    C::P(FFP, FP, 0),
                ]),
                C::S(&[C::Col(V3_HI), C::P(FPC, V3_HI, 0), C::P(FFP, V3_HI, 0)]),
            ],
        ),
        mem(C::P(FP, O3, 0), R3, [C::Col(V3_LO), C::Col(V3_HI)]),
    ]
};

// ---- JUMP --------------------------------------------------------------------

mod jump {
    pub const PC: usize = 0;
    pub const FP: usize = 1;
    pub const OC: usize = 2;
    pub const OD: usize = 3;
    pub const OF: usize = 4;
    // The condition, destination and frame words are all K-valued, so each is a
    // single lane read with a zero high limb: bus balance forces the stored words
    // into K, exactly as for the DEREF pointer. A guest branches on g-powers,
    // never on an arbitrary word: `assert a != b` takes an inverse hint instead
    // of a branch (§sec:prog-div-ne).
    pub const V_COND: usize = 5;
    pub const V_PC: usize = 6;
    pub const V_FP: usize = 7;
    pub const RC: usize = 8;
    pub const RD: usize = 9;
    pub const RF: usize = 10;
    pub const RBC: usize = 11;
    // Local witness columns (committed, never flushed): the inverse hint `w = c⁻¹`
    // and the taken indicator `b = [c ≠ 0]` it certifies (the `JUMP` table in
    // `doc/leanvm/body/07-instruction-tables.tex`). Both are single K lanes.
    pub const W: usize = 12;
    pub const B: usize = 13;
    pub const N: usize = 14;
}

/// `b = cond·w` and `cond·(b+1) = 0` (§sec:tab-jump), weighted `pows[0]` and `pows[1]`.
///
/// The two relations together force `b = [cond ≠ 0]`: when `cond ≠ 0` the second
/// gives `b = 1` (and the first `w = cond⁻¹`); when `cond = 0` the first gives
/// `b = 0`. The two selections need no identity: the state push carries each as its
/// own degree-2 coordinate (§sec:m3).
///
/// The condition is `K`-valued, so both identities are single-lane. Its memory
/// flush carries literal zeros above the low limb, so a word outside
/// `K` cannot balance the bus; the interpreter rejects one outright.
fn jump_constraint(pows: &[F128]) -> Form {
    use jump::*;
    let mut form = Form::new(N);
    form.coeffs[B] = pows[0];
    form.coeffs[V_COND] = pows[1];
    form.prods = vec![(V_COND, W, pows[0]), (V_COND, B, pows[1])];
    form
}

/// The successor state is derived: `b·d + (b+1)·g·pc` and `b·f + (b+1)·fp`, each degree 2 in K columns, so neither
/// successor is committed. Written out in characteristic 2 as `b·d + b·(g·pc) + g·pc`.
const JUMP: &[Flush] = {
    use jump::*;
    &[
        derived(
            C::S(&[C::P(B, V_PC, 0), C::P(B, PC, 1), C::G(PC, 1)]),
            C::S(&[C::P(B, V_FP, 0), C::P(B, FP, 0), C::Col(FP)]),
        ),
        code(RBC, OP_JUMP, &[C::Col(OC), C::Col(OD), C::Col(OF), ZERO, ZERO]),
        mem(C::P(FP, OC, 0), RC, [C::Col(V_COND), ZERO]),
        mem(C::P(FP, OD, 0), RD, [C::Col(V_PC), ZERO]),
        mem(C::P(FP, OF, 0), RF, [C::Col(V_FP), ZERO]),
    ]
};

// ---- KECCAK ---------------------------------------------------------------------

/// `KECCAK` (“KECCAK” in `doc/leanvm/body/07-instruction-tables.tex`): the Keccak-f\[1600\]
/// permutation of a state in memory. The four `m` cells and `b8` are addressed *independently*
/// at `fp·o_i` (`o_i = g^{m[i]}`), so a caller hashing e.g. `(tweak, pp)` need not copy them into
/// adjacent cells; the four `tail` cells, the four `cap` cells and the thirteen output cells are
/// consecutive runs based at `fp·o_T`, `fp·o_C` and `fp·o_O`. No address is committed: each rides
/// the bus as the product `fp·o_X·g^k` (§sec:m3). The permutation relating output lanes to input
/// lanes carries no table constraint either: it is proven by the Keccak reduction over
/// `q_keccak` (§annex:keccak), which leaves this table with no identity of its own.
///
/// The cells read and written hold the lanes in the layout their flag names
/// ([`verifier::layout::keccak_cell_lanes`]), the flags bound by the bytecode read, so a cell's limb is the
/// form `a + flag·(a + b)` of its lane in either layout, of degree two. The one limb of a read
/// cell that holds no lane is the column `FREE`; written, it is zero. The fifty lanes are
/// value columns, listed in `n_committed_columns` (they need a local index for the flushes), but
/// `cpu` treats them as virtual ([`crate::cpu::keccak_value`]): the input lanes are `q_keccak`'s
/// slots, which hold those words, so their claims route there and the fill leaves them alone,
/// and the output lanes' claims are the Keccak reduction's claim on the output.
pub(crate) mod keccakt {
    use crate::keccak::ROW_CELLS;
    use primitives::hash::STATE_LANES;

    // Column 0 is `pc`.
    pub const FP: usize = 1;
    pub const O_M0: usize = 2; // the g-powers of the eight offset operands, as `KeccakOp` orders them
    pub const IN_ODD: usize = O_M0 + 8; // the layout read …
    pub const OUT_ODD: usize = IN_ODD + 1; // … and the layout written
    pub const OUT_TWO: usize = OUT_ODD + 1; // whether output cell 1 is written …
    pub const OUT_ALL: usize = OUT_TWO + 1; // … and cells 2..13
    pub const FREE: usize = OUT_ALL + 1; // the read limb that holds no lane
    pub const V_IN: usize = FREE + 1; // the 25 input lanes, in lane order …
    pub const V_OUT: usize = V_IN + STATE_LANES; // … and the 25 output lanes
    pub const R0: usize = V_OUT + STATE_LANES; // one read count per cell, in flush order
    pub const RBC: usize = R0 + ROW_CELLS;
    pub const N: usize = RBC + 1;
}

/// `KECCAK`'s operand columns, as [`KeccakOp`] orders them.
const KECCAK_OPERANDS: [C; keccakt::OUT_ALL + 1 - keccakt::O_M0] = {
    let mut ops = [ZERO; keccakt::OUT_ALL + 1 - keccakt::O_M0];
    let mut i = 0;
    while i < ops.len() {
        ops[i] = C::Col(keccakt::O_M0 + i);
        i += 1;
    }
    ops
};

/// The terms of a cell limb holding lane `even` in the even layout and `odd` in the odd one, as `flag` selects:
/// `a + flag·(a + b)`, a missing lane being `missing`, how many there are, and whether they are a sum. When the layouts
/// agree the limb is that column, or zero, alone: one term, no sum.
const fn limb_terms(
    even: Option<usize>,
    odd: Option<usize>,
    values: usize,
    flag: usize,
    missing: Option<usize>,
) -> ([C; 3], usize, bool) {
    let mut terms = [ZERO; 3];
    match (lane_column(even, values, missing), lane_column(odd, values, missing)) {
        (Some(a), Some(b)) if a == b => {
            terms[0] = C::Col(a);
            (terms, 1, false)
        }
        (None, None) => (terms, 1, false),
        (a, b) => {
            let mut n = 0;
            if let Some(a) = a {
                (terms[0], terms[1], n) = (C::Col(a), C::P(flag, a, 0), 2);
            }
            if let Some(b) = b {
                terms[n] = C::P(flag, b, 0);
                n += 1;
            }
            (terms, n, true)
        }
    }
}

/// The value column of `lane`, if any, else `missing`.
const fn lane_column(lane: Option<usize>, values: usize, missing: Option<usize>) -> Option<usize> {
    match lane {
        Some(l) => Some(values + l),
        None => missing,
    }
}

/// Each `KECCAK` cell's sums, in flush order: its low limb's terms, its high limb's and its counter's
/// ([`KECCAK_FLUSHES`]), each with how many there are and whether they are a sum.
static KECCAK_SUMS: [([C; 3], usize, bool); 3 * crate::keccak::ROW_CELLS] = {
    use crate::keccak::STATE_CELLS;
    use keccakt::*;
    let [even, odd] = crate::keccak::CELL_LANES;
    let mut sums = [([ZERO; 3], 0, false); 3 * crate::keccak::ROW_CELLS];
    let mut c = 0;
    while c < sums.len() / 3 {
        let (s, values, flag, free) = if c < STATE_CELLS {
            (c, V_IN, IN_ODD, Some(FREE))
        } else {
            (c - STATE_CELLS, V_OUT, OUT_ODD, None)
        };
        sums[3 * c] = limb_terms(even[s].0, odd[s].0, values, flag, free);
        sums[3 * c + 1] = limb_terms(even[s].1, odd[s].1, values, flag, free);
        // Output cell 0 is always written, cell 1 as `OUT_TWO` says, the rest as `OUT_ALL` says. The counter of a cell
        // written when the column `flag` is 1 is `count·(1 + flag·(g + 1))`: `g·count` at 1, and the pull's `count` at
        // 0, so the pair cancels and touches no cell.
        let count = R0 + c;
        sums[3 * c + 2] = match c {
            _ if c <= STATE_CELLS => ([C::G(count, 1), ZERO, ZERO], 1, false),
            _ => {
                let flag = if c == STATE_CELLS + 1 { OUT_TWO } else { OUT_ALL };
                ([C::Col(count), C::P(flag, count, 1), C::P(flag, count, 0)], 3, true)
            }
        };
        c += 1;
    }
    sums
};

/// `KECCAK`'s bus interactions: its state step and bytecode read, then its thirteen cells read and up to thirteen
/// written. A consecutive cell is a free ×g on the product's g-power.
const KECCAK_FLUSHES: [Flush; 2 + crate::keccak::ROW_CELLS] = {
    use keccakt::*;
    const fn sum(k: usize) -> C {
        match KECCAK_SUMS[k] {
            (terms, _, false) => terms[0],
            (_, n, true) => C::S(KECCAK_SUMS[k].0.split_at(n).0),
        }
    }
    let mut flushes = [STEP; 2 + crate::keccak::ROW_CELLS];
    flushes[1] = code(RBC, OP_KECCAK, &KECCAK_OPERANDS);
    let mut c = 0;
    while c < crate::keccak::ROW_CELLS {
        let (operand, step) = KECCAK_CELLS[c];
        let tuple = [
            C::K(SEP_MEM),
            C::P(FP, O_M0 + operand, step),
            sum(3 * c + 2),
            sum(3 * c),
            sum(3 * c + 1),
        ];
        flushes[2 + c] = flush(&tuple, [(2, C::Col(R0 + c)); 2]);
        c += 1;
    }
    flushes
};

/// The `KECCAK` rows' output lanes, their input lanes permuted again, since a row writes only the output cells its
/// bytecode requests.
pub(crate) fn keccak_outputs(inputs: &[[u64; STATE_LANES]]) -> Vec<[u64; STATE_LANES]> {
    let mut outputs = inputs.to_vec();
    parallel::chunks_mut(&mut outputs, 64, |_, states| primitives::hash::keccak_f_many(states));
    outputs
}

/// Zeros, but for the output lanes: a padding row, like the Keccak reduction's padding steps, permutes zeros, in the
/// even layout.
fn keccak_padding() -> Vec<F64> {
    let mut state = [0; STATE_LANES];
    primitives::hash::keccak_f(&mut state);
    let mut row = vec![F64::ZERO; keccakt::N];
    for (lane, w) in state.into_iter().enumerate() {
        row[keccakt::V_OUT + lane] = F64(w);
    }
    row
}

/// The fewest committed columns of a table's row, `SET`'s: a run of `n` steps commits at least `n` times it, which
/// bounds the steps of a provable run (the interpreter's step limit).
pub(crate) const MIN_COMMITTED_COLUMNS: usize = set::N;
const _: () = assert!(set::N <= arith::N && set::N <= deref::N && set::N <= jump::N && set::N <= keccakt::N);

// Each table's columns are the verifier's, in number, and the KECCAK value lanes and read counts where the verifier's
// spare slots expect them.
const _: () = {
    use verifier::layout::{KECCAK_CNT, KECCAK_IN, KECCAK_OUT, OP_DEREF, OP_JUMP, OP_MUL, OP_SET, OP_XOR};
    assert!(arith::N == TABLE_WIDTHS[OP_XOR] && arith::N == TABLE_WIDTHS[OP_MUL]);
    assert!(set::N == TABLE_WIDTHS[OP_SET] && deref::N == TABLE_WIDTHS[OP_DEREF] && jump::N == TABLE_WIDTHS[OP_JUMP]);
    assert!(keccakt::N == TABLE_WIDTHS[verifier::layout::OP_KECCAK]);
    assert!(keccakt::V_IN == KECCAK_IN && keccakt::V_OUT == KECCAK_OUT && keccakt::R0 == KECCAK_CNT);
    assert!(Table::Xor as usize == OP_XOR && Table::Mul as usize == OP_MUL && Table::Set as usize == OP_SET);
    assert!(Table::Deref as usize == OP_DEREF && Table::Jump as usize == OP_JUMP);
    assert!(Table::Keccak as usize == verifier::layout::OP_KECCAK);
};

#[cfg(test)]
mod tests {
    use super::*;
    use primitives::field::powers;

    /// The hand-unrolled tower product is `E`'s multiplication, lane by lane. `MUL`'s
    /// result coordinate rides the bus, where nothing checks it against the field at
    /// run time, so pin the unrolling here.
    #[test]
    fn unrolled_tower_product_matches_field_product() {
        let x = F128::new(0x0123_4567_89ab_cdef, 0xfeed_face_dead_beef);
        let y = x * x + F128::ONE;
        let mut row = vec![F64::ZERO; arith::N];
        (row[arith::VA_LO], row[arith::VA_HI]) = (F64(x.c0), F64(x.c1));
        (row[arith::VB_LO], row[arith::VB_HI]) = (F64(y.c0), F64(y.c1));
        let got = MUL_RESULT.map(|lane| crate::leaf::coord_at(&lane.coord(0), &row, 0).0);
        assert_eq!(F128::from_limbs(got), x * y);
    }

    /// `JUMP`'s two identities vanish on an honest row, taken or not.
    #[test]
    fn jump_identities_vanish_on_an_honest_row() {
        let pows = powers(F128::new(0x9e37_79b9_7f4a_7c15, 0x1234_5678_9abc_def0), 2);
        // The condition is K-valued (a zero high limb on its read, §sec:tab-jump), so the
        // pair is single-lane: `w = c⁻¹` in K too.
        for cond in [F64::ZERO, F64(0x9e37_79b9_7f4a_7c15)] {
            let mut row = vec![F64::ZERO; jump::N];
            let w = cond.inv();
            row[jump::V_COND] = cond;
            row[jump::W] = w;
            row[jump::B] = if cond.is_zero() { F64::ZERO } else { F64::ONE };
            let row: Vec<F128> = row.into_iter().map(F128::from).collect();
            assert_eq!(jump_constraint(&pows).eval(&row, false), F128::ZERO, "cond = {cond:?}");
        }
    }
}
