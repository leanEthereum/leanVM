//! Per-instruction tables (`doc/leanvm/body/07-instruction-tables.tex`). Each opcode is one [`Table`] impl that declares,
//! in one place, its committed columns, how to fill them from the trace, its bus
//! interactions (flushes), the read-count columns that feed the count channel,
//! and its degree-2 constraint. Column indices here are *local* (`0..n_committed_columns`);
//! `cpu`'s schema offsets them to global witness columns.
//!
//! Columns are `K`-valued (`F64`). The pc/fp, operands, counts, opcodes and
//! separators are single `K`-columns; a **machine word** (memory value) is
//! 192-bit (`E = F192`), committed as THREE `K`-lane columns. Nothing a row
//! DERIVES is a column at all: an operand address `fp·o`, an `XOR`/`MUL` result,
//! the `DEREF` store, the `JUMP` successors are each written out as the degree-2
//! bus coordinate that carries them (§sec:m3), which leaves `JUMP`'s is-nonzero
//! indicator as the one identity any table still has. Every identity is `K`-valued,
//! so a relation on machine words is written out lane by lane; after the round a
//! table joins the batch its columns are `E`-valued, which is what
//! `eval_constraint` takes.

use crate::colval::ColVal;
use crate::cpu::{Brow, Drow, Jrow, Op, Srow, Trace};
use crate::leaf::Coord::{self, Col, Const, GCol, Prod};
use primitives::field::{F64, F192, mul_by_g};

// ---- the identities ----------------------------------------------------------
//
// Each is written ONCE, generic over the column type: `F64` in the round a table
// joins the batch, `F192` afterwards (see [`ColVal`]). Products of two `K`
// columns stay 64-bit and an `η`-power multiplies through `mul_e`.
//
// EVERY identity is `K`-valued, like the columns it reads and like the bus
// coordinates (§sec:air). A relation between machine WORDS is therefore written out
// lane by lane, with the tower multiplication unrolled by hand ([`TOWER_LANES`]),
// rather than assembled into one `E` equation. A table's identity slice is then a
// mixed dot product against its `η`-range: in the round a table joins the batch (the
// batch's largest) that is one 64-bit product per identity plus three PMULL for its
// `η`-power, with ONE reduction for the whole slice ([`ColVal::dot`]). One `E`-valued
// identity would instead cost a full `E×E` product against its `η`-power, plus a
// reduction of its own, and the lanes it bundles are the same lane polynomials
// either way.

/// The tower product `x·y` in `E = K[y]/(y³+y+1)` as three lane sums: lane `i` is
/// `Σ x_j·y_k` over `TOWER_LANES[i]`. The five partial sums of §sec:tab-mul fold
/// into `c0 = p0+p3`, `c1 = p1+p3+p4`, `c2 = p2+p4`; written once here because both
/// `MUL`'s result coordinate ([`arith_result`]) and `JUMP`'s inverse identity need
/// the same unrolling.
const TOWER_LANES: [&[(usize, usize)]; 3] = [
    &[(0, 0), (1, 2), (2, 1)],
    &[(0, 1), (1, 0), (1, 2), (2, 1), (2, 2)],
    &[(0, 2), (1, 1), (2, 0), (2, 2)],
];

/// One lane of the tower product, in the columns' own field. Only the test that
/// checks [`TOWER_LANES`] against the field needs it: `MUL`'s result rides the bus
/// as a coordinate ([`arith_result`]), and `JUMP`'s condition is `K`-valued, so no
/// identity assembles a tower product any more.
#[cfg(test)]
fn tower_lane<T: ColVal>(lane: usize, x: [T; 3], y: [T; 3]) -> T {
    TOWER_LANES[lane].iter().fold(T::ZERO, |acc, &(j, k)| acc + x[j] * y[k])
}

/// `JUMP`'s two identities: `b = cond·w` and `cond·(b+1) = 0` (§sec:tab-jump).
///
/// The two relations together force `b = [cond ≠ 0]`: when `cond ≠ 0` the second
/// gives `b = 1` (and the first `w = cond⁻¹`); when `cond = 0` the first gives
/// `b = 0`. The two selections need no identity: the state push carries each as its
/// own degree-2 coordinate (§sec:m3).
///
/// The condition is `K`-valued, so both identities are single-lane. Its memory
/// flush carries literal zeros above the low limb (`memory_k`), so a word outside
/// `K` cannot balance the bus; the interpreter rejects one outright.
fn jump_identity<T: ColVal>(pows: &[F192], cols: &[T], quadratic: bool) -> F192 {
    use jump::*;
    let (b, b1) = if quadratic {
        (T::ZERO, cols[B])
    } else {
        (cols[B], cols[B] + T::ONE)
    };
    T::dot(pows, &[b + cols[V_COND] * cols[W], cols[V_COND] * b1], F192::ZERO)
}

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

// Domain separators (coordinate 0 of every bus tuple): the g-powers g^0, g^1, g^2.
pub(crate) const SEP_STATE: F64 = g_pow(0);
pub(crate) const SEP_MEM: F64 = g_pow(1);
pub(crate) const SEP_BYTECODE: F64 = g_pow(2);

// Opcodes (coordinate 3 of a bytecode tuple).
pub(crate) const OP_XOR: F64 = g_pow(0);
pub(crate) const OP_MUL: F64 = g_pow(1);
pub(crate) const OP_SET: F64 = g_pow(2);
pub(crate) const OP_DEREF: F64 = g_pow(3);
pub(crate) const OP_JUMP: F64 = g_pow(4);
pub(crate) const OP_BLAKE2S: F64 = g_pow(5);

// ---- flush builder -----------------------------------------------------------

/// Collects a table's push/pull bus interactions in *local* column indices. The
/// push/pull of a memory-checked entry differ only by one coordinate carrying the
/// post-increment `g·count` (`GCol`) instead of the pre-increment (`Col`); these
/// helpers encode that pairing so each table reads declaratively.
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

    /// Fall-through state step: the next pc is `g·pc`, fp unchanged.
    pub(crate) fn state_step(&mut self, pc: usize, fp: usize) {
        self.pair(
            vec![Const(SEP_STATE), GCol(pc, 1), Col(fp)],
            vec![Const(SEP_STATE), Col(pc), Col(fp)],
        );
    }

    /// Explicit state transition (JUMP): push the next state, which the row
    /// DERIVES from its columns rather than committing, and pull `(pc, fp)`.
    pub(crate) fn state_derived(&mut self, pc: usize, fp: usize, npc: Coord, nfp: Coord) {
        self.pair(
            vec![Const(SEP_STATE), npc, nfp],
            vec![Const(SEP_STATE), Col(pc), Col(fp)],
        );
    }

    /// Bytecode read at `pc`: the program tuple (opcode + seven operand slots),
    /// with the per-pc execution count advanced by ×g on the push side.
    pub(crate) fn bytecode(&mut self, pc: usize, count: usize, opcode: F64, operands: &[Coord]) {
        let mut push = vec![Const(SEP_BYTECODE), Col(pc), GCol(count, 1), Const(opcode)];
        let mut pull = vec![Const(SEP_BYTECODE), Col(pc), Col(count), Const(opcode)];
        push.extend_from_slice(operands);
        pull.extend_from_slice(operands);
        self.pair(push, pull);
    }

    /// The shape every memory interaction shares: the word at `addr` carried as
    /// three value coordinates, with the cell's access count advanced by ×g on the
    /// push side. A value the row DERIVES rather than commits (an `XOR`/`MUL`
    /// result, a `DEREF` store) is passed here as its form: the cell then holds
    /// whatever the form says, which removes both the value columns and the
    /// identity that used to tie them (§sec:m3).
    pub(crate) fn memory_coords(&mut self, addr: Coord, count: usize, vals: [Coord; 3]) {
        let mut push = vec![Const(SEP_MEM), addr.clone(), GCol(count, 1)];
        let mut pull = vec![Const(SEP_MEM), addr, Col(count)];
        push.extend_from_slice(&vals);
        pull.extend_from_slice(&vals);
        self.pair(push, pull);
    }

    /// Memory access: read the three-limb word at `addr`.
    pub(crate) fn memory(&mut self, addr: Coord, count: usize, val0: usize, val1: usize, val2: usize) {
        self.memory_coords(addr, count, [Col(val0), Col(val1), Col(val2)]);
    }

    /// Memory read of a K-valued word: both higher limbs are literal zero. Used where
    /// the word is carried by a single K column (e.g. the DEREF pointer). Sound
    /// because the bus balances only if the stored value's HI lane is likewise 0.
    pub(crate) fn memory_k(&mut self, addr: Coord, count: usize, val: usize) {
        self.memory_coords(addr, count, [Col(val), Const(F64::ZERO), Const(F64::ZERO)]);
    }

    /// Memory access to a canonical 128-bit word `(lo, hi, 0)`.
    pub(crate) fn memory_128(&mut self, addr: Coord, count: usize, lo: usize, hi: usize) {
        self.memory_coords(addr, count, [Col(lo), Col(hi), Const(F64::ZERO)]);
    }
}

// ---- fill context ------------------------------------------------------------

/// Inputs a table needs to fill its columns: the trace rows, the final memory
/// image (for read values), and `g^0..` for O(1) address/operand lookups.
pub struct FillCtx<'a> {
    pub(crate) trace: &'a Trace,
    pub(crate) mem: &'a [F192],
    pub(crate) gpow: &'a [F64],
    pub(crate) prog: &'a [Op],
    /// This table's height `2^tau`, the length of every window in `out`, and its row
    /// count too: every row is a row the program executed (`cpu::filler`).
    pub(crate) rows: usize,
    /// Which local columns [`Self::col`] / [`Self::cols`] have written. A fill that
    /// misses one would leave the stacked witness holding uninitialized slots, so
    /// [`fill_table`] checks the whole set was covered.
    written: std::sync::atomic::AtomicU64,
}

/// Where one column's values go: its window in the stacked witness, or a private
/// buffer if the column is virtual.
pub type ColumnOut<'a> = &'a mut [F64];

impl<'a> FillCtx<'a> {
    pub(crate) fn new(trace: &'a Trace, mem: &'a [F192], gpow: &'a [F64], prog: &'a [Op], rows: usize) -> Self {
        Self {
            trace,
            mem,
            gpow,
            prog,
            rows,
            written: std::sync::atomic::AtomicU64::new(0),
        }
    }

    fn g_at(&self, i: u32) -> F64 {
        self.gpow[i as usize]
    }

    /// The three frame offsets of an `XOR`/`MUL` row. A row records
    /// only its `(pc, fp)`; the operands are the instruction's, so they are read
    /// back from the bytecode rather than copied into every row (§the trace rows
    /// in `cpu::trace`).
    fn ternary_operands(&self, pc: u32) -> (u32, u32, u32) {
        match self.prog[pc as usize] {
            Op::Xor { a, b, c } | Op::Mul { a, b, c } => (a, b, c),
            op => unreachable!("a three-operand row's pc {pc} holds {op:?}"),
        }
    }

    /// Write local column `at`: `f` over the trace rows, then its pad value to the
    /// end of the window.
    fn col<R: Sync>(&self, out: &mut [ColumnOut], rows: &[R], at: usize, f: impl Fn(&R) -> F64 + Sync) {
        self.cols(out, rows, at, |r| [f(r)]);
    }

    /// Write the `N` local columns at `at..at + N` from one closure per row.
    /// Columns fed by the same read fill together: the three lanes of a 192-bit
    /// memory word are one random access, and splitting them across `N` passes
    /// pays for it `N` times.
    fn cols<const N: usize, R: Sync>(
        &self,
        out: &mut [ColumnOut],
        rows: &[R],
        at: usize,
        f: impl Fn(&R) -> [F64; N] + Sync,
    ) {
        self.cols_at(out, rows.len(), at, |i| f(&rows[i]));
    }

    /// [`Self::cols`] over row indices, for values held in a side buffer rather
    /// than read off the row.
    fn cols_at<const N: usize>(
        &self,
        out: &mut [ColumnOut],
        n_rows: usize,
        at: usize,
        f: impl Fn(usize) -> [F64; N] + Sync,
    ) {
        let n = self.rows;
        let dst: [parallel::SendPtr<F64>; N] = std::array::from_fn(|k| {
            assert_eq!(out[at + k].len(), n, "column {} has the wrong window length", at + k);
            self.written
                .fetch_or(1 << (at + k), std::sync::atomic::Ordering::Relaxed);
            parallel::SendPtr(out[at + k].as_mut_ptr())
        });
        // Every row is a row the program executed: a table's height is its row
        // count (`cpu::filler`), so there is nothing to pad with.
        assert_eq!(n_rows, n, "a table's rows must fill its cube");
        parallel::for_each(n, |i| {
            let v = f(i);
            for (k, p) in dst.iter().enumerate() {
                // SAFETY: distinct `i` write disjoint in-bounds slots of each of the
                // `N` windows, each exactly once, and the dispatch blocks until
                // every write is finished.
                unsafe { p.add(i).write(v[k]) };
            }
        });
    }

    /// The three `K`-lanes of the 192-bit word in memory cell `addr`.
    fn limbs(&self, addr: u32) -> [F64; 3] {
        let w = self.mem[addr as usize];
        [F64(w.c0), F64(w.c1), F64(w.c2)]
    }
}

/// Fill one table's columns and check that every window was written. The stack is
/// allocated uninitialized, so a column the table forgot would be read as
/// indeterminate bytes rather than caught by a length mismatch.
pub(crate) fn fill_table(table: &dyn Table, ctx: &FillCtx, out: &mut [ColumnOut]) {
    table.fill(ctx, out);
    let n = table.n_committed_columns();
    assert!(n <= 64, "the write mask covers at most 64 columns per table");
    let all = if n == 64 { u64::MAX } else { (1u64 << n) - 1 };
    let written = ctx.written.load(std::sync::atomic::Ordering::Relaxed);
    assert_eq!(written, all, "a table left one of its columns unwritten");
}

// ---- the trait ---------------------------------------------------------------

/// One instruction table. Indices in [`flushes`](Table::flushes) and
/// [`count_columns`](Table::count_columns) are local to this table.
pub trait Table: Sync {
    /// Number of committed columns (local indices `0..n_committed_columns`).
    fn n_committed_columns(&self) -> usize;
    /// Local indices of this table's read-count columns: the `g^{count}` values
    /// recording how many times each accessed cell (and the pc) was read. The
    /// framework treats them specially: each gets its own single-column "count"
    /// bus block, and padding rows fill them with `1` (= g^0) instead of `0`.
    fn count_columns(&self) -> &'static [usize];
    /// How many identities [`eval_constraint`](Table::eval_constraint) folds.
    /// Sizes this table's slice of the batch's disjoint `xi`-range (§constraints).
    /// Defaults to none, which is every table but `JUMP`: a relation whose value
    /// rides the bus as a coordinate needs no identity to tie it (§sec:m3).
    fn n_constraints(&self) -> usize {
        0
    }
    /// Evaluate the table's degree-2 constraint at one row, reading column values
    /// by local index from `cols` (e.g. `cols[jump::V_COND]`) and weighting identity
    /// `i` by `pows[i]`, this table's slice of the batch's `xi`-powers. The slice is
    /// is exactly [`n_constraints`](Table::n_constraints) long: an identity indexed
    /// past its end panics rather than silently reaching into the next table's
    /// range. The table sumcheck carries every committed column of a table, in
    /// local order, so `cols` is indexed directly. With `quadratic=false` it returns
    /// `0` on every valid row (§sec:air); `true` selects only the degree-two terms.
    /// The default is the constraint-free case; a table that declares constraints
    /// and forgets to evaluate them trips the assert instead of dropping them.
    fn eval_constraint(&self, pows: &[F192], _cols: &[F192], _quadratic: bool) -> F192 {
        assert!(pows.is_empty(), "a table with constraints must evaluate them");
        F192::ZERO
    }
    /// The same identity over `K`-valued columns, for the round a table joins the
    /// batch, before its columns have been folded into `E` (§sec:air). Both entry
    /// points delegate to one generic definition per table, so they cannot drift.
    fn eval_constraint_k(&self, pows: &[F192], _cols: &[F64], _quadratic: bool) -> F192 {
        assert!(pows.is_empty(), "a table with constraints must evaluate them");
        F192::ZERO
    }
    /// Declare the table's bus interactions.
    fn flushes(&self, f: &mut FlushBuilder);
    /// Fill this table's columns from the trace: `out[i]` is local column `i`'s
    /// window, already at its padded length. Every window must be written in full;
    /// use `FillCtx::col` / `FillCtx::cols`, which append the column's pad value
    /// past the last trace row and record the coverage `fill_table` checks.
    fn fill(&self, ctx: &FillCtx, out: &mut [ColumnOut]);
}

/// The tables in fixed order `[XOR, MUL, SET, DEREF, JUMP, BLAKE2S]`, the
/// order of `row_counts` / `taus` throughout `cpu`.
pub const N_TABLES: usize = 6;

pub fn tables() -> [&'static dyn Table; N_TABLES] {
    [
        &Arith { is_xor: true },
        &Arith { is_xor: false },
        &SetTable,
        &DerefTable,
        &JumpTable,
        &Blake2sTable,
    ]
}

/// Index of the BLAKE2s table in [`tables`].
pub(crate) const BLAKE2S_TABLE: usize = 5;

/// The seven base addresses a `BLAKE2s` row reads: the four message cells, the
/// chaining-value base, the output base (each of those two spans that cell and
/// its successor) and the metadata cell. Recovered from the instruction, not
/// stored per row.
pub(crate) fn blake2s_addresses(prog: &[Op], r: &Brow) -> [u32; 7] {
    match prog[r.pc as usize] {
        Op::Blake2s { ins, cv, out, md } => [
            r.fp + ins[0],
            r.fp + ins[1],
            r.fp + ins[2],
            r.fp + ins[3],
            r.fp + cv,
            r.fp + out,
            r.fp + md,
        ],
        op => unreachable!("a BLAKE2s row's pc {} holds {op:?}", r.pc),
    }
}

/// BLAKE2s value-column LOCAL indices in canonical slot order
/// `[a0..a3, b0..b3, c0..c3, cv0..cv3, md_lo, md_hi]` (matches
/// `hash_flock::SLOTS`). These columns are
/// VIRTUAL (never committed): `q_flock` already holds those words at fixed packed
/// slots, so `cpu` routes their memory-bus evaluation claims straight to `q_flock`
/// (`slot_claims`): the value the bus flushes IS the flock-proven word.
pub const BLAKE2S_VALUE_COLS: [usize; 18] = [
    blake2st::V_M0,
    blake2st::V_M0 + 1,
    blake2st::V_M0 + 2,
    blake2st::V_M0 + 3,
    blake2st::V_M2,
    blake2st::V_M2 + 1,
    blake2st::V_M2 + 2,
    blake2st::V_M2 + 3,
    blake2st::V_OUT0,
    blake2st::V_OUT0 + 1,
    blake2st::V_OUT0 + 2,
    blake2st::V_OUT0 + 3,
    blake2st::V_CV0,
    blake2st::V_CV0 + 1,
    blake2st::V_CV0 + 2,
    blake2st::V_CV0 + 3,
    blake2st::MD0,
    blake2st::MD1,
];
// The eighteen value lanes are laid out contiguously (V_M0..V_M0+17), so they map
// 1:1 onto `hash_flock::SLOTS`.
const _: () = assert!(
    blake2st::V_M2 == blake2st::V_M0 + 4
        && blake2st::V_OUT0 == blake2st::V_M0 + 8
        && blake2st::V_CV0 == blake2st::V_M0 + 12
        && blake2st::MD0 == blake2st::V_M0 + 16
        && blake2st::MD1 == blake2st::V_M0 + 17
);

// ---- XOR / MUL ---------------------------------------------------------------

/// `XOR` and `MUL_NATIVE` share their column layout, flushes, and fill; they
/// differ only in the opcode tag and in how the destination cell's value rides
/// the bus (`v_A + v_B` for `XOR`, `v_A·v_B` in `E = K[y]/(y³+y+1)` for `MUL`).
/// Neither commits that value and neither has an identity: the destination's
/// memory flush carries the result as a degree-≤2 coordinate over the operand
/// lanes, so bus balance IS the assertion (§sec:m3).
struct Arith {
    is_xor: bool,
}

mod arith {
    pub const PC: usize = 0;
    pub const FP: usize = 1;
    pub const OA: usize = 2;
    pub const OB: usize = 3;
    pub const OC: usize = 4;
    // No absolute-address columns: the memory bus carries `fp·o` as a product
    // coordinate (§sec:m3), which is why there is no address binding below.
    // The two read words, each three K-limbs. The third (the result) is DERIVED.
    pub const VA_LO: usize = 5;
    pub const VA_HI: usize = 6;
    pub const VA_TOP: usize = 7;
    pub const VB_LO: usize = 8;
    pub const VB_HI: usize = 9;
    pub const VB_TOP: usize = 10;
    pub const RA: usize = 11;
    pub const RB: usize = 12;
    pub const RC: usize = 13;
    pub const RBC: usize = 14;
    pub const N: usize = 15;
}

/// The result word's three K-lanes as forms over the operand lanes. For `XOR`
/// that is the lane-wise sum; for `MUL` it is the tower product, unrolled through
/// [`TOWER_LANES`].
fn arith_result(is_xor: bool) -> [Coord; 3] {
    use arith::*;
    if is_xor {
        return [
            Coord::Sum(vec![Col(VA_LO), Col(VB_LO)]),
            Coord::Sum(vec![Col(VA_HI), Col(VB_HI)]),
            Coord::Sum(vec![Col(VA_TOP), Col(VB_TOP)]),
        ];
    }
    let (a, b) = ([VA_LO, VA_HI, VA_TOP], [VB_LO, VB_HI, VB_TOP]);
    let lane = |i: usize| Coord::Sum(TOWER_LANES[i].iter().map(|&(j, k)| Prod(a[j], b[k], 0)).collect());
    [lane(0), lane(1), lane(2)]
}

impl Table for Arith {
    fn n_committed_columns(&self) -> usize {
        arith::N
    }
    fn count_columns(&self) -> &'static [usize] {
        use arith::*;
        &[RA, RB, RC, RBC]
    }
    fn flushes(&self, f: &mut FlushBuilder) {
        use arith::*;
        f.state_step(PC, FP);
        f.bytecode(
            PC,
            RBC,
            if self.is_xor { OP_XOR } else { OP_MUL },
            &[Col(OA), Col(OB), Col(OC), Const(F64::ZERO), Const(F64::ZERO)],
        );
        f.memory(Prod(FP, OA, 0), RA, VA_LO, VA_HI, VA_TOP);
        f.memory(Prod(FP, OB, 0), RB, VB_LO, VB_HI, VB_TOP);
        f.memory_coords(Prod(FP, OC, 0), RC, arith_result(self.is_xor));
    }
    fn fill(&self, ctx: &FillCtx, out: &mut [ColumnOut]) {
        use arith::*;
        let rows = if self.is_xor { &ctx.trace.xor } else { &ctx.trace.mul };
        ctx.col(out, rows, PC, |r| ctx.g_at(r.pc));
        ctx.col(out, rows, FP, |r| ctx.g_at(r.fp));
        // The offsets and both operand words come out of ONE bytecode decode: split
        // across passes, the row's instruction is fetched once per pass.
        ctx.cols(out, rows, OA, |r| {
            let (a, b, c) = ctx.ternary_operands(r.pc);
            let (va, vb) = (ctx.limbs(r.fp + a), ctx.limbs(r.fp + b));
            [
                ctx.g_at(a),
                ctx.g_at(b),
                ctx.g_at(c),
                va[0],
                va[1],
                va[2],
                vb[0],
                vb[1],
                vb[2],
            ]
        });
        ctx.cols(out, rows, RA, |r| [r.ra, r.rb, r.rc]);
        ctx.col(out, rows, RBC, |r| r.bytecode_read);
    }
}

// ---- SET ---------------------------------------------------------------------

struct SetTable;

mod set {
    pub const PC: usize = 0;
    pub const FP: usize = 1;
    pub const O: usize = 2;
    // The stored immediate's three K-limbs ride the bytecode's spare slots.
    pub const K_LO: usize = 3;
    pub const K_HI: usize = 4;
    pub const K_TOP: usize = 5;
    pub const R: usize = 6;
    pub const RBC: usize = 7;
    pub const N: usize = 8;
}

impl Table for SetTable {
    fn n_committed_columns(&self) -> usize {
        set::N
    }
    fn count_columns(&self) -> &'static [usize] {
        use set::*;
        &[R, RBC]
    }
    fn flushes(&self, f: &mut FlushBuilder) {
        use set::*;
        f.state_step(PC, FP);
        // The immediate's three limbs occupy bytecode operand slots o2..o4
        // (matching layout::operands for SET).
        f.bytecode(
            PC,
            RBC,
            OP_SET,
            &[Col(O), Col(K_LO), Col(K_HI), Col(K_TOP), Const(F64::ZERO)],
        );
        // The stored constant K is the cell's value.
        f.memory(Prod(FP, O, 0), R, K_LO, K_HI, K_TOP);
    }
    fn fill(&self, ctx: &FillCtx, out: &mut [ColumnOut]) {
        use set::*;
        let rows = &ctx.trace.set;
        // The offset and the stored immediate are the instruction's.
        let imm = |r: &Srow| match ctx.prog[r.pc as usize] {
            Op::Set { o, k } => (o, k),
            op => unreachable!("a SET row's pc {} holds {op:?}", r.pc),
        };
        ctx.col(out, rows, PC, |r| ctx.g_at(r.pc));
        ctx.col(out, rows, FP, |r| ctx.g_at(r.fp));
        ctx.col(out, rows, O, |r| ctx.g_at(imm(r).0));
        ctx.cols(out, rows, K_LO, |r| {
            let k = imm(r).1;
            [F64(k.c0), F64(k.c1), F64(k.c2)]
        });
        ctx.col(out, rows, R, |r| r.r);
        ctx.col(out, rows, RBC, |r| r.bytecode_read);
    }
}

// ---- DEREF -------------------------------------------------------------------

struct DerefTable;

mod deref {
    pub const PC: usize = 0;
    pub const FP: usize = 1;
    pub const O1: usize = 2;
    pub const O2: usize = 3;
    pub const O3: usize = 4;
    pub const FPC: usize = 5;
    pub const FFP: usize = 6;
    // The pointer word is a SINGLE K-lane, so its extension limbs are provably
    // zero: they are NOT committed, and the memory read carries literal zeros
    // there. Being a column is what puts it in K, and the pointer-relative
    // address it forms on the bus, `p·obe`, is a K product for the same reason.
    pub const P: usize = 7;
    // The local cell, a full 192-bit word. The store target is DERIVED from it,
    // the two flags, `pc` and `fp`, so it is no column.
    pub const V3_LO: usize = 8;
    pub const V3_HI: usize = 9;
    pub const V3_TOP: usize = 10;
    pub const R1: usize = 11;
    pub const R2: usize = 12;
    pub const R3: usize = 13;
    pub const RBC: usize = 14;
    pub const N: usize = 15;
}

/// The stored word's three K-lanes as forms:
/// `v_2 = (1+f_pc+f_fp)·v_3 + f_pc·(g²·pc) + f_fp·fp`, the flag-selected source
/// of §sec:tab-deref. The `pc` source is the virtual return target `g²·pc`, a
/// free `×g²` on the product coordinate. Only the low lane takes the two K-valued
/// sources; the upper two are the gated local lanes alone.
fn deref_store() -> [Coord; 3] {
    use deref::*;
    let gated = |v: usize| vec![Col(v), Prod(FPC, v, 0), Prod(FFP, v, 0)];
    let mut lo = gated(V3_LO);
    lo.push(Prod(FPC, PC, 2));
    lo.push(Prod(FFP, FP, 0));
    [Coord::Sum(lo), Coord::Sum(gated(V3_HI)), Coord::Sum(gated(V3_TOP))]
}

impl Table for DerefTable {
    fn n_committed_columns(&self) -> usize {
        deref::N
    }
    fn count_columns(&self) -> &'static [usize] {
        use deref::*;
        &[R1, R2, R3, RBC]
    }
    fn flushes(&self, f: &mut FlushBuilder) {
        use deref::*;
        f.state_step(PC, FP);
        f.bytecode(PC, RBC, OP_DEREF, &[Col(O1), Col(O2), Col(O3), Col(FPC), Col(FFP)]);
        // The pointer cell and the local cell are frame-relative; the store target
        // is pointer-relative, so its address is `p·obe`, and its value is the
        // flag-selected source rather than a column.
        f.memory_k(Prod(FP, O1, 0), R1, P);
        f.memory_coords(Prod(P, O2, 0), R2, deref_store());
        f.memory(Prod(FP, O3, 0), R3, V3_LO, V3_HI, V3_TOP);
    }
    fn fill(&self, ctx: &FillCtx, out: &mut [ColumnOut]) {
        use deref::*;
        let rows = &ctx.trace.deref;
        // Offsets and store mode are the instruction's. Neither the store target's
        // address nor its value is committed.
        let ins = |r: &Drow| match ctx.prog[r.pc as usize] {
            Op::Deref { o1, o2, o3, mode } => (o1, o2, o3, mode),
            op => unreachable!("a DEREF row's pc {} holds {op:?}", r.pc),
        };
        ctx.col(out, rows, PC, |r| ctx.g_at(r.pc));
        ctx.col(out, rows, FP, |r| ctx.g_at(r.fp));
        debug_assert!(
            rows.iter().all(|r| {
                let p = ctx.mem[(r.fp + ins(r).0) as usize];
                p.c1 == 0 && p.c2 == 0
            }),
            "deref pointer must be K-valued"
        );
        // The three offsets, the two mode flags, the pointer lane and the local
        // word all follow from ONE bytecode decode.
        ctx.cols(out, rows, O1, |r| {
            let (o1, o2, o3, mode) = ins(r);
            let v3 = ctx.limbs(r.fp + o3);
            [
                ctx.g_at(o1),
                ctx.g_at(o2),
                ctx.g_at(o3),
                mode.f_pc(),
                mode.f_fp(),
                F64(ctx.mem[(r.fp + o1) as usize].c0),
                v3[0],
                v3[1],
                v3[2],
            ]
        });
        ctx.cols(out, rows, R1, |r| [r.r1, r.r2, r.r3]);
        ctx.col(out, rows, RBC, |r| r.bytecode_read);
    }
}

// ---- JUMP --------------------------------------------------------------------

struct JumpTable;

mod jump {
    pub const PC: usize = 0;
    pub const FP: usize = 1;
    pub const OC: usize = 2;
    pub const OD: usize = 3;
    pub const OF: usize = 4;
    // The condition, destination and frame words are all K-valued, so each is a
    // SINGLE lane read through `memory_k`: bus balance forces the stored words
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

impl Table for JumpTable {
    fn n_committed_columns(&self) -> usize {
        jump::N
    }
    fn count_columns(&self) -> &'static [usize] {
        use jump::*;
        &[RC, RD, RF, RBC]
    }
    fn n_constraints(&self) -> usize {
        2 // the two indicator identities; the selections ride the state push
    }
    fn eval_constraint(&self, pows: &[F192], cols: &[F192], quadratic: bool) -> F192 {
        jump_identity(pows, cols, quadratic)
    }
    fn eval_constraint_k(&self, pows: &[F192], cols: &[F64], quadratic: bool) -> F192 {
        jump_identity(pows, cols, quadratic)
    }
    fn flushes(&self, f: &mut FlushBuilder) {
        use jump::*;
        // The successor state is DERIVED: `b·d + (b+1)·g·pc` and `b·f + (b+1)·fp`,
        // each degree 2 in K columns, so neither successor is committed. Written
        // out in characteristic 2 as `b·d + b·(g·pc) + g·pc`.
        f.state_derived(
            PC,
            FP,
            Coord::Sum(vec![Prod(B, V_PC, 0), Prod(B, PC, 1), GCol(PC, 1)]),
            Coord::Sum(vec![Prod(B, V_FP, 0), Prod(B, FP, 0), Col(FP)]),
        );
        f.bytecode(
            PC,
            RBC,
            OP_JUMP,
            &[Col(OC), Col(OD), Col(OF), Const(F64::ZERO), Const(F64::ZERO)],
        );
        f.memory_k(Prod(FP, OC, 0), RC, V_COND);
        f.memory_k(Prod(FP, OD, 0), RD, V_PC);
        f.memory_k(Prod(FP, OF, 0), RF, V_FP);
    }
    fn fill(&self, ctx: &FillCtx, out: &mut [ColumnOut]) {
        use jump::*;
        let rows = &ctx.trace.jump;
        let ins = |r: &Jrow| match ctx.prog[r.pc as usize] {
            Op::Jump { oc, od, of } => (oc, od, of),
            op => unreachable!("a JUMP row's pc {} holds {op:?}", r.pc),
        };
        let cell = |r: &Jrow, o: u32| ctx.mem[(r.fp + o) as usize];
        let cond = |r: &Jrow| cell(r, ins(r).0);
        ctx.col(out, rows, PC, |r| ctx.g_at(r.pc));
        ctx.col(out, rows, FP, |r| ctx.g_at(r.fp));
        // The three offsets and the three cells they name come out of ONE decode.
        // Those cells are K-valued on every row, taken or not (`cpu::execute`
        // rejects anything else), so each is one lane and the memory flush carries
        // literal zeros above it.
        ctx.cols(out, rows, OC, |r| {
            let (oc, od, of) = ins(r);
            [
                ctx.g_at(oc),
                ctx.g_at(od),
                ctx.g_at(of),
                F64(cell(r, oc).c0),
                F64(cell(r, od).c0),
                F64(cell(r, of).c0),
            ]
        });
        // The is-nonzero witness `w = c⁻¹` (0 where c = 0) for every row, in one
        // batched Montgomery inversion. `prefix[i]` is the
        // running product of the nonzero conditions before row `i`, so `acc` ends
        // as their full product (nonzero, hence invertible). The taken indicator
        // `b = [c ≠ 0]` falls out of the same pass, so it costs no extra decode.
        let (w, b) = {
            let mut acc = F192::ONE;
            let mut prefix: Vec<F192> = Vec::with_capacity(rows.len());
            let mut b = vec![F64::ZERO; rows.len()];
            for (i, r) in rows.iter().enumerate() {
                prefix.push(acc);
                let c = cond(r);
                if !c.is_zero() {
                    acc *= c;
                    b[i] = F64::ONE;
                }
            }
            let mut inv = acc.inv();
            let mut w = vec![F192::ZERO; rows.len()];
            for (i, r) in rows.iter().enumerate().rev() {
                let c = cond(r);
                if !c.is_zero() {
                    w[i] = inv * prefix[i];
                    inv *= c;
                }
            }
            (w, b)
        };
        ctx.cols_at(out, rows.len(), W, |i| [F64(w[i].c0), b[i]]);
        ctx.cols(out, rows, RC, |r| [r.rc, r.rd, r.rf]);
        ctx.col(out, rows, RBC, |r| r.bytecode_read);
    }
}

// ---- BLAKE2s ------------------------------------------------------------------

/// `BLAKE2s` (“BLAKE2s” in `doc/leanvm/body/07-instruction-tables.tex`): one standard compression. The four 128-bit message
/// chunks are addressed *independently* at `fp·o_i` (`o_i = g^{ins[i]}`), each a
/// single cell, with no forced contiguity between chunks, so a caller hashing e.g.
/// `(tweak, pp)` need not copy them into adjacent cells. The chaining value and the
/// 32-byte output each occupy two consecutive cells, based at `fp·o_cv` and
/// `fp·o_c`, and the metadata is one more cell at `fp·o_md`, so the row reads nine
/// cells in all. No address is committed: each rides the bus as the product `fp·o_X`
/// (§sec:m3). The compression relating output words to input words carries no
/// table constraint either: it is proven by flock's R1CS validity via `q_flock`
/// (§hash_flock), which leaves this table with no identity of its own.
///
/// A 128-bit chunk is two flock 64-bit words (lo, hi lanes), so the eighteen
/// memory-borne flock words are eighteen value LANE columns over the nine cells.
/// They are listed in `n_committed_columns` (they need a local index for the
/// flushes and are filled from the trace for the bus), but `cpu` treats them as
/// VIRTUAL (not committed) and routes their bus claims to `q_flock`, which already
/// holds those words (see [`BLAKE2S_VALUE_COLS`]).
struct Blake2sTable;

pub(crate) mod blake2st {
    pub const PC: usize = 0;
    pub const FP: usize = 1;
    pub const O_M0: usize = 2; // operand g-powers (offsets) of the four message cells …
    pub const O_M1: usize = 3;
    pub const O_M2: usize = 4;
    pub const O_M3: usize = 5;
    pub const O_CV: usize = 6; // … the chaining-value base …
    pub const O_OUT: usize = 7; // … the output base …
    pub const O_MD: usize = 8; // … and the metadata cell
    // The eighteen flock lanes: a (lo, hi) pair for each of the nine cells,
    // the four message cells first, then the output pair, the chaining-value
    // pair, and last the metadata cell's counter and flag lanes.
    pub const V_M0: usize = 9; // m0.lo, m0.hi, m1.lo, m1.hi
    pub const V_M2: usize = 13; // m2.lo, m2.hi, m3.lo, m3.hi
    pub const V_OUT0: usize = 17; // out0.lo, out0.hi, out1.lo, out1.hi
    pub const V_CV0: usize = 21; // cv0.lo, cv0.hi, cv1.lo, cv1.hi
    pub const MD0: usize = 25; // metadata: the counter lane …
    pub const MD1: usize = 26; // … and the final ‖ last_node lane
    pub const R_M0: usize = 27; // one read count per cell: the four message cells …
    pub const R_M1: usize = 28;
    pub const R_M2: usize = 29;
    pub const R_M3: usize = 30;
    pub const R_CV0: usize = 31; // … the two chaining-value cells …
    pub const R_CV1: usize = 32;
    pub const R_OUT0: usize = 33; // … the two output cells …
    pub const R_OUT1: usize = 34;
    pub const R_MD: usize = 35; // … and the metadata cell.
    pub const RBC: usize = 36;
    pub const N: usize = 37;
}

impl Table for Blake2sTable {
    fn n_committed_columns(&self) -> usize {
        blake2st::N
    }
    fn count_columns(&self) -> &'static [usize] {
        use blake2st::*;
        &[R_M0, R_M1, R_M2, R_M3, R_CV0, R_CV1, R_OUT0, R_OUT1, R_MD, RBC]
    }
    fn flushes(&self, f: &mut FlushBuilder) {
        use blake2st::*;
        f.state_step(PC, FP);
        f.bytecode(
            PC,
            RBC,
            OP_BLAKE2S,
            &[
                Col(O_M0),
                Col(O_M1),
                Col(O_M2),
                Col(O_M3),
                Col(O_CV),
                Col(O_OUT),
                Col(O_MD),
            ],
        );
        // Nine cell reads: four independent 128-bit message cells, the chaining
        // value's two consecutive cells (ACV, g·ACV), the output's two
        // consecutive cells (AC, g·AC), and the metadata cell. Each carries its
        // chunk's two lanes with a literal-zero top limb (`memory_128`), so the
        // canonical embedding is proof-enforced and the zero limbs are never
        // committed. A consecutive cell is a free ×g on the product's g-power.
        f.memory_128(Prod(FP, O_M0, 0), R_M0, V_M0, V_M0 + 1);
        f.memory_128(Prod(FP, O_M1, 0), R_M1, V_M0 + 2, V_M0 + 3);
        f.memory_128(Prod(FP, O_M2, 0), R_M2, V_M2, V_M2 + 1);
        f.memory_128(Prod(FP, O_M3, 0), R_M3, V_M2 + 2, V_M2 + 3);
        f.memory_128(Prod(FP, O_CV, 0), R_CV0, V_CV0, V_CV0 + 1);
        f.memory_128(Prod(FP, O_CV, 1), R_CV1, V_CV0 + 2, V_CV0 + 3);
        f.memory_128(Prod(FP, O_OUT, 0), R_OUT0, V_OUT0, V_OUT0 + 1);
        f.memory_128(Prod(FP, O_OUT, 1), R_OUT1, V_OUT0 + 2, V_OUT0 + 3);
        // The metadata rides the memory bus like every other operand: the read
        // is what binds flock's counter and flag inputs, so a compile-time
        // counter is pinned by the `SET` immediate that wrote the cell.
        f.memory_128(Prod(FP, O_MD, 0), R_MD, MD0, MD1);
    }
    fn fill(&self, ctx: &FillCtx, out: &mut [ColumnOut]) {
        use blake2st::*;
        let rows = &ctx.trace.blake2s;
        let ad = |r: &Brow| blake2s_addresses(ctx.prog, r);
        ctx.col(out, rows, PC, |r| ctx.g_at(r.pc));
        ctx.col(out, rows, FP, |r| ctx.g_at(r.fp));
        // O_M0..O_MD are the seven base addresses' offsets, from the instruction decode.
        ctx.cols(out, rows, O_M0, |r| ad(r).map(|a| ctx.g_at(a - r.fp)));
        // The eighteen memory-borne flock words are the nine cells' lo/hi lanes:
        // the four message cells, then the cv pair, the output pair and the
        // metadata. A cell's two lanes are one read, so each group of four takes two.
        let word_pair = |c0: u32, c1: u32| {
            let (w0, w1) = (ctx.mem[c0 as usize], ctx.mem[c1 as usize]);
            [F64(w0.c0), F64(w0.c1), F64(w1.c0), F64(w1.c1)]
        };
        ctx.cols(out, rows, V_M0, |r| {
            let a = ad(r);
            word_pair(a[0], a[1])
        });
        ctx.cols(out, rows, V_M2, |r| {
            let a = ad(r);
            word_pair(a[2], a[3])
        });
        ctx.cols(out, rows, V_OUT0, |r| {
            let a = ad(r);
            word_pair(a[5], a[5] + 1)
        });
        ctx.cols(out, rows, V_CV0, |r| {
            let a = ad(r);
            word_pair(a[4], a[4] + 1)
        });
        ctx.cols(out, rows, MD0, |r| {
            let md = ctx.mem[ad(r)[6] as usize];
            [F64(md.c0), F64(md.c1)]
        });
        ctx.cols(out, rows, R_M0, |r| {
            [
                r.ra[0], r.ra[1], r.rb[0], r.rb[1], r.rcv[0], r.rcv[1], r.rc[0], r.rc[1], r.rmd,
            ]
        });
        ctx.col(out, rows, RBC, |r| r.bytecode_read);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use primitives::field::powers;

    const C: F192 = F192::new(0x0123_4567_89ab_cdef, 0xfeed_face_dead_beef, 0x1111_2222_3333_4444);

    /// The hand-unrolled tower product IS `E`'s multiplication, lane by lane. Both
    /// `MUL`'s result coordinate and `JUMP`'s inverse identity are written out from
    /// [`TOWER_LANES`], and neither can be checked against the field at run time (one
    /// is a bus coordinate, the other a `K` identity), so pin the unrolling here.
    #[test]
    fn unrolled_tower_product_matches_field_product() {
        let lanes = |v: F192| [F64(v.c0), F64(v.c1), F64(v.c2)];
        let (x, y) = (C, C * C + F192::ONE);
        let got = [0, 1, 2].map(|i| tower_lane(i, lanes(x), lanes(y)).0);
        assert_eq!(F192::new(got[0], got[1], got[2]), x * y);
    }

    /// `JUMP`'s two identities vanish on an honest row, taken or not, and reject a
    /// wrong indicator or, for a taken jump, an inverse that is not `cond⁻¹`.
    #[test]
    fn jump_identities_bind_indicator_and_inverse() {
        let pows = powers(F192::new(0x9e37_79b9_7f4a_7c15, 0x1234_5678_9abc_def0, 7), 2);
        // The condition is K-valued (`memory_k` on its read, §sec:tab-jump), so the
        // pair is single-lane: `w = c⁻¹` in K too.
        for cond in [F64::ZERO, F64(0x9e37_79b9_7f4a_7c15)] {
            let mut row = vec![F64::ZERO; jump::N];
            let w = if cond.is_zero() {
                F64::ZERO
            } else {
                F64(F192::from(cond).inv().c0)
            };
            row[jump::V_COND] = cond;
            row[jump::W] = w;
            row[jump::B] = if cond.is_zero() { F64::ZERO } else { F64::ONE };
            assert_eq!(jump_identity(&pows, &row, false), F192::ZERO, "cond = {cond:?}");
            // On a zero condition the inverse is unconstrained, being multiplied by
            // zero: what has to be pinned there is the indicator alone.
            let forgeable: &[usize] = if cond.is_zero() {
                &[jump::B]
            } else {
                &[jump::B, jump::W]
            };
            for &col in forgeable {
                let mut forged = row.clone();
                forged[col] += F64::ONE;
                assert_ne!(
                    jump_identity(&pows, &forged, false),
                    F192::ZERO,
                    "column {col}, cond = {cond:?}"
                );
            }
        }
    }
}
