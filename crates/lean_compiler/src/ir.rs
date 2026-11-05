//! Lowered intermediate instructions and hints, between the AST and final assembly.

use super::*;

pub(crate) type Off = u32;

/// A `SET` immediate: a field constant, or a function entry address resolved
/// once entry program counters are fixed.
#[derive(Clone, Debug)]
pub(crate) enum KVal {
    /// The stride to the next frame in a reserved loop run.
    FrameSize,
    /// A 192-bit machine-word constant. Source literals fill only c0/c1, while
    /// compiler-generated constants may use the full field.
    Const(F192),
    Entry(String),
    /// The halt sentinel pc `g^{B-1}` (last bytecode slot), fixed once the
    /// padded bytecode size `B` is known. `main` jumps here, with `fp = g^0`, to
    /// terminate: the machine halts in the final state `(g^{B-1}, g^0)`, so the
    /// frame pointer is half of what ends the run.
    EndSentinel,
    /// An intra-function jump target: the `i`-th instruction of the function
    /// this `SET` belongs to, resolved to `g^{entry + i}` once entry pcs are
    /// fixed. Emitted with a placeholder by the `if`/`else` lowering and
    /// backpatched (`FnLower::patch_local`).
    Local(u32),
    /// The `i`-th instruction of the named function: a `match` arm's entry, written
    /// into the arm's jump-table slot ([`JumpTables`]).
    At(String, u32),
}

#[derive(Clone, Debug)]
pub(crate) struct LInstr {
    pub(crate) op: LOp,
    /// Source line of the statement that emitted this instruction. Becomes
    /// `Program::src_lines`.
    pub(crate) line: u32,
    /// Prover hints applied (in order) *before* this instruction during witness
    /// generation.
    pub(crate) hints: Vec<Hint>,
}

#[derive(Clone, Debug)]
pub(crate) enum LOp {
    /// A copy into the next loop frame, outside this frame's own allocation.
    MulNextFrame {
        a: Off,
        b: Off,
        c: Off,
    },
    Set {
        o: Off,
        k: KVal,
    },
    Xor {
        a: Off,
        b: Off,
        c: Off,
    },
    Mul {
        a: Off,
        b: Off,
        c: Off,
    },
    Deref {
        o1: Off,
        o2: Off,
        o3: Off,
        mode: DerefMode,
    },
    Jump {
        oc: Off,
        od: Off,
        of: Off,
    },
    /// `dst = m[x·g^(base+first)]`: slot `x = g^j` of the jump table at `first`, a
    /// `DEREF` whose `base`, where the tables start, is fixed at assembly ([`JumpTables`]).
    Slot {
        x: Off,
        first: u32,
        dst: Off,
    },
    /// `KECCAK`: one permutation. The four `m` cells and `b8` are addressed
    /// independently, `tail` (4 cells), `cap` (4 cells) and the output `c` (13 cells)
    /// are consecutive runs; the flags name the layouts read and written.
    Keccak {
        m: [Off; 4],
        tail: Off,
        b8: Off,
        cap: Off,
        c: Off,
        in_odd: bool,
        out_odd: bool,
    },
}

/// A prover hint attached to an instruction. Most are already the runtime's own
/// [`RHint`] and pass straight through; the allocation ones are compiler-side,
/// since their size is only known once every function's frame is laid out.
#[derive(Clone, Debug)]
pub(crate) enum Hint {
    /// Index the next frame address without allocating it again.
    NextFrameAddress,
    /// Reserve the loop run, including the final untaken call's argument frame, of
    /// which only the first `tail` cells (return target, arguments, frame pointer)
    /// are ever written.
    AllocLoopFrames {
        ptr: Off,
        callee: String,
        count: LoopCount,
        tail: u32,
    },
    /// `m[fp·g^ptr] = g^{fresh base}`: a fresh, disjoint frame for `callee`.
    AllocFrame { ptr: Off, callee: String },
    /// `AllocFrame` sized to the **largest** of several callees, a shared frame
    /// for a dispatched call (all `callees` share the arg/return layout; only
    /// their local count, hence frame size, differs). See `FnLower::lower_dispatched_call`.
    AllocFrameMax { ptr: Off, callees: Vec<String> },
    /// `m[fp·g^ptr] = g^{fresh base}`: a fresh, disjoint heap region of `size`
    /// cells (a `HeapBuf(size)`), addressed by g-power offsets from the pointer.
    AllocBuffer { ptr: Off, size: u32 },
    /// `AllocBuffer` with a *runtime* size in the exponent: the cell count is
    /// the g-power exponent of `m[fp·g^size]` (a `HeapBuf(size_expr)`).
    AllocBufferDyn { ptr: Off, size: Off },
    /// A hint that needs nothing from the layout: witness fills, computed
    /// advice, debug prints.
    Resolved(RHint),
}

pub(crate) struct Lowered {
    pub(crate) name: String,
    pub(crate) code: Vec<LInstr>,
    pub(crate) frame_size: u32,
    /// `main` only: its branch blocks, where jump-table writes can go ([`Region`]).
    pub(crate) regions: Vec<Region>,
}

/// A block of `main`'s code that runs at most once and is entered only at its start:
/// the whole body (region 0), a runtime `if` arm, or the entry of a `mul_range` loop
/// that runs at least once. `main` has no back edges (a loop body is a function of its
/// own), so a `SET` at a region's start runs once, and only on paths through it.
#[derive(Clone, Debug)]
pub(crate) struct Region {
    pub(crate) parent: usize,
    /// Code indices `[start, end)`; a child's range lies inside its parent's.
    pub(crate) start: usize,
    pub(crate) end: usize,
}

/// The jump tables every `match` dispatches through: one cell per arm, holding the
/// pc it jumps to, in `main`'s frame past its own cells. `main`'s frame sits at a
/// fixed address (`fp = g^0`), so a dispatch reads slot `x = g^j` of a table with
/// one `DEREF` ([`LOp::Slot`]). `main` writes each slot once, with one `SET`, at the
/// start of the innermost [`Region`] every path to a dispatch through it crosses
/// (`place_tables`), so a table behind a loop or branch of `main` that does not run
/// is never written.
#[derive(Default)]
pub(crate) struct JumpTables {
    /// Each slot's target: an arm's first instruction ([`KVal::At`]) or, for a
    /// dispatched call, a callee's entry ([`KVal::Entry`]).
    pub(crate) slots: Vec<KVal>,
    /// The table of each dispatched call's callees, shared by every call to the same ones.
    pub(crate) shared: HashMap<Vec<String>, usize>,
}

/// A resolved run of consecutive cells (`FnLower::cell_run`): a
/// frame (stack) run, used in place, or a heap slice (the buffer pointer's cell
/// plus the first g-power offset), which a `keccak` operand must bridge through
/// the stack since `KECCAK` addresses only frame cells.
pub(crate) enum CellRun {
    Stack { base: Off, len: u32 },
    Heap { ptr: Off, lo: u32, len: u32 },
}

#[derive(Clone, Debug)]
pub(crate) enum LoopCount {
    Constant(u64),
    Bound { cell: Off, start: u64 },
}
