//! Lowered intermediate instructions and hints, between the AST and final assembly.

use super::*;

pub(crate) type Off = u32;

/// A `SET` immediate: a field constant, or a function entry address resolved
/// once entry program counters are fixed.
#[derive(Clone, Debug)]
pub(crate) enum KVal {
    /// The stride to the next frame in a reserved loop run.
    FrameSize,
    /// A 128-bit machine-word constant.
    Const(F128),
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
    /// `x·b = c`, `c` already written: the `MUL` back-solves the unwritten `x`.
    Solve {
        x: Off,
        b: Off,
        c: Off,
    },
    /// `dst = src·one`, a copy: `one` is a cell the lowering set to 1 on every path to here.
    Copy {
        src: Off,
        one: Off,
        dst: Off,
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
    /// independently, `tail` (4 cells), `cap` (4 cells) and the output `c` (its first
    /// `out_cells` cells) are consecutive runs; the flags name the layouts read and written.
    Keccak {
        m: [Off; 4],
        tail: Off,
        b8: Off,
        cap: Off,
        c: Off,
        in_odd: bool,
        out_odd: bool,
        out_cells: OutCells,
    },
}

/// A prover hint attached to an instruction. Most are already the runtime's own
/// [`RHint`] and pass straight through; the allocation ones are compiler-side,
/// since their size is only known once every function's frame is laid out.
#[derive(Clone, Debug)]
pub(crate) enum Hint {
    /// Index the next frame address without allocating it again.
    NextFrameAddress,
    /// Reserve the loop run, the final untaken call's frame included.
    AllocLoopFrames {
        ptr: Off,
        callee: String,
        count: LoopCount,
        /// The final, untaken call's frame: only its first `tail` cells (return target, arguments, frame pointer)
        /// are ever written.
        tail: u32,
    },
    /// `m[fp·g^ptr] = g^{fresh base}`: a fresh, disjoint frame for `callee`.
    AllocFrame { ptr: Off, callee: String },
    /// `AllocFrame` for a dispatched call: the frame of `callees[k]`, where
    /// `m[fp·g^sel] = g^k` selects the arm (`FnLower::lower_dispatched_call`).
    AllocArm { ptr: Off, sel: Off, callees: Vec<String> },
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
    /// The cells below this one keep their offsets: the return target, the caller's frame, the arguments, the
    /// return area and, in a loop frame, its own frame pointer. Callers address them.
    pub(crate) keep: u32,
    /// The return area: the callee alone writes it, and every return writes all of it.
    pub(crate) rets: std::ops::Range<u32>,
    /// The frame keeps its layout and its copies (an `addr()` names its cells by offset).
    pub(crate) fixed: bool,
}

impl Lowered {
    /// Whether the caller writes cell `x` before the call: the return target, its frame, the arguments and a loop
    /// frame's own pointer, every kept cell outside the return area.
    pub(crate) fn caller_writes(&self, x: Off) -> bool {
        x < self.keep && !self.rets.contains(&x)
    }
}

/// The jump tables every `match` dispatches through: one cell per arm, holding the
/// pc it jumps to, in `main`'s frame past its own cells. `main`'s frame sits at a
/// fixed address (`fp = g^0`), so a dispatch reads slot `x = g^j` of a table with
/// one `DEREF` ([`LOp::Slot`]). Code at pc 0, before `main` and in its frame, writes
/// every slot once, with one `SET` each.
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
