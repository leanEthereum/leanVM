//! Lowering: each function AST is compiled to a sequence of intermediate
//! [`LOp`] instructions (fp-relative offsets, backpatched jump targets).
//!
//! This file holds the walk itself, control flow, instruction emission, and
//! [`Scope`]. The rest is split by the question it answers, because each of the
//! four has an invariant worth stating once rather than rediscovering:
//!
//! - [`mod@eval`] asks what an expression is worth before anything runs. Every
//!   function there takes `&self` and emits nothing, which is what lets a caller
//!   ask without paying for the answer.
//! - [`mod@mem`] asks which cell a name means, and what writing to it costs.
//!   Every index is bounds-checked, in every position, and every store emits: the
//!   machine's write-once memory is what separates an assertion from a definition.
//! - [`mod@call`] is the call boundary. Caller and callee must agree on the
//!   arity, because they place the return area from their own idea of it.
//! - [`mod@builtins`] is the precompile and the hints: the two places a value
//!   arrives without an instruction computing it.
//!
//! [`Scope`] is what a name means HERE, and it reverts at a branch join, so a
//! cell whose `SET` sits inside a branch is never trusted outside it.

use super::*;
use crate::filler::FillerOp;
use lean_vm::cpu::filler::Block;

mod builtins;
mod call;
mod eval;
mod mem;
use call::ret_binding;
use eval::field_pow;
/// Runtime parameter/argument pairs, the `Const`-substituted body, and return arity.
type SpecializedBody<'a> = (Vec<(String, &'a Expr)>, Vec<Stmt>, usize);

/// A value equal to `pointer(base)·g^exp`, or the pure constant `g^exp` when
/// `base` is `None`. Heap-address arithmetic (`ptr·gᵏ`, and constant g-power
/// cursors such as a tweak-table index) is tracked symbolically so a later
/// access folds the whole offset into `DEREF`'s `β` immediate rather than
/// emitting a `SET`+`MUL` per step. A cursor read only as an index thus costs
/// nothing; one used as a value is materialized on demand ([`FnLower::materialize`]).
#[derive(Clone, Copy)]
struct GAddr {
    base: Option<Off>,
    exp: u128,
    /// For a pointer minted by `addr(sb)`, the frame run it names, as
    /// `(first cell, length)`. `base` is then the shared `fp` cell and `exp` the
    /// absolute frame offset, so the run cannot be recovered from those two
    /// alone: carrying it here is what lets [`FnLower::check_heap_bound`] hold a
    /// frame pointer to the same bound a `HeapBuf` pointer gets. `None` for a
    /// heap pointer (bounded through `heap_sizes`) and for a pure g-power.
    run: Option<(Off, u32)>,
}

/// The fixed prefix of every frame: the caller's return pc and frame pointer,
/// then the arguments, then the flattened return area (a `StackBuf(n)` return
/// occupies `n` consecutive cells). One place derives every offset in it, so a
/// caller writing into a callee's frame and the callee reading its own cannot
/// drift apart, and `2 + n_args + n_ret_cells` is not spelled out at each site.
struct Abi;

impl Abi {
    /// Where the caller leaves the return pc and the return frame pointer.
    const RET_PC: Off = 0;
    const RET_FP: Off = 1;
    /// Argument `i`, after the two return slots and the preceding arguments.
    fn arg(shapes: impl Iterator<Item = Shape>, i: usize) -> Off {
        2 + shapes.take(i).map(Shape::cells).sum::<u32>()
    }
    /// Total width of the argument area.
    fn arg_cells(shapes: impl Iterator<Item = Shape>) -> u32 {
        shapes.map(Shape::cells).sum()
    }
    /// Return cell `i` of a callee whose arguments occupy `arg_cells` cells.
    fn ret(arg_cells: u32, i: u32) -> Off {
        2 + arg_cells + i
    }
    /// One past the last cell the CALLER touches, so the first local cell.
    fn end(arg_cells: u32, n_ret_cells: u32) -> Off {
        Self::ret(arg_cells, n_ret_cells)
    }
}

/// Cap on a `β`-folded exponent, inclusive: the operand g-power table is sized to
/// the largest immediate, so beyond this a huge constant index falls back to a
/// materialized pointer instead of inflating that table. The one cap: every site
/// that folds an exponent into `β` measures it against this.
const FOLD_MAX: u128 = 1 << lean_vm::cpu::MIN_LOG_MEM;

/// The two pure operations worth interning. Both are commutative, so operands
/// are stored sorted.
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
enum PureOp {
    Xor,
    Mul,
}

/// How an inlined `@inline` tail-return value binds into the caller
/// ([`FnLower::inline_stack_ret`]): a `StackBuf` hands over its cell run and a
/// folded g-address hands over its symbolic pointer, both aliased at zero
/// copies (so `cvb = obs(cvb, x)` and a fused `fs, x, cur = fs_next(fs, cur)`
/// stay free); a scalar was already copied into its dst cell.
#[derive(Clone, Copy)]
enum RetBind {
    Stack(Off, u32),
    Gaddr(GAddr),
    Scalar,
}

/// What a name is bound to. The kinds are mutually exclusive: a name has exactly
/// one of them, which is why they are one enum and not four maps.
#[derive(Clone, Copy)]
enum Binding {
    Scalar(Off),
    Stack(Off, u32),
    Gaddr(GAddr),
    FConst(F192),
}

/// What one name means: its value binding, plus an OPTIONAL compile-time integer
/// reading of the same expression. The two genuinely coexist (`x = 2` names the
/// field element 2 AND the index 2, while `n = len(A) - 1` has no g-power reading
/// at all), so `int` rides beside `val` rather than being another variant. One
/// entry per name is what makes a rebind atomic.
#[derive(Clone, Copy)]
struct Bound {
    val: Binding,
    int: Option<u128>,
}

/// Everything a runtime branch may not have executed: the name bindings, plus the
/// lazily materialized cells whose `SET` sits wherever it was first needed.
/// [`FnLower::scoped`] restores one of these at the join, so a cell written on one
/// path is never trusted on another.
#[derive(Clone, Default)]
struct Scope {
    names: HashMap<String, Bound>,
    /// The cell holding this function's own `fp`, materialized lazily
    /// ([`FnLower::self_fp`]): local (`if`/`else`) jumps reload the frame
    /// pointer on the taken branch.
    self_fp_off: Option<Off>,
    /// Results of pure operations: `(op, sorted operands)` → the cell holding it.
    ///
    /// Reverting at a branch join (with `const_cells`, below) is the whole
    /// invalidation: a cached cell must dominate every later use, and nothing
    /// clears this at a label target. That is sound only because every backward
    /// edge crosses a function boundary (a loop body is its own `Func` with a
    /// fresh `Scope`) and every `patch_local` target is a forward jump, so a
    /// cached cell's defining instruction always precedes its reuse. A new
    /// backward edge, or a `patch_local` that jumps backwards, would need this
    /// cleared at the target.
    pure_cells: HashMap<(PureOp, Off, Off), Off>,
    /// Every lazily-`SET` constant cell: field value (as bits) → the frame cell
    /// holding it. Cells are write-once and read-many, so one `SET` serves every
    /// use in scope. A `SET` first emitted inside a branch must not be named from
    /// outside it, where the other path leaves the cell unwritten and therefore
    /// prover-chosen, which is why this reverts at a join with the bindings.
    const_cells: HashMap<[u64; 3], Off>,
    /// Two consecutive frame cells holding the standard BLAKE2s IV, emitted
    /// lazily at the first dominating default-IV compression in this
    /// control-flow scope.
    blake2s_iv: Option<Off>,
}

impl Scope {
    fn bound(&self, n: &str) -> Option<Bound> {
        self.names.get(n).copied()
    }
    fn stack(&self, n: &str) -> Option<(Off, u32)> {
        match self.bound(n)?.val {
            Binding::Stack(base, size) => Some((base, size)),
            _ => None,
        }
    }
    /// The compile-time integer reading of `n`, when it has one.
    fn int(&self, n: &str) -> Option<u128> {
        self.bound(n)?.int
    }
    /// Attach the integer reading to the binding just made for `n`.
    fn set_int(&mut self, n: &str, k: u128) {
        if let Some(b) = self.names.get_mut(n) {
            b.int = Some(k);
        }
    }
}

struct FnLower<'a> {
    scope: Scope,
    next: Off,
    /// Physical width of this function's argument area, which is not its
    /// parameter COUNT once a parameter can be a run of cells.
    arg_cells: u32,
    /// Source-level return shapes for this function. Their physical cell widths
    /// determine the reserved return area immediately after the arguments.
    return_shapes: &'a [Shape],
    is_main: bool,
    code: Vec<LInstr>,
    /// Declared size of each `HeapBuf`, keyed by its pointer cell. Shifted
    /// aliases resolve to the same base cell through their gaddr, so a
    /// compile-time index checks against the ORIGINAL buffer's bound.
    heap_sizes: HashMap<Off, u128>,
    /// While inlining an `@inline` call ([`Self::try_inline`]), the destination
    /// cells its tail `return` binds into instead of emitting a return jump.
    /// `None` outside an inlined body.
    inline_ret: Option<Vec<Off>>,
    /// Set by an inlined tail `return`, one [`RetBind`] per returned value,
    /// telling the caller's `let`/tuple how to bind each (alias a `StackBuf` run
    /// or a folded g-address, or take the scalar dst cell). `None` outside an
    /// inlined return.
    inline_stack_ret: Option<Vec<RetBind>>,
    /// Source line of the statement being lowered, for diagnostics and for the
    /// pc-to-line table. Zero for a synthesized statement with no source.
    cur_line: u32,
    /// Hints queued to attach to the next emitted instruction.
    pending: Vec<Hint>,
    /// Active `@inline` expansion stack. Nested inline helpers are allowed,
    /// but direct or indirect recursion would otherwise recurse forever in
    /// the compiler.
    inline_calls: Vec<String>,
    /// Set by [`lower_func`] just before lowering a statement that sits in tail
    /// position; consumed by the next [`Self::stmt`] call, so nested lowering
    /// never inherits it.
    tail_call: bool,
    queue: &'a mut Vec<Func>,
    loop_ctr: &'a mut usize,
    /// Function name for diagnostics and generated-loop handling.
    fn_name: &'a str,
    /// The program's function definitions by name, for `Const`-parameter
    /// specialization at call sites ([`Self::specialize`]).
    defs: &'a HashMap<&'a str, &'a Func>,
    /// Top-level constant arrays, resolved at compile time: `NAME[i]` yields the
    /// element (a field value or an index), `len(NAME)` its length.
    const_arrays: &'a HashMap<&'a str, &'a [F192]>,
}

impl FnLower<'_> {
    /// Abort with a diagnostic naming the source line being lowered. Every
    /// deliberate user-facing error goes through here; a bare `assert!` left in
    /// the file is an internal invariant, i.e. a compiler bug rather than a
    /// program one, and deliberately does NOT get a line.
    fn fail(&self, msg: impl std::fmt::Display) -> ! {
        // The line alone is not the site when the function being lowered is one
        // the author never wrote: `hash_pair__L1` exists because of a `Const`
        // call site, `__loop3` because of a `for` header, and an `@inline` body
        // is lowered through the CALLER, so its statements report the caller's
        // line. Naming the function, and the inline chain when there is one, is
        // what turns "line 19" back into somewhere to look.
        let site = match (self.cur_line, self.fn_name) {
            (0, "main") => String::new(),
            (0, f) => format!("in {f}: "),
            (n, "main") => format!("line {n}: "),
            (n, f) => format!("line {n} in {f}: "),
        };
        match self.inline_calls.as_slice() {
            [] => panic!("{site}{msg}"),
            chain => panic!("{site}{msg} (inlined through {})", chain.join(" -> ")),
        }
    }

    fn fresh(&mut self) -> Off {
        let o = self.next;
        self.next += 1;
        o
    }

    fn emit(&mut self, op: LOp) {
        let hints = std::mem::take(&mut self.pending);
        self.code.push(LInstr {
            op,
            line: self.cur_line,
            hints,
        });
    }

    fn set(&mut self, o: Off, k: KVal) {
        self.emit(LOp::Set { o, k });
    }

    fn set_const(&mut self, o: Off, v: F192) {
        self.set(o, KVal::Const(v));
    }

    fn deref(&mut self, o1: Off, o2: u32, o3: Off, mode: DerefMode) {
        self.emit(LOp::Deref { o1, o2, o3, mode });
    }

    /// A no-op instruction to hang a pending hint on, so it fires exactly here
    /// instead of drifting onto whatever is emitted next (which may sit past a
    /// branch join, or on a path this hint does not belong to).
    fn anchor(&mut self) {
        let o = self.fresh();
        self.set_const(o, F192::ZERO);
    }

    /// A top-level constant name is reserved (`zkDSL.md` §Global constants). A
    /// scalar one enforces that by construction, its value being substituted
    /// textually so a shadowing binding becomes a literal and fails loudly. A
    /// constant ARRAY is carried to lowering instead and resolved without
    /// consulting the scope, so a colliding local would have its
    /// compile-time-indexed reads folded to baked literals, including reads of a
    /// `hint_witness` destination whose asserts would then run on the constant.
    /// Reject the collision rather than pick a winner.
    fn check_not_reserved(&self, name: &str) {
        if self.const_arrays.contains_key(name) {
            self.fail(format!(
                "`{name}` is a top-level constant array, so the name is reserved: rename the local \
             or parameter (zkDSL.md §Global constants)"
            ))
        };
    }

    /// Replace the binding, clearing its previous compile-time integer reading.
    fn rebind(&mut self, name: &str, b: Binding) {
        self.check_not_reserved(name);
        self.scope.names.insert(name.to_string(), Bound { val: b, int: None });
    }

    /// Bind each of `names` to the join cell holding its value, after a `match`
    /// dispatch: whichever arm ran wrote them, so they are plain scalars now.
    fn bind_targets(&mut self, binds: &[(&str, Off)]) {
        for (name, cell) in binds {
            self.rebind(name, Binding::Scalar(*cell));
        }
    }

    /// The cell holding `a op b`, computed only if this scope has not already.
    ///
    /// **Route an operation here only when no later write to its result cell
    /// could be the assertion.** A fresh cell is not sufficient: `assert a != b`
    /// mints one for `x·inv` and writes it again with `SET p = 1`, and THAT write
    /// is the assertion, so sharing the cell would let the next `assert a != b`
    /// skip its `MUL` and assert nothing. A second writer is fine where the value
    /// is already pinned, as in `q = x ** k / w`, whose division writes into the
    /// cell the squaring chain already determined.
    ///
    /// So these stay out: the zero cell an `assert a == b` XORs into, the
    /// `g^{k-1}` a range check multiplies into, `assert a != b`'s product, a
    /// division's back-solve, and `expr_into`'s caller-chosen destination.
    fn pure(&mut self, op: PureOp, a: Off, b: Off) -> Off {
        let key = (op, a.min(b), a.max(b));
        if let Some(&o) = self.scope.pure_cells.get(&key) {
            return o;
        }
        let o = self.fresh();
        match op {
            PureOp::Xor => self.emit(LOp::Xor { a, b, c: o }),
            PureOp::Mul => self.emit(LOp::Mul { a, b, c: o }),
        }
        self.scope.pure_cells.insert(key, o);
        o
    }

    /// The frame cell `arr[idx]` names, bounds-checked, or `None` when `arr` is
    /// not a `StackBuf` and the caller should take its heap path.
    ///
    /// Emits nothing, so each caller keeps its own evaluation order. In
    /// `hb[sb[0]] = f(sb, …)`, the address may read a cell the value writes.
    /// The heap bound lives where the address is formed ([`Self::heap_addr`]).
    fn frame_cell(&mut self, arr: &Expr, idx: &Expr) -> Option<Off> {
        let (base, size) = self.stack_of(arr)?;
        let k = self.const_index(idx);
        if k >= size {
            self.fail(format!("index {k} out of bounds (StackBuf size {size})"))
        };
        Some(base + k)
    }

    /// A frame cell holding `1` (always-taken `JUMP` condition).
    fn one(&mut self) -> Off {
        self.const_cell(F192::ONE)
    }

    /// A frame cell holding `v`, shared by every dominated use in the current
    /// scope: the one cache for every lazily-`SET` constant.
    ///
    /// The `SET` is emitted where the cell is allocated, before anything can name
    /// it, which is what makes every later write a write-once equality against a
    /// bytecode constant rather than a chance to choose the value. It reverts at
    /// a branch join with the rest of [`Scope`], since a `SET` first emitted
    /// inside a branch must not be named outside it, where the other path leaves
    /// the cell unwritten and so prover-chosen. Several call sites hoist
    /// [`Self::one`] above a branch on purpose; the revert is what makes that an
    /// optimization rather than the thing holding the invariant up.
    fn const_cell(&mut self, v: F192) -> Off {
        let key = [v.c0, v.c1, v.c2];
        if let Some(&o) = self.scope.const_cells.get(&key) {
            return o;
        }
        let o = self.fresh();
        self.set_const(o, v);
        self.scope.const_cells.insert(key, o);
        o
    }

    /// A frame cell holding `0`, set lazily once: the source for forwarded zero
    /// words (a `BLAKE2s` padding half), and the destination every `assert a == b`
    /// in this scope XORs into.
    fn zero(&mut self) -> Off {
        self.const_cell(F192::ZERO)
    }

    /// Terminate `main`: jump to the halt sentinel `g^{B-1}` with `fp = g^0`.
    /// The cell holding `1` doubles as the (nonzero) jump condition and the new
    /// frame pointer `g^0`; the dest cell holds `g^{B-1}` (doc §sec:e2e, final state).
    fn halt(&mut self) {
        let one = self.one();
        let dest = self.fresh();
        self.set(dest, KVal::EndSentinel);
        self.emit(LOp::Jump {
            oc: one,
            od: dest,
            of: one,
        });
    }

    /// Emit the fill blocks: per table and per size in `lean_vm::cpu::filler::SIZES`,
    /// that many dummy instructions of the table's opcode, then a `JUMP` back to the
    /// block's own first instruction, in the same frame.
    ///
    /// A block is a cycle and nothing jumps into one: they sit past `main`'s halt
    /// and the interpreter enters them itself once the program has stopped. The
    /// state tuples a traversal pushes are the ones it pulls, so the cycle
    /// balances for any number of traversals (`lean_vm::cpu::filler`).
    ///
    /// The closing jump is always taken (its destination is a g-power, so
    /// nonzero) and reads its destination and frame from cells the interpreter
    /// writes, so a traversal costs the block's rows plus that jump. A dummy uses
    /// one scratch cell as each operand, writing the value already there, so a
    /// block costs one cell whatever its size.
    fn lower_filler_blocks(&mut self) -> Vec<Block> {
        use lean_vm::cpu::filler::{SIZES, frame as fr};

        // No statement wrote these, so they get the "unknown" line rather than
        // whatever `main` happened to end on.
        self.cur_line = 0;

        // A block runs in a frame the interpreter carves out, so the cells it reads are at
        // fixed offsets in *that* frame rather than allocated from this function's
        // counter, and nothing here touches `main`'s frame at all.
        let mut blocks = Vec::new();
        for (table, op) in crate::filler::TABLES {
            for size in SIZES {
                blocks.push(Block {
                    pc: self.code.len() as u32,
                    size: size as u32,
                    table,
                });
                for _ in 0..size {
                    self.emit(match op {
                        FillerOp::Xor => LOp::Xor {
                            a: fr::SCRATCH,
                            b: fr::SCRATCH,
                            c: fr::SCRATCH,
                        },
                        FillerOp::Mul => LOp::Mul {
                            a: fr::SCRATCH,
                            b: fr::SCRATCH,
                            c: fr::SCRATCH,
                        },
                        FillerOp::Set => LOp::Set {
                            o: fr::SCRATCH,
                            k: KVal::Const(F192::ZERO),
                        },
                        FillerOp::Deref => LOp::Deref {
                            o1: fr::PTR,
                            o2: 0,
                            o3: fr::SCRATCH,
                            mode: DerefMode::Cell,
                        },
                        // Its condition is a cell nothing ever writes, so it reads as
                        // zero: the dummy is not taken and falls through to the next
                        // instruction of the block instead of closing the cycle early.
                        FillerOp::Jump => LOp::Jump {
                            oc: fr::ZERO,
                            od: fr::ZERO,
                            of: fr::ZERO,
                        },
                        // Its metadata cell is one no instruction writes, like its
                        // message cells: the interpreter leaves those zero, and a
                        // prover choosing otherwise only picks which compression the
                        // dummy proves, which nothing reads (`lean_vm::cpu::filler`).
                        FillerOp::Blake2s => LOp::Blake2s {
                            ins: [fr::DIGEST + 2, fr::DIGEST + 3, fr::DIGEST + 4, fr::DIGEST + 5],
                            cv: fr::SCRATCH,
                            c: fr::DIGEST,
                            md: fr::ZERO,
                        },
                    });
                }
                // Back to the top, closing the cycle. For the `JUMP` table this is one
                // more row of its own, which is why the solver decomposes that table over
                // `size + 1`.
                self.emit(LOp::Jump {
                    oc: fr::DEST,
                    od: fr::DEST,
                    of: fr::NEXT_FP,
                });
            }
        }
        blocks
    }

    /// `dst = src` (no MOV: multiply by `1`).
    fn copy(&mut self, src: Off, dst: Off) {
        let one = self.one();
        self.emit(LOp::Mul { a: src, b: one, c: dst });
    }

    /// A frame cell holding this function's own `fp` (the g-power element),
    /// materialized lazily once: a taken `JUMP` reloads the frame pointer
    /// from a cell, so local (`if`/`else`) jumps must name it. The ISA has no
    /// fp-read, so bounce it through a fresh 1-cell heap buffer: a
    /// `DEREF`-fp writes it there and a `DEREF`-cell copies it back. In `main`, `fp = g^0 = 1`, which is
    /// the [`Self::one`] cell.
    fn self_fp(&mut self) -> Off {
        if self.is_main {
            return self.one();
        }
        if let Some(o) = self.scope.self_fp_off {
            return o;
        }
        let q = self.fresh();
        self.pending.push(Hint::AllocBuffer { ptr: q, size: 1 });
        self.deref(q, 0, 0, DerefMode::Fp); // m[q] := fp
        let o = self.fresh();
        self.deref(q, 0, o, DerefMode::Cell); // m[fp·g^o] := m[q]
        self.scope.self_fp_off = Some(o);
        o
    }

    /// Backpatch a [`KVal::Local`] `SET` (emitted with a placeholder) to name
    /// the instruction at index `target` of this function's code.
    fn patch_local(&mut self, set_idx: usize, target: usize) {
        match &mut self.code[set_idx].op {
            LOp::Set { k: KVal::Local(t), .. } => *t = target as u32,
            other => unreachable!("patch_local on {other:?}"),
        }
    }

    /// Run `f` with branch-local scope: bindings AND the lazily cached cells
    /// (`one`, `self_fp`, range-check bounds, default BLAKE2s IV) revert
    /// afterwards, since a cell whose `SET` sits inside a conditionally-executed
    /// region must not be trusted outside it.
    fn scoped(&mut self, f: impl FnOnce(&mut Self)) {
        let saved_scope = self.scope.clone();
        f(self);
        // A hint pending at the end of a branch (e.g. a trailing
        // `hint_witness`) must not attach to whatever instruction follows the
        // join, which would fire it unconditionally.
        if !self.pending.is_empty() {
            self.anchor();
        }
        self.scope = saved_scope;
    }

    /// Lower a branch body with branch-local scope ([`Self::scoped`]).
    fn branch(&mut self, body: &[Stmt]) {
        self.scoped(|s| {
            for st in body {
                s.stmt(st);
            }
        });
    }

    /// The cell each multi-return target names, and the names still to bind.
    ///
    /// A plain name takes a fresh cell. A `StackBuf` element uses its existing
    /// cell, so [`Self::call_into`] returns directly into the destination.
    fn ret_targets<'a>(&mut self, targets: &'a [Expr]) -> (Vec<Off>, Vec<(&'a str, Off)>) {
        let mut cells = Vec::with_capacity(targets.len());
        let mut binds = Vec::new();
        for t in targets {
            match t {
                // Only a frame cell can be a return slot. Rejecting here rather
                // than after forming the address keeps a pointer `MUL` out of the
                // program and reports the actual problem: routing a heap target
                // through the heap path lectured about g-powers instead, and told a
                // scalar it was a HeapBuf.
                Expr::Index(arr, idx) => match self.frame_cell(arr, idx) {
                    Some(c) => cells.push(c),
                    None => self.fail(format!(
                        "a multi-value target must be a name or a StackBuf element, got `{t:?}`"
                    )),
                },
                Expr::Var(n) => {
                    let c = self.fresh();
                    cells.push(c);
                    binds.push((n.as_str(), c));
                }
                other => self.fail(format!(
                    "a multi-value target must be a name or a StackBuf element, got `{other:?}`"
                )),
            }
        }
        (cells, binds)
    }

    /// `targets = match(log(x), …)`: dispatch through the trampoline table
    /// ([`Self::lower_match_dispatch`]), arm `j` evaluating the lambda body at
    /// `i = j` into cells every arm shares. Write-once makes that sound, exactly
    /// one arm running, and [`Self::ret_targets`] says which cells those are.
    fn lower_match(&mut self, targets: &[Expr], x: &Expr, arms: &[Expr]) {
        for arm in arms {
            if let Expr::Call(f, _) = arm
                && self
                    .defs
                    .get(f.as_str())
                    .is_some_and(|d| !d.inline && d.return_shapes.iter().any(|s| matches!(s, Shape::StackBuf(_))))
            {
                self.fail("a normal function's StackBuf return cannot cross a match join; bind it with `let`");
            }
        }
        // Calls with identical runtime args share one callee frame and a
        // two-instruction trampoline per arm. Const args select specializations;
        // see `lower_dispatched_call` for the shared argument/return layout checks.
        if arms.iter().all(|a| matches!(a, Expr::Call(..))) {
            let specialized: Vec<(String, Vec<&Expr>)> = arms
                .iter()
                .map(|a| {
                    let Expr::Call(f, cargs) = a else { unreachable!() };
                    self.specialize(f, cargs)
                })
                .collect();
            let rt0 = &specialized[0].1;
            if specialized.iter().all(|(_, rt)| rt == rt0) {
                let callees: Vec<String> = specialized.iter().map(|(c, _)| c.clone()).collect();
                self.lower_dispatched_call(targets, x, &callees, rt0);
                return;
            }
            // Not uniform: fall through (the specializations queued above are
            // re-requested idempotently by `call_into`).
        }
        let xo = self.expr(x);
        let (rcells, binds) = self.ret_targets(targets);
        self.lower_match_dispatch(xo, arms.len(), |s, j| {
            s.scoped(|s| {
                if let [rcell] = rcells.as_slice() {
                    s.expr_into(&arms[j], *rcell);
                } else {
                    let Expr::Call(f, cargs) = &arms[j] else {
                        s.fail(format!(
                            "a multi-target match arm must be a function call, got `{:?}`",
                            arms[j]
                        ));
                    };
                    s.inline_stack_ret = None;
                    s.call_into(f, cargs, &rcells);
                    // An @inline arm's aliased returns materialize into the
                    // shared join cells (a real call wrote them directly).
                    if let Some(binds) = s.inline_stack_ret.take() {
                        for (b, &rc) in binds.iter().zip(&rcells) {
                            match *b {
                                RetBind::Gaddr(ga) => {
                                    let c = s.materialize(ga);
                                    s.copy(c, rc);
                                }
                                RetBind::Stack(base, size) => {
                                    if size != 1 {
                                        s.fail("a multi-cell StackBuf return cannot cross a match join")
                                    }
                                    // `copy` reads the run's first cell, which is where
                                    // the arm's single returned value sits.
                                    let src = base;
                                    s.copy(src, rc);
                                }
                                RetBind::Scalar => {}
                            }
                        }
                    }
                }
            });
        });
        self.bind_targets(&binds);
    }

    /// The two-jump dispatch itself: `d = g^T · x²` names slot `x` of the
    /// two-instruction trampoline table at bytecode base `T`. Returns the index
    /// of the `SET` holding `T`, for the caller to patch once the table's
    /// position is known.
    fn emit_dispatch(&mut self, xo: Off, one: Off, of: Off) -> usize {
        let kcell = self.fresh();
        let kset = self.code.len();
        self.set(kcell, KVal::Local(0)); // patched: table base T
        let x2 = self.pure(PureOp::Mul, xo, xo);
        let d = self.fresh();
        self.emit(LOp::Mul { a: kcell, b: x2, c: d });
        self.emit(LOp::Jump { oc: one, od: d, of });
        kset
    }

    /// The `n` trampoline slots themselves, each `SET c = k(j); JUMP c`.
    /// Returns the table's start; slot `j` has its `SET` at `start + 2*j`.
    fn emit_slots(&mut self, n: usize, one: Off, of: Off, k: impl Fn(usize) -> KVal) -> usize {
        let start = self.code.len();
        for j in 0..n {
            let c = self.fresh();
            self.set(c, k(j));
            self.emit(LOp::Jump { oc: one, od: c, of });
        }
        start
    }

    /// The trampoline dispatch every `match` lowers through: jump to
    /// `d = g^T · x²` (slot `j` of the two-instruction table at bytecode base
    /// `T`), then to `body(j)`'s code; every non-final body exits to the
    /// join. `body` lowers arm `j`, with its own branch-local scope.
    fn lower_match_dispatch(&mut self, xo: Off, n: usize, mut body: impl FnMut(&mut Self, usize)) {
        // Hoisted on purpose: these SETs must dominate the join.
        let sfp = self.self_fp();
        let one = self.one();
        let join = self.fresh();
        let jset = self.code.len();
        self.set(join, KVal::Local(0)); // patched: the join
        // Slot j (two instructions) sits at T + 2j.
        let kset = self.emit_dispatch(xo, one, sfp);
        // The trampoline table.
        self.patch_local(kset, self.code.len());
        let start = self.emit_slots(n, one, sfp, |_| KVal::Local(0));
        // The arm blocks, each exiting to the join (the last falls through).
        for j in 0..n {
            self.patch_local(start + 2 * j, self.code.len());
            body(self, j);
            if j + 1 != n {
                self.emit(LOp::Jump {
                    oc: one,
                    od: join,
                    of: sfp,
                });
            }
        }
        self.patch_local(jset, self.code.len());
    }

    /// Lower `if` / `else`, arranging the blocks so the nonzero `XOR` result jumps to the correct arm.
    fn lower_if(&mut self, eq: bool, lhs: &Expr, rhs: &Expr, then: &[Stmt], els: &[Stmt], force_const: bool) {
        // A folded condition emits no test and no jump, so the taken arm is
        // straight-line code and its bindings persist, unlike a runtime branch's.
        //
        // The fold reads INTEGERS while the runtime lowering below tests a field
        // XOR, and the two disagree whenever a side's readings do. Neither can
        // simply win, so an ambiguous condition is REJECTED and `const(...)` is
        // how the author names the regime (`zkDSL.md`, "`if const(...)`").
        let (a, b) = (self.eval(lhs), self.eval(rhs));
        if let (Some(ai), Some(bi)) = (
            a.int.and_then(|n| u32::try_from(n).ok()),
            b.int.and_then(|n| u32::try_from(n).ok()),
        ) {
            // Checked per SIDE, not by comparing the two verdicts. If each side's
            // own readings agree then integer equality and field equality say the
            // same thing, so a side that disagrees with ITSELF is the whole of the
            // ambiguity. Comparing verdicts instead needs a field reading for both
            // sides, and `try_field_const` has no arm for `-`, `//` or `%`, so
            // `n == 3 - 1` slipped through and folded on the integer reading while
            // `n == 2`, the same condition, was rejected.
            if !force_const {
                for (e, known) in [(lhs, a), (rhs, b)] {
                    if let Some((n, f)) = known.diverging_readings() {
                        self.fail(format!(
                            "`{e:?}` reads as the integer {n} where a condition folds, and as the field \
                             element {:#x}:{:#x} where a value is wanted, so this branch would be decided \
                             by one reading and its body run under the other. Write `if const(...)` to \
                             decide it with integer arithmetic, or spell the operand so the two agree.",
                            f.c1, f.c0
                        ))
                    }
                }
            }
            for st in if (ai == bi) == eq { then } else { els } {
                self.stmt(st);
            }
            return;
        }
        // `const(...)` also decides a condition only the field can read (`GEN ** 3`,
        // or anything past `u32`), which has no integer reading to be ambiguous
        // against. A plain `if` must NOT: folding it would rescope the arm, whose
        // bindings then outlive it.
        if force_const {
            if let (Some(fa), Some(fb)) = (a.field, b.field) {
                for st in if (fa == fb) == eq { then } else { els } {
                    self.stmt(st);
                }
                return;
            }
            self.fail("`if const(...)` asks for a compile-time decision, but this condition is not one: both sides must be compile-time constants")
        }
        // `x != 0` needs no XOR: the cell itself is the JUMP's nonzero test.
        let x = if self.try_lit(rhs) == Some(0) {
            self.expr(lhs)
        } else if self.try_lit(lhs) == Some(0) {
            self.expr(rhs)
        } else {
            let (la, lb) = (self.expr(lhs), self.expr(rhs));
            // x = lhs + rhs: nonzero ⇔ !=
            self.pure(PureOp::Xor, la, lb)
        };
        // Hoisted on purpose: these SETs must dominate the join.
        let sfp = self.self_fp();
        let one = self.one();
        let (a_block, b_block) = if eq { (then, els) } else { (els, then) };
        let bdest = self.fresh();
        let bset = self.code.len();
        self.set(bdest, KVal::Local(0)); // patched: start of B
        self.emit(LOp::Jump {
            oc: x,
            od: bdest,
            of: sfp,
        });
        self.branch(a_block);
        if b_block.is_empty() {
            self.patch_local(bset, self.code.len());
        } else {
            let edest = self.fresh();
            let eset = self.code.len();
            self.set(edest, KVal::Local(0)); // patched: the join
            self.emit(LOp::Jump {
                oc: one,
                od: edest,
                of: sfp,
            });
            self.patch_local(bset, self.code.len());
            self.branch(b_block);
            self.patch_local(eset, self.code.len());
        }
    }

    /// `assert a != b`: `XOR` for `x = a + b`, a hinted `inv = x⁻¹`, then
    /// `MUL p = x·inv` and `SET p = 1`, the write-once conflict being the
    /// assertion (as for `assert a == b`). Sound because `x = 0` forces `p = 0`
    /// whatever the hint, and `p` cannot then be `1`.
    /// A compile-time-equal pair is a hard compile error.
    fn lower_assert_ne(&mut self, a: &Expr, b: &Expr) {
        // Compile-time literals (e.g. after `Const`-arg substitution): a
        // trivially-true pair emits nothing, an equal pair is a hard error.
        // Restricted to plain literals so a field value is never confused with a
        // g-power index (unlike stack-index folding).
        if let (Expr::Lit(x), Expr::Lit(y)) = (a, b) {
            if x == y {
                self.fail(format!("assert a != b: sides are the compile-time-equal literal {x}"))
            };
            return;
        }
        let (la, lb) = (self.expr(a), self.expr(b));
        // x = a + b: nonzero ⇔ a != b
        let x = self.pure(PureOp::Xor, la, lb);
        let inv = self.fresh();
        self.pending.push(Hint::Resolved(RHint::Inverse { value: x, dst: inv }));
        let p = self.fresh();
        self.emit(LOp::Mul { a: x, b: inv, c: p });
        self.set_const(p, F192::ONE);
    }

    /// The frame cell holding `g^{k-1}`, the range-check product target, shared
    /// by every check of that bound.
    ///
    /// An ordinary [`Self::const_cell`], so it is shared with any plain use of
    /// the same constant: at `k = 1` the target is `g^0 = 1`, the very cell
    /// [`Self::one`] hands out, which in `main` is also `self_fp`. Sound, since
    /// the `SET` precedes every use and each later write is the write-once
    /// equality, but a second WRITER on any of those paths would land on all.
    fn bound_cell(&mut self, k: u64) -> Off {
        self.const_cell(g_pow_u128((k - 1) as u128).into())
    }

    /// `assert log x < log GEN ** k`: the 3-cycle range check in the exponent
    /// (`doc/leanvm/body/09-isa-programming.tex` §sec:prog-range-checks). With
    /// `x = g^e`:
    ///
    /// 1. `DEREF` through `x`, so the bus proves `x = g^e` with `e < 2^h`;
    /// 2. `MUL x·y` into the write-once cell holding `g^{k-1}`. The complement
    ///    `y = g^{k-1-e}` needs no hint, the result cell being already written,
    ///    so the runner back-solves the one unknown operand;
    /// 3. `DEREF` through `y`, proving `y = g^f` with `f < 2^h`.
    ///
    /// Then `e + f ≡ k-1 (mod 2^64-1)` with `e, f < 2^h`, and a negative `k-1-e`
    /// wraps to `≈ 2^64 ≫ 2^h`, so `e ≤ k-1` for ANY announced memory size,
    /// provided `k ≤ 2^MIN_LOG_MEM`. Both `DEREF` destinations are unconstrained
    /// touches, back-filled at the end of execution: only the ADDRESS matters, so
    /// nothing reading their results is correct rather than an omission.
    ///
    /// A [`LtBound::Runtime`] bound reaches the same gadget through one extra
    /// `MUL` for `g^{k-1} = Y·g^{-1}`, still back-solved rather than hinted, and
    /// the `k ≤ 2^MIN_LOG_MEM` obligation moves to the program.
    fn lower_assert_lt(&mut self, e: &Expr, bound: &LtBound) {
        let kcell = match bound {
            LtBound::Const(k) => {
                if *k < 1 {
                    self.fail("range-check bound GEN ** 0 names the empty set")
                };
                if *k > 1 << lean_vm::cpu::MIN_LOG_MEM {
                    self.fail(format!(
                        "range-check bound GEN ** {k} exceeds 2^{} (the minimum memory size)",
                        lean_vm::cpu::MIN_LOG_MEM
                    ))
                };
                self.bound_cell(*k)
            }
            LtBound::Runtime(b) => {
                // A bound that folds only after substitution (`GEN ** i` inside an
                // `unroll`) reaches here rather than the arm above, and would then
                // skip the `k <= 2^MIN_LOG_MEM` cap entirely. Reject it: the author
                // wrote a compile-time bound and should get the compile-time check.
                if self.try_field_const(b).is_some() {
                    self.fail(format!(
                        "a compile-time range-check bound must be written as `log GEN ** k` or an \
                     integer, so that the 2^{} cap applies",
                        lean_vm::cpu::MIN_LOG_MEM
                    ))
                };
                let bcell = self.expr(b);
                let inv = self.const_cell(F192::new(primitives::field::G.inv().0, 0, 0));
                let c = self.fresh();
                self.emit(LOp::Mul { a: bcell, b: inv, c });
                c
            }
        };
        let x = self.expr(e);
        let y = self.fresh(); // the complement g^{k-1-e}, back-solved by the MUL
        let t1 = self.fresh(); // DEREF targets: unconstrained touch cells
        let t2 = self.fresh();
        self.deref(x, 0, t1, DerefMode::Cell);
        self.emit(LOp::Mul { a: x, b: y, c: kcell });
        self.deref(y, 0, t2, DerefMode::Cell);
    }

    fn expr(&mut self, e: &Expr) -> Off {
        // A wholly compile-time expression, whatever its shape, is one pooled
        // `SET` ([`Self::const_cell`]): folded here once rather than arm by arm.
        if let Some(v) = self.try_field_const(e) {
            return self.const_cell(v);
        }
        match e {
            Expr::Lit(_) | Expr::Gen | Expr::GPow(_) => unreachable!("a literal folds above"),
            // Not folded above, so its exponent is not a compile-time integer,
            // which `gpow_exp` reports.
            Expr::GenPow(e) => {
                let k = self.gpow_exp(e);
                self.const_cell(g_pow_u128(k).into())
            }
            Expr::Pow(b, e) => self.pow_expr(b, e),
            Expr::Var(v) => match self.scope.bound(v).map(|b| b.val) {
                Some(Binding::Stack(..)) => {
                    self.fail(format!("StackBuf `{v}` used as a scalar; index it (`{v}[k]`) or pass it to blake2s"));
                }
                Some(Binding::Gaddr(ga)) => self.materialize(ga),
                Some(Binding::Scalar(o)) => o,
                _ => {
                    // A `for` body that ASSIGNS to an enclosing name reads it before
                    // it binds it, and the capture set drops every name the body
                    // binds, so the read arrives here with nothing behind it. That is
                    // the loop-carry limitation rather than a typo, and it deserves
                    // the same courtesy the `StackBuf` case already gets: the
                    // tail-recursive helper threads its captures IN, never out, so an
                    // accumulator cannot come back.
                    if self.fn_name.starts_with("__loop") {
                        self.fail(format!(
                            "unbound variable `{v}` in a `for` loop body. If `{v}` names a value from \
                             outside the loop that this body also assigns to, the loop cannot carry it: \
                             the helper threads its captures in, not out. Assign to a new name inside \
                             the body, or carry state through a `HeapBuf`."
                        ))
                    }
                    self.fail(format!("unbound variable `{v}`"))
                }
            },
            Expr::Add(a, b) => {
                if let Some(x) = self.add_identity(a, b) {
                    return self.expr(x);
                }
                let (la, lb) = (self.expr(a), self.expr(b));
                self.pure(PureOp::Xor, la, lb)
            }
            Expr::Mul(a, b) => {
                if let Some(x) = self.mul_identity(a, b) {
                    return self.expr(x);
                }
                let (la, lb) = (self.expr(a), self.expr(b));
                self.pure(PureOp::Mul, la, lb)
            }
            Expr::FieldDiv(a, b) => {
                // q = a / b via the MUL write-once back-solve: emit `a = q * b`
                // with the quotient `q` the unset operand. Witness-gen fills
                // q = a·b⁻¹, and the MUL constraint pins q·b == a (so b == 0 is
                // rejected unless a == 0). One MUL, no hint. The dividend cell
                // `a` must already be written, which `self.expr(a)` guarantees.
                let (la, lb) = (self.expr(a), self.expr(b));
                let q = self.fresh();
                self.emit(LOp::Mul { a: q, b: lb, c: la });
                q
            }
            // A well-formed one folds above, so this is a malformed call.
            Expr::Call(f, _) if f == "f192" => self.fail("f192 needs three literal u64 limbs"),
            // Folded above when it is what it claims to be, so reaching here means
            // it is not: name that, rather than reporting an unknown function.
            Expr::Call(f, args) if f == "const" => {
                if args.len() != 1 {
                    self.fail(format!("const(...) takes one expression, got {}", args.len()))
                };
                self.fail(format!(
                    "const(...) asks for a compile-time integer, and `{:?}` is not one",
                    args[0]
                ))
            }
            Expr::Call(f, args) if f == "addr" => {
                let ga = self.stack_addr(args);
                self.materialize(ga)
            }
            Expr::Call(f, args) if f == "hint_log2_ceil" => {
                // Computed advice: the prover fills g^log2_ceil (base-2 ceil-log) of the value in
                // `bits` (a `nbits`-bit buffer), floored at `floor`. Returned
                // UNCONSTRAINED, so the caller (log2_ceil) re-verifies it. Same
                // "prover computes, circuit checks" pattern as `/`.
                if args.len() != 3 {
    self.fail(format!(
                        "hint_log2_ceil takes three arguments, `(bits, nbits, floor)`, got {}",
                        args.len()
                    ))
};
                let nbits = self.const_index(&args[1]);
                let floor = self.const_index(&args[2]);
                let bits = self.bits_dest(&args[0], nbits, "hint_log2_ceil");
                let dst = self.fresh();
                self.pending.push(Hint::Resolved(RHint::Log2Ceil {
                    bits,
                    dst,
                    nbits,
                    floor,
                }));
                dst
            }
            Expr::Call(f, args) => {
                let d = self.call(f, args, 1)[0];
                self.take_inline_ret_cell(d)
            }
            Expr::HeapBuf(n) => {
                let arr = self.fresh();
                self.heap_sizes.insert(arr, *n as u128);
                // Allocate before the next instruction reads the pointer.
                self.pending.push(Hint::AllocBuffer {
                    ptr: arr,
                    size: *n as u32,
                });
                arr
            }
            Expr::HeapBufDyn(e) => {
                // Evaluate the size first (its cell must be written when the
                // alloc hint fires), then allocate before the pointer is read.
                let size = self.expr(e);
                let arr = self.fresh();
                self.pending.push(Hint::AllocBufferDyn { ptr: arr, size });
                arr
            }
            Expr::StackBuf(_) => {
                self.fail("StackBuf(n) must be bound to a name: `x = StackBuf(n)`")
            }
            // A frame cell IS the answer; a heap cell needs a `DEREF` to read.
            Expr::Index(arr, idx) => {
                if let Some(c) = self.frame_cell(arr, idx) {
                    return c;
                }
                let (ptr, o2) = self.heap_addr(arr, idx);
                let dst = self.fresh();
                self.deref(ptr, o2, dst, DerefMode::Cell);
                dst
            }
            Expr::Sub(..) | Expr::Div(..) | Expr::Mod(..) => {
                self.fail(format!(
                    "`-`, `//`, `%` are compile-time only (field subtraction is `+`); use them in an index, a bound, or a `Const` argument, got `{e:?}`"
                ))
            }
            Expr::Slice(..) => self.fail("a slice is not a scalar; it is only a blake2s operand"),
            Expr::ListLit(..) => self.fail("a list literal must be bound to a name: `x = [a, b]`"),
        }
    }

    /// `base ** e` (non-`GEN` base, compile-time exponent `e`): a fully-constant
    /// base folds to one `SET`; a runtime base is raised by square-and-multiply.
    fn pow_expr(&mut self, b: &Expr, e: &Expr) -> Off {
        let k = self
            .try_const_index(e)
            .unwrap_or_else(|| self.fail(format!("`**` exponent must be a compile-time integer, got `{e:?}`")));
        // Fully constant: evaluate in the field and emit a single `SET`.
        if let Some(bc) = self.try_field_const(b) {
            return self.const_cell(field_pow(bc, k));
        }
        if k == 0 {
            let o = self.fresh();
            self.set_const(o, F192::ONE);
            return o;
        }
        // Runtime base: square-and-multiply over the compile-time exponent bits.
        let base = self.expr(b);
        let hi = 31 - k.leading_zeros(); // top set bit (k >= 1)
        let mut acc = base;
        for bit in (0..hi).rev() {
            acc = self.pure(PureOp::Mul, acc, acc);
            if (k >> bit) & 1 == 1 {
                acc = self.pure(PureOp::Mul, acc, base);
            }
        }
        acc
    }

    /// Evaluate `e` into `dst`, writing constants, arithmetic, heap reads and call results directly.
    /// Writing an existing cell enforces equality under write-once memory.
    fn expr_into(&mut self, e: &Expr, dst: Off) {
        // A wholly compile-time expression (a literal, a constant-array element,
        // constant arithmetic) is one `SET` into `dst`, not a heap read.
        if let Some(v) = self.try_field_const(e) {
            self.set_const(dst, v);
            return;
        }
        match e {
            // Heap read straight into dst (a stack read falls through to the copy).
            // Through the same resolver as every other index, so the frame/heap
            // split is written once: a heap read `DEREF`s straight into `dst`, and a
            // frame read is the cell, copied.
            Expr::Index(arr, idx) => match self.frame_cell(arr, idx) {
                Some(c) => self.copy(c, dst),
                None => {
                    let (ptr, o2) = self.heap_addr(arr, idx);
                    self.deref(ptr, o2, dst, DerefMode::Cell);
                }
            },
            Expr::Pow(b, e) => {
                let v = self.pow_expr(b, e);
                self.copy(v, dst);
            }
            Expr::Add(a, b) => {
                if let Some(x) = self.add_identity(a, b) {
                    self.expr_into(x, dst);
                } else {
                    // Not `pure`: `dst` is the caller's, so it may be written
                    // again and the second write be the assertion. See its doc.
                    let (la, lb) = (self.expr(a), self.expr(b));
                    self.emit(LOp::Xor { a: la, b: lb, c: dst });
                }
            }
            Expr::Mul(a, b) => {
                if let Some(x) = self.mul_identity(a, b) {
                    self.expr_into(x, dst);
                } else {
                    let (la, lb) = (self.expr(a), self.expr(b));
                    self.emit(LOp::Mul { a: la, b: lb, c: dst });
                }
            }
            // A call writes its single return value straight into `dst` (an
            // aliased inline return materializes, then copies into `dst`).
            Expr::Call(f, args) => {
                self.inline_stack_ret = None;
                self.call_into(f, args, &[dst]);
                let v = self.take_inline_ret_cell(dst);
                if v != dst {
                    self.copy(v, dst);
                }
            }
            _ => {
                let v = self.expr(e);
                self.copy(v, dst);
            }
        }
    }

    fn stmt(&mut self, s: &Stmt) {
        let tail = std::mem::take(&mut self.tail_call);
        // Every diagnostic raised while lowering this statement, and every
        // instruction it emits, is attributed to this line.
        self.cur_line = s.line;
        match &s.kind {
            StmtKind::Let(name, e) => match e {
                // `x = StackBuf(n)`: bind a run of `n` consecutive frame cells.
                Expr::StackBuf(n) => {
                    let base = self.alloc_stack(*n as u32);
                    self.rebind(name, Binding::Stack(base, *n as u32));
                }
                // `x = [a, b, …]`: an initialized StackBuf. Allocate the run and
                // write each element in place, through the ordinary stack-store
                // path. Elements are lowered before `name` rebinds, so they may
                // read its old binding (`fs = [fs[1], fs[0]]`).
                Expr::ListLit(es) => {
                    let base = self.alloc_stack(es.len() as u32);
                    for (k, el) in es.iter().enumerate() {
                        self.expr_into(el, base + k as u32);
                    }
                    self.rebind(name, Binding::Stack(base, es.len() as u32));
                }
                // `p = addr(sb)` binds the address itself, so the offset folds
                // into every later access; in any other position `expr` has to
                // materialize it into a cell instead.
                Expr::Call(f, cargs) if f == "addr" => {
                    let ga = self.stack_addr(cargs);
                    self.rebind(name, Binding::Gaddr(ga));
                }
                // `x = other_stackbuf`: a compile-time alias of the same cell
                // run (zero instructions), the chaining-state idiom `st = sn`
                // of an MD loop.
                Expr::Var(v) if self.scope.stack(v).is_some() => {
                    let (base, size) = self.scope.stack(v).expect("guarded above");
                    self.rebind(name, Binding::Stack(base, size));
                }
                _ => {
                    // NOTE: `name`'s old binding stays visible while the RHS is
                    // lowered (the MD-chain idiom `cvb = obs(cvb, x)` reads it);
                    // each terminal path below unbinds/rebinds afterwards.
                    // A compile-time integer binding (a literal, or an expression
                    // that folds: `FOLDBASE[lvl] + j`, `n // 2`, `len(A) - 1`) is
                    // usable as a compile-time index / bound / exponent, and that
                    // role survives the value binding chosen below.
                    let known = self.eval(e);
                    // A symbolic g-address (a constant g-power or a shifted
                    // pointer) or a compile-time field constant stays virtual:
                    // no instruction here, folded / materialized only on demand.
                    if let Some(ga) = known.addr {
                        self.rebind(name, Binding::Gaddr(ga));
                    } else if let Some(c) = known.field {
                        self.rebind(name, Binding::FConst(c));
                    } else if let Some(k) = known.int {
                        // Integer-only fold (`//`, `-`, `%` of constants): a
                        // compile-time value too, and as a scalar it is the field
                        // element with those 128 bits, materialized on demand.
                        self.rebind(name, Binding::FConst(lit_field(k)));
                    } else if let Expr::Call(cf, cargs) = e
                        && self.defs.contains_key(cf.as_str())
                    {
                        // A bare `name = call(...)` of a user function: bind per
                        // the inlined return's RetBind, aliasing its StackBuf run
                        // or folded g-address at zero copies (the `cvb = obs(...)`
                        // / advanced-cursor idiom), else (a plain scalar, or a
                        // real call) bind the dst cell. Embedded calls do NOT
                        // take this path: `expr` materializes theirs
                        // ([`Self::take_inline_ret_cell`]).
                        let o = self.call(cf, cargs, 1)[0];
                        let b = ret_binding(self.inline_stack_ret.take().and_then(|b| b.into_iter().next()), o);
                        self.rebind(name, b);
                    } else {
                        let o = self.expr(e);
                        self.rebind(name, Binding::Scalar(o));
                    }
                    // The integer reading of the SAME expression, if it has one,
                    // rides alongside whichever value binding was chosen above.
                    // It is attached after, because a rebind clears it, and the
                    // RHS above still had to see `name`'s old reading.
                    if let Some(k) = known.int {
                        self.scope.set_int(name, k);
                    }
                }
            },
            StmtKind::LetTuple(names, f, args) => {
                let dsts = self.call(f, args, names.len());
                // Each returned value binds per its RetBind (alias a StackBuf run
                // or folded g-address, else take the scalar dst cell); a real call
                // leaves the field None, so every name binds its scalar dst.
                let binds = self.inline_stack_ret.take();
                for (i, (n, d)) in names.iter().zip(&dsts).enumerate() {
                    let b = ret_binding(binds.as_ref().and_then(|b| b.get(i).copied()), *d);
                    self.rebind(n, b);
                }
            }
            // `a + b` into the frame's zero cell: the double write IS the
            // assertion, so the `SET .. = 0` a fresh destination needed is gone
            // and no cell is burned. Not through `pure`, for the same reason:
            // sharing this cell would drop the assertion.
            StmtKind::AssertEq(a, b) => {
                let (la, lb) = (self.expr(a), self.expr(b));
                let z = self.zero();
                self.emit(LOp::Xor { a: la, b: lb, c: z });
            }
            StmtKind::AssertNe(a, b) => self.lower_assert_ne(a, b),
            StmtKind::AssertLt(e, bound) => self.lower_assert_lt(e, bound),
            StmtKind::HintWitness { dest, name } => self.lower_hint_witness(dest, name),
            // One hinted value into one fresh cell, bound to `name`. The run form
            // names its destination's physical cells, and a scalar's cell is never
            // a store target at all, being reachable only through a name.
            StmtKind::LetHintWitness { name, stream } => {
                let dst = self.fresh();
                self.pending.push(Hint::Resolved(RHint::WitnessStack {
                    name: stream.clone(),
                    base: dst,
                    len: 1,
                }));
                self.rebind(name, Binding::Scalar(dst));
            }
            StmtKind::Print { label, value } => {
                // Prover-side debug print: evaluate the value into a cell, hang
                // a Print hint on a no-op anchor so it fires exactly here (and
                // only on this path), at witness generation. No constraints.
                let cell = self.expr(value);
                self.pending.push(Hint::Resolved(RHint::Print {
                    label: label.clone(),
                    cell,
                }));
                self.anchor();
            }
            StmtKind::If {
                eq,
                lhs,
                rhs,
                then,
                els,
                force_const,
            } => self.lower_if(*eq, lhs, rhs, then, els, *force_const),
            StmtKind::Match { targets, x, arms } => self.lower_match(targets, x, arms),
            StmtKind::Call(f, args) => {
                if !self.lower_builtin(f, args) {
                    self.call(f, args, 0);
                }
            }
            StmtKind::Store(arr, idx, val) => {
                // A frame write places the value in the cell; a heap write is the
                // `DEREF` asserting `m[arr·idx] == val` (write-once). The VALUE is
                // lowered first on the heap path, since the address may read a cell
                // the value writes (`hb[sb[0]] = f(sb, …)`), and Python's own
                // evaluation order for `a[i] = v` is the same.
                if let Some(c) = self.frame_cell(arr, idx) {
                    self.expr_into(val, c);
                } else {
                    let v = self.expr(val);
                    let (ptr, o2) = self.heap_addr(arr, idx);
                    self.deref(ptr, o2, v, DerefMode::Cell);
                }
            }
            StmtKind::Return(es) => self.lower_return(es),
            StmtKind::CallIfNe(lhs, rhs, callee, args) => {
                // A conditional call: the frame setup runs either way, and the
                // `JUMP`'s nonzero test decides whether the callee is entered,
                // so the not-taken path continues straight after it. In tail
                // position the callee inherits THIS frame's `retpc`/`retfp`, so
                // a `mul_range` loop builds no unwind chain: only the final
                // iteration returns, straight to the loop's original caller.
                let (la, lb) = (self.expr(lhs), self.expr(rhs));
                // x = lhs + rhs; x != 0 ⇔ lhs != rhs
                let x = self.pure(PureOp::Xor, la, lb);
                self.lower_call(callee, args, Some(x), &[], tail);
            }
            StmtKind::For { var, lo, hi, body } => self.lower_for(var, *lo, hi, body),
            // Compile-time unrolling: emit the body per integer, the counter
            // substituted as its literal. Every copy executes (this is
            // straight-line code, not a branch), so bindings simply rebind (a
            // fresh binding per iteration) and lazy caches persist.
            StmtKind::Unroll { var, lo, hi, body } => {
                let bound = |s: &Self, e: &Expr| {
                    s.try_const_index(e).unwrap_or_else(|| {
                        self.fail(format!("unroll bounds must be compile-time integers, got `{e:?}`"))
                    })
                };
                let (lo, hi) = (bound(self, lo), bound(self, hi));
                if lo > hi {
                    self.fail(format!("unroll(a, b) needs a <= b, got ({lo}, {hi})"))
                };
                for j in lo..hi {
                    for s in subst_stmts(body, var, &Expr::Lit(j as u128)) {
                        self.stmt(&s);
                    }
                }
            }
        }
    }

    /// `for i in mul_range(GEN**lo, GEN**hi)` → a single tail-recursive helper, with the
    /// exit test folded into the recursion's condition (no separate branch, no
    /// is-zero gadget):
    /// ```text
    /// loop(i):
    ///     <body>
    ///     j = i·g
    ///     if j != g^hi: loop(j)   // JUMP's nonzero test on (j − g^hi)
    ///     return
    /// caller: if lo != hi: loop(g^lo)   // resolved at compile time
    /// ```
    /// Free variables of the body that are bound in the enclosing scope are
    /// captured by value as extra helper parameters (e.g. a `HeapBuf` pointer
    /// threaded through the loop).
    fn lower_for(&mut self, var: &str, lo: u64, hi: &ForBound, body: &[Stmt]) {
        let id = *self.loop_ctr;
        *self.loop_ctr += 1;
        let loop_name = format!("__loop{id}");
        if std::env::var("DBG_LOOPS").is_ok() {
            let bound = match hi {
                ForBound::Const(h) => format!("g^{lo}..g^{h}"),
                ForBound::Runtime(e) => format!("g^{lo}..{e:?}"),
            };
            eprintln!("DBG_LOOPS {loop_name} in {} for {var} in {bound}", self.fn_name);
        }
        // A runtime stop bound is evaluated once here and threaded through the
        // helper as an extra leading parameter (the exit test compares the
        // advanced counter against it each iteration).
        let bound_var = format!("__bound{id}");
        let (exit, entry_bound): (Expr, Expr) = match hi {
            ForBound::Const(hi) => (Expr::GPow(*hi as u128), Expr::GPow(*hi as u128)),
            ForBound::Runtime(e) => (Expr::Var(bound_var.clone()), e.clone()),
        };

        // Determine captures: referenced − locally-bound − the counter, kept if
        // they exist in the enclosing scope (deterministic order).
        let mut referenced = Vec::new();
        let mut bound = std::collections::HashSet::new();
        bound.insert(var);
        for s in body {
            free_vars_stmt(s, &mut referenced, &mut bound);
        }
        // Everything the body binds ANYWHERE, branch-local or not. `bound` above
        // is scoped, which is what makes the capture set right; this flat one
        // only answers "does the body have an `r` of its own?", which is what the
        // StackBuf rejection below needs: a body that merely SHADOWS an enclosing
        // `StackBuf` never touches it, so rejecting it names a capture that is
        // not happening.
        let mut shadowed = std::collections::HashSet::new();
        binds_anywhere(body, &mut shadowed);
        let mut captures = Vec::new();
        let mut seen = std::collections::HashSet::new();
        for r in &referenced {
            if bound.contains(r) {
                continue;
            }
            // A StackBuf is a run of cells, not a single scalar arg, and the
            // tail-recursive loop helper can't thread one across iterations, so a
            // StackBuf from the enclosing scope can't be captured. Reject with a
            // clear error (not the misleading "unbound variable" the capture drop
            // would otherwise trigger). Keep it inside the loop body, or carry
            // state through a `HeapBuf`.
            if self.scope.stack(r).is_some() && !shadowed.contains(r) {
                self.fail(format!(
                    "StackBuf `{r}` cannot be captured into a `for` loop; \
                     define it inside the loop body or carry state via a `HeapBuf`"
                ));
            }
            // A compile-time field constant is capturable too: the body becomes
            // its own function, so the constant is not in scope there, and the
            // helper takes it as a parameter that the call site materializes
            // with one `SET`. Dropping it made `c = 5` followed by a loop that
            // reads `c` fail as "unbound variable", which named neither the
            // cause nor a fix.
            if matches!(
                self.scope.bound(r).map(|b| b.val),
                Some(Binding::Scalar(_) | Binding::Gaddr(_) | Binding::FConst(_))
            ) && seen.insert(*r)
            {
                captures.push((*r).to_string());
            }
        }

        // The helper takes the counter, the runtime bound (if any), then the
        // captures. `cap_args` builds an argument list (a leading expression,
        // the bound, then the captures by name).
        let runtime = matches!(hi, ForBound::Runtime(_));
        let mut params = vec![var.to_string()];
        if runtime {
            params.push(bound_var.clone());
        }
        params.extend(captures.iter().cloned());
        let cap_args = |first: Expr, bound: Expr| {
            let mut a = vec![first];
            if runtime {
                a.push(bound);
            }
            a.extend(captures.iter().map(|c| Expr::Var(c.clone())));
            a
        };

        // loop(i, [bound,] caps): run the body, advance to j = i·g, and
        // tail-recurse while j != stop. The exit test is the recursive call's
        // own condition (`JUMP`'s nonzero check on j − stop): no is-zero
        // gadget, no inverse hint, and no extra call beyond the one a loop
        // iteration already makes.
        let next_var = format!("__next{id}");
        let next = Expr::Mul(Box::new(Expr::Var(var.to_string())), Box::new(Expr::Gen));
        let mut loop_body: Vec<Stmt> = body.to_vec();
        // The counter advance and the self-call belong to the `for` header.
        let at = |kind| Stmt::new(self.cur_line, kind);
        loop_body.push(at(StmtKind::Let(next_var.clone(), next)));
        loop_body.push(at(StmtKind::CallIfNe(
            Expr::Var(next_var.clone()),
            exit,
            loop_name.clone(),
            cap_args(Expr::Var(next_var), Expr::Var(bound_var.clone())),
        )));
        loop_body.push(at(StmtKind::Return(vec![])));
        self.queue.push(Func {
            name: loop_name.clone(),
            params: params
                .into_iter()
                .map(|name| Param {
                    name,
                    kind: ParamKind::Runtime(Shape::Scalar),
                })
                .collect(),
            return_shapes: vec![],
            body: loop_body,
            inline: false,
        });

        // Enter the loop iff it runs at least once: compile-time for constant
        // bounds (an empty range compiles to nothing), a conditional call on
        // `g^lo != stop` for runtime ones.
        match hi {
            ForBound::Const(hi) => {
                if lo != *hi {
                    self.call(
                        &loop_name,
                        &cap_args(Expr::GPow(lo as u128), Expr::GPow(*hi as u128)),
                        0,
                    );
                }
            }
            ForBound::Runtime(_) => {
                let stmt = Stmt::new(
                    self.cur_line,
                    StmtKind::CallIfNe(
                        Expr::GPow(lo as u128),
                        entry_bound.clone(),
                        loop_name,
                        cap_args(Expr::GPow(lo as u128), entry_bound),
                    ),
                );
                self.stmt(&stmt);
            }
        }
    }
}

/// The literal `k` when `hi` is syntactically `lo + k` (either operand order):
/// the shape of a runtime slice, whose bounds cannot be evaluated at compile
/// time.
fn plus_k(lo: &Expr, hi: &Expr) -> Option<u128> {
    match hi {
        Expr::Add(a, b) => match (a.as_ref(), b.as_ref()) {
            (Expr::Lit(k), other) | (other, Expr::Lit(k)) if other == lo => Some(*k),
            _ => None,
        },
        _ => None,
    }
}

/// Lower one function to its instruction list and frame size.
pub(crate) fn lower_func(
    f: &Func,
    queue: &mut Vec<Func>,
    loop_ctr: &mut usize,
    defs: &HashMap<&str, &Func>,
    const_arrays: &HashMap<&str, &[F192]>,
    with_filler: bool,
) -> Lowered {
    let mut names: HashMap<String, Bound> = HashMap::new();
    for (i, p) in f.params.iter().enumerate() {
        assert!(
            !const_arrays.contains_key(p.name.as_str()),
            "`{}`: parameter `{}` collides with a top-level constant array, whose name is \
             reserved (zkDSL.md §Global constants)",
            f.name,
            p.name
        );
        // A `StackBuf(n)` parameter binds the run the caller wrote, exactly as a
        // local `StackBuf(n)` binds one it allocated.
        let off = Abi::arg(f.param_shapes(), i);
        let val = match p.shape() {
            Shape::StackBuf(n) => Binding::Stack(off, n),
            Shape::Scalar => Binding::Scalar(off),
        };
        names.insert(p.name.clone(), Bound { val, int: None });
    }
    // Reserve [0,1] retpc/retfp, params, then the flattened return area, then
    // locals. A StackBuf(n) return occupies n consecutive physical slots.
    let n_ret_cells: u32 = f.return_shapes.iter().map(|s| s.cells()).sum();
    let arg_cells = Abi::arg_cells(f.param_shapes());
    let abi_end = Abi::end(arg_cells, n_ret_cells);
    let mut lowerer = FnLower {
        scope: Scope {
            names,
            ..Default::default()
        },
        next: abi_end,
        arg_cells,
        return_shapes: &f.return_shapes,
        is_main: f.name == "main",
        fn_name: &f.name,
        tail_call: false,
        code: Vec::new(),
        cur_line: 0,
        heap_sizes: HashMap::new(),
        inline_ret: None,
        inline_stack_ret: None,

        pending: Vec::new(),
        inline_calls: Vec::new(),
        queue,
        loop_ctr,
        defs,
        const_arrays,
    };
    for (i, s) in f.body.iter().enumerate() {
        // Tail position: a conditional call whose only successor is a bare
        // `return`, in a function that returns nothing. The `mul_range` helper
        // ends exactly like this, so its self-call stops building an unwind
        // chain.
        lowerer.tail_call = !lowerer.is_main
            && f.return_shapes.is_empty()
            && matches!(s.kind, StmtKind::CallIfNe(..))
            && matches!(f.body.get(i + 1).map(|n| &n.kind), Some(StmtKind::Return(r)) if r.is_empty());
        lowerer.stmt(s);
    }
    let mut filler = Vec::new();
    if lowerer.is_main {
        lowerer.halt(); // main terminates at the sentinel pc, not by falling off
        if with_filler {
            // Past the halt, so no program code reaches them: the fill blocks are cycles
            // the interpreter enters on its own ([`FnLower::lower_filler_blocks`]).
            filler = lowerer.lower_filler_blocks();
        }
    } else if !matches!(f.body.last().map(|s| &s.kind), Some(StmtKind::Return(_))) {
        // A function must never fall off its end into whatever code the
        // layout placed next: append the implicit bare return.
        let last = f.body.last().map_or(0, |s| s.line);
        lowerer.stmt(&Stmt::new(last, StmtKind::Return(vec![])));
    }
    Lowered {
        name: f.name.clone(),
        code: lowerer.code,
        frame_size: lowerer.next,
        filler,
    }
}
