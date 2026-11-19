/-
  LeanVM.Compiler.Trace

  The allocation trace of an expansion: what the Rust lowering decides while it walks the source
  and the core IR does not keep, as advice to the back end.
-/

module

public import LeanVM.Core
public import LeanVM.Core.Source

/-!
# The allocation trace

The core IR keeps a function's relations, not its frame. The Rust lowering
(`crates/zkdsl_compiler/src/lower.rs` at leanVM `6363526c0`) takes a frame cell wherever the expansion makes a value
(`Expand.fresh`, `Expand.freshRun`), and the core IR names a value only where a statement uses
it. So the following are gone from the core IR, and each moves cells:

* a value no statement names (a `StackBuf` cell never read, the destination of an `@inline` call
  whose return aliases a run or an address, the site of an `@inline` call): the trace marks it
  `Kind.unnamed` (`markUnnamed`) and it takes no cell, where the Rust lowering gave it one;
* which values are no cell at all: an `addr` pointer, the return area;
* which constants, sums, products and loads the lowering takes from a pool, and which it writes
  into a cell of their own (`const_cell` and `pure` against `expr_into`, `xor_byte`, an anchor);
  a constant set into a cell of its own that every other statement only reads as one cell, in
  its block, is taken from the pool too (`markPooled`), where the Rust lowering gave it a cell;
* which values share a cell with a value they are copied from, into, or asserted equal to: the
  trace marks them `Kind.joined` and moves their allocation to the statement where they are first
  named (`markJoined`), where the Rust lowering gave each a cell and emitted the copy or check;
* when a cell is taken relative to the cells a statement takes for its own plumbing (a pooled
  `1`, a callee's frame pointer, a jump target);
* an `else` block that emits nothing, which the lowering still jumps over; two `match`es chained;
  the offset `at` of a `hint_windows_exponent` into frame cells.

The trace (`Event`) is the expansion's record of them, in the order it runs: one `alloc` a
`fresh` or `freshRun`, with how the lowering treats it (`Kind`), one `emit` a core statement, and
`enter`, `leave` around a branch or an arm. `Expand` records it (`Expand.expandProgramTraced`),
and `Place` walks a core function and its trace together.

The trace is advice. Placement takes from it when a value's cells are taken, how many, and
whether a pool is asked, never what an instruction relates: every cell is the next free one or a
pooled cell holding the same word, and placement fails rather than use a value the trace gave no
cell. So the statement to prove of placement quantifies over every trace.
-/

namespace LeanVM.Compiler

open LeanVM.Core
open LeanVM.Core (V)

@[expose] public section

/-- How the lowering treats a value the expansion makes. -/
inductive Kind where
  /-- Its cells are the next free ones, taken now (`fresh`, `alloc_stack`). -/
  | cell
  /-- The result of `const_cell`, `pure` or a cached load, or a constant `markPooled` pools: the
  pool's cell if the scope holds one, else the next free one, written by the statement that
  follows. -/
  | pooled
  /-- A value no statement of the function names, such as the site of an `@inline` call
  (`Core.Seg.i`): no cell. -/
  | unnamed
  /-- An `addr` pointer: no cell, the frame pointer and an offset (`stack_addr`). -/
  | addr
  /-- The return area, which the frame holds past its arguments. -/
  | ret
  /-- The Keccak padding run, whose first cells are also the pooled `0x01` and `0`
  (`keccak_pad_run`). -/
  | padRun
  /-- Cells shared with values already placed: the cells of the values the next statements,
  reached through atoms only, equate with it (a copy either way round, an `assert ==`), when they
  are consecutive; else the next free ones (`sponge_run`, `markJoined`). -/
  | joined
  deriving DecidableEq, Repr, Inhabited

/-- One step of an expansion, as placement follows it. -/
inductive Event where
  /-- A value is made: its cells hold the values `vs`, in order (one value, or the run of a
  buffer). -/
  | alloc (vs : List V) (kind : Kind)
  /-- A core statement is emitted; a branch or a `match` after its blocks. -/
  | emit
  /-- A branch or an arm begins. -/
  | enter
  /-- A branch or an arm ends. -/
  | leave
  /-- The value is wanted in a cell (`materialize` of an address with no shift of its own). -/
  | use (v : V)
  /-- The next `addr` value is the pointer `v` shifted by `exp` cells (`materialize`). -/
  | shift (v : V) (exp : Nat)
  /-- The arms of the `match` lowered next end in the dispatch of the one after it
  (`chain_next`). -/
  | chain
  /-- The offset `at` of the `hint_windows_exponent` emitted next. -/
  | note (n : Nat)
  deriving Repr, Inhabited

/-- The value the atom equates with `v`: the other side of a copy or an `assert ==` naming it
(the values a `Kind.joined` allocation may share a cell with). -/
def eqPartner (v : V) : Atom → Option V
  | .copy d s => if d == v then some s else if s == v then some d else none
  | .assertEq a b => if a == v then some b else if b == v then some a else none
  | _ => none

/-- A lowered function: its core function and its trace, and what the back end takes from its
source as the expansion queued it: the cells of its returned values and its `loopSource`; and,
for a loop helper, its constant parameters (`Consts.lean`, `withConstTable`). -/
structure TracedFn where
  core : Core.Fn
  trace : Array Event
  /-- The cells of its returned values (`returnShapes`). -/
  rets : Nat
  /-- `loopSource` of its source: whether a loop helper's frames are reserved in one run, and
  its constant exit bound. -/
  loop : Bool × Option Nat
  /-- Its constant parameters: argument positions and the word every call passes there. -/
  consts : List (Nat × LeanVM.Parameters.E) := []
  deriving Inhabited

open LeanVM.Core.Source in
/-- A loop helper's entry of `loop_bounds` (`lower_for`), from the helper the expansion queued:
its body is the loop's, then `next = counter · g`, the closing `callIfNe next exit` and a
`return`. Its frames are reserved in one run when the loop's body has no `return` and does not
bind the counter; its exit is a constant power of `g`, or the runtime bound. -/
def loopSource (f : Func) : Bool × Option Nat :=
  let body := f.body.take (f.body.length - 3)
  let counter := (f.params.head?.map (·.name)).getD ""
  let registered := !Stmt.hasRetList body && !(Stmt.bindsList body).contains counter
  let hi := match f.body[f.body.length - 2]? with
    | some (.mk _ (.callIfNe _ (.gpow h) _ _)) => some h
    | _ => none
  (registered, hi)

end
end LeanVM.Compiler
