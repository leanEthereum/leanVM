/-
  LeanVM.Compiler.Ir

  The intermediate forms of the zkDSL compiler's back end: the placed IR (core statements on frame
  cells, every plumbing cell chosen), the labelled code of a function (instructions with symbolic
  immediates, `crates/zkdsl_compiler/src/ir.rs`) and the assembled program.
-/

module

public import Statement.LeanIsa

/-!
# The back end's intermediate forms

The back end takes the core IR (`LeanVM.Guest.Core`, as `Expand.expandProgram` gives it) to
leanISA bytecode in three passes, each a function between two of these forms:

1. `Place` gives every core value a frame cell and every control statement the cells it jumps
   with, as the Rust lowering does (`crates/zkdsl_compiler/src/lower.rs`): the **placed IR**
   (`PStmt`, `PFn`). It is the one pass with state, and the one that reads the expansion's
   allocation trace (`Trace`).
2. `Emit` writes each placed statement as its instructions, by structural recursion and with no
   state but the position: the **labelled code** (`LInstr`, `Lowered`), whose `SET` immediates are
   still symbolic (`KVal`), and the jump tables' slots.
3. `Assemble` lays the functions out and resolves every immediate and hint: the **assembled
   program** (`Assembled`), `OffsetInstruction`s as `Statement/Data/` holds them.

A cell is a frame offset: the operand `g^k` names the word at `fp · g^k`.
-/

namespace LeanVM.Compiler

open LeanVM.Guest LeanVM.Semantics

@[expose] public section

/-- A frame cell, as its offset from the frame pointer (`ir::Off`). -/
abbrev Cell := Nat

/-! ## Labelled code (`ir.rs`) -/

/-- A `SET` immediate before layout (`KVal`). -/
inductive KVal where
  /-- `g^S`, `S` the function's frame size: the stride to the next loop frame. -/
  | frameSize
  /-- A word, by its limbs. -/
  | const (c0 c1 : Nat)
  /-- The entry of a function. -/
  | entry (f : String)
  /-- The halting pc, the last slot of the padded bytecode. -/
  | endSentinel
  /-- Instruction `i` of the function this `SET` is in. -/
  | local (i : Nat)
  /-- Instruction `i` of the function `f`: a `match` arm's entry, in a jump-table slot. -/
  | at (f : String) (i : Nat)
  deriving Repr, DecidableEq, Inhabited

/-- Where a computed-advice hint writes (`BitsDest`). -/
inductive BitsDest where
  | stack (base : Cell)
  | heap (ptr : Cell)
  deriving Repr, BEq, Inhabited

/-- A prover hint with every size known (`RHint`, `crates/isa/src/lib.rs`), but
`Print`, which the core IR does not carry. -/
inductive RHint where
  | frameAddress (offset : Nat)
  | allocFrames (ptr : Cell) (size : Nat) (bound : Cell) (startInverse : Nat) (tail : Nat)
  | alloc (ptr : Cell) (size : Nat)
  | allocDyn (ptr size : Cell)
  | witnessStack (stream : String) (base : Cell) (len : Nat)
  | witnessHeap (stream : String) (ptr : Cell) (lo len : Nat)
  | log2Ceil (bits : BitsDest) (dst : Cell) (nbits floor : Nat)
  | bitDecompose (value : Cell) (bits : BitsDest) (nbits : Nat)
  | bitDecomposeExp (value : Cell) (bits : BitsDest) (nbits : Nat)
  | digitDecomposeExp (value : Cell) (dst : BitsDest) (nbits ndigits digitBits start : Nat)
      (startCell : Option Cell)
  | windowsExp (value : Cell) (dest : BitsDest) (skip start width count : Nat)
  | fieldLimbs (value base : Cell) (len : Nat)
  | inverse (value dst : Cell)
  deriving Repr, BEq, Inhabited

/-- The iterations a loop's frames are reserved for (`LoopCount`). -/
inductive LoopCount where
  | constant (n : Nat)
  /-- From `g^start` to the word of `cell`. -/
  | bound (cell : Cell) (start : Nat)
  deriving Repr, BEq, Inhabited

/-- A hint before layout (`Hint`): the allocation of a frame waits for the callee's frame size. -/
inductive LHint where
  | nextFrameAddress
  | allocLoopFrames (ptr : Cell) (callee : String) (count : LoopCount) (tail : Nat)
  | allocFrame (ptr : Cell) (callee : String)
  | allocFrameMax (ptr : Cell) (callees : List String)
  | resolved (h : RHint)
  deriving Repr, BEq, Inhabited

/-- An instruction before layout (`LOp`). -/
inductive LOp where
  /-- A copy into the next loop frame: `c` is an offset in that frame. -/
  | mulNextFrame (a b c : Cell)
  | set (o : Cell) (k : KVal)
  | xor (a b c : Cell)
  | mul (a b c : Cell)
  | deref (o1 : Cell) (o2 : Nat) (o3 : Cell) (mode : DerefMode)
  | jump (oc od of : Cell)
  /-- `dst` is slot `x = g^j` of the jump table at `first`. -/
  | slot (x : Cell) (first : Nat) (dst : Cell)
  | keccak (m0 m1 m2 m3 tail b8 cap out : Cell) (inOdd outOdd : Bool)
      (outCells : KeccakOutputCells)
  deriving Inhabited

/-- An instruction and the hints that fire before it (`LInstr`). -/
structure LInstr where
  op : LOp
  hints : List LHint
  deriving Inhabited

/-- A function's labelled code (`Lowered`). -/
structure Lowered where
  name : String
  code : Array LInstr
  frameSize : Nat
  deriving Inhabited

/-! ## The placed IR -/

/-- A call's cells: the callee's frame pointer `nfp`, the cell holding its entry, the jump's
condition `oc`, and the caller's cells of its arguments and returns, in the callee's order. -/
structure CallSite where
  callee : String
  nfp : Cell
  entry : Cell
  oc : Cell
  args : List Cell
  rets : List Cell
  /-- The callee is a loop helper whose frames are reserved in one run. -/
  loop : Option LoopCount
  /-- The callee takes over this frame's return target. -/
  tail : Bool
  deriving Inhabited

/-- A placed statement: a core statement on frame cells. Every constructor is a fixed run of
instructions (`Emit`), and `hints` fire before its first. -/
inductive PStmt where
  /-- One instruction, never a taken jump. -/
  | op (hints : List LHint) (o : LOp)
  /-- A forward branch on `c`: `SET bdest; JUMP c bdest sfp; zero; [SET edest; JUMP one edest sfp;
  nonzero]`, the bracket when the source has an `else` block (`hasElse`), which may emit
  nothing. -/
  | ite (hints : List LHint) (c bdest sfp : Cell) (zero : List PStmt) (hasElse : Bool)
      (edest one : Cell) (nonzero : List PStmt)
  /-- A chain of `match`es: `SET join; DEREF entry from slot x of table firsts[0]; JUMP one entry sfp`,
  then the arms of each, arm `j` of `match` `k` filling slot `firsts[k] + j`. An arm's block
  holds its exit: the jump to the join, or through the next table. -/
  | chain (hints : List LHint) (join x entry one sfp : Cell) (firsts : List Nat)
      (stages : List (List (List PStmt)))
  /-- A call. -/
  | call (hints : List LHint) (c : CallSite)
  /-- A loop helper's closing call into the next frame of its run: the copies of the arguments,
  of the next frame's pointer `nfp` and of the return registers, then the jump on `oc`. -/
  | loopNext (hints : List LHint) (callee : String) (nfp entry oc one : Cell) (args : List Cell)
  /-- A fused `match` of calls on one shared frame, through the shared table at `first`. -/
  | dispatch (hints : List LHint) (callees : List String) (nfp joinCell x entry one : Cell)
      (first : Nat) (args rets : List Cell)
  /-- `return`: `JUMP one 0 1`. -/
  | ret (hints : List LHint) (one : Cell)
  /-- `main`'s end: `SET dest := halting pc; JUMP one dest one`. -/
  | halt (hints : List LHint) (one dest : Cell)
  deriving Inhabited

/-- A placed function. -/
structure PFn where
  name : String
  body : List PStmt
  frameSize : Nat
  deriving Inhabited

/-! ## The assembled program -/

/-- An assembled program: the bytecode before its padding to `size` slots with `SET fp[0] = 0`,
the hints by pc, `main`'s frame, and the functions' ranges (`isa::Program`). -/
structure Assembled where
  size : Nat
  code : Array OffsetInstruction
  hints : Array (Nat × List RHint)
  mainFrame : Nat
  fns : Array (String × Nat × Nat)
  deriving Inhabited

end
end LeanVM.Compiler
