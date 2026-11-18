/-
  LeanVM.Compiler.Compile

  The zkDSL compiler in Lean: the front end (`Expand`) and the back end, a zkDSL program to its
  assembled bytecode and hints.
-/

module

public import LeanVM.Guest.Expand
public import LeanVM.Compiler.Consts
public import LeanVM.Compiler.Assemble

/-!
# The compiler

`compile` is the Rust compiler's `compile` (`crates/zkdsl_compiler/src/lib.rs` at leanVM `6363526c0`) as four functions:

    Source.Program ─Expand.expandProgramTraced→ List TracedFn ─withConstTable→ List TracedFn
      ─placeProgram→ List PFn ─emitFn→ List Lowered, jump table slots ─assemble→ Assembled

The first is the front end, `Expand`, with the allocation trace it records; the others are the
back end, `compileTraced`. `lowerProgram` checks the loop helpers' constant parameters
(`ConstsOk`) before it places the program.
`cli/GuestBackend.lean` runs it compiled on the guest's source and compares the result with
`Statement/Data/`, instruction for instruction.
-/

namespace LeanVM.Compiler

open LeanVM.Guest

@[expose] public section

/-- The jump tables hold what was written: every slot an arm filled names that arm, and every
slot of a shared table its callee. A slot written twice fails here. -/
def slotsHold (slots : Array KVal) (fills : List Fill) (shared : List (List String × Nat)) :
    Bool :=
  (fills.all fun x => decide (slots[x.1]? = some x.2)) &&
    shared.all fun p => p.1.zipIdx.all fun x => decide (slots[p.2 + x.2]? = some (.entry x.1))

/-- The jump table slots the placed functions fill, in order. -/
def fillsOf (fns : List Placed) : List Fill := fns.flatMap fun pf => (emitFn pf.fn).2.toList

/-- The labelled code of a program's functions, in order, and the jump tables' slots, its loop
helpers' constant parameters right of it. -/
def lowerProgram (p : List TracedFn) : Except String (List Lowered × Array KVal) :=
  if !ConstsOk (constsOf (loopTable p)) (p.map (·.core)) then
    .error "a constant parameter that a call does not pass as its word"
  else
  match placeProgram p with
  | .error e => .error e
  | .ok (fns, tables) =>
      let slots := tableSlots tables.len (fillsOf fns).toArray tables.entries
      if !slotsHold slots (fillsOf fns) tables.shared then .error "a jump table slot written twice"
      else .ok (fns.map fun pf => (emitFn pf.fn).1, slots)

/-- The back end: the core functions of a program, each with its source and its trace, to the
assembled program, its loop helpers' constant parameters found (`withConstTable`). -/
def compileTraced (p : List TracedFn) : Except String Assembled := do
  let (fns, slots) ← lowerProgram (withConstTable p)
  return assemble fns slots

/-- The compiler: a zkDSL program to its assembled program. -/
def compile (p : Source.Program) : Except String Assembled := do
  compileTraced (← Expand.expandProgramTraced p)

end
end LeanVM.Compiler
