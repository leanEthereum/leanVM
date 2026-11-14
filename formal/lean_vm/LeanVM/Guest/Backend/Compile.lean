/-
  LeanVM.Guest.Backend.Compile

  The guest compiler in Lean: the front end (`Expand`) and the back end, a zkDSL program to its
  assembled bytecode and hints.
-/

module

public import LeanVM.Guest.Expand
public import LeanVM.Guest.Backend.ExpandTrace
public import LeanVM.Guest.Backend.Place
public import LeanVM.Guest.Backend.Assemble

/-!
# The compiler

`compile` is `lean_compiler::compile` (`crates/lean_compiler/src/lib.rs`) as four functions:

    Source.Program ─ExpandTrace.expandProgram→ List TracedFn ─placeProgram→ List PFn
      ─emitFn→ List Lowered, jump table slots ─assemble→ Assembled

The first is the front end, `Expand.expandProgram`, recording its allocation trace
(`TraceFaithful`); the other three are the back end, `compileTraced`.
`cli/GuestBackend.lean` runs it compiled on the guest's source and compares the result with
`Statement/Data/`, instruction for instruction.
-/

namespace LeanVM.Guest.Backend

@[expose] public section

/-- The jump tables hold what was written: every slot an arm filled names that arm, and every
slot of a shared table its callee. A slot written twice fails here. -/
def slotsHold (slots : Array KVal) (fills : List Fill) (entries : List (Nat × String)) : Bool :=
  (fills.all fun x => decide (slots[x.1]? = some x.2)) &&
    entries.all fun x => decide (slots[x.1]? = some (.entry x.2))

/-- The labelled code of a program's functions, in order, and the jump tables' slots. -/
def lowerProgram (p : List TracedFn) : Except String (List Lowered × Array KVal) := do
  let (fns, tables) ← placeProgram p
  let emitted := fns.map fun pf => emitFn pf.fn
  let fills := emitted.flatMap (·.2.toList)
  let slots := tableSlots tables.len fills.toArray tables.entries
  if !slotsHold slots fills tables.entries.toList then throw "a jump table slot written twice"
  return (emitted.map (·.1), slots)

/-- The back end: the core functions of a program, each with its source and its trace, to the
assembled program. -/
def compileTraced (p : List TracedFn) : Except String Assembled := do
  let (fns, slots) ← lowerProgram p
  return assemble fns slots

/-- The compiler: a zkDSL program to its assembled program. -/
def compile (p : Source.Program) : Except String Assembled := do
  compileTraced (← ExpandTrace.expandProgram p)

/-- The traced expansion's core functions are the expansion's: the back end compiles the core IR
`Expand.expandProgram` gives. `guest-backend check` tests it on the guest. -/
def TraceFaithful : Prop :=
  ∀ p : Source.Program,
    (ExpandTrace.expandProgram p).map (·.map (·.core)) = Expand.expandProgram p

end
end LeanVM.Guest.Backend
