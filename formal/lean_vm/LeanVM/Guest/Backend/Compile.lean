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

/-- The labelled code of a program's functions, in order, and the jump tables' slots. -/
def lowerProgram (p : List TracedFn) : Except String (List Lowered × Array KVal) := do
  let (fns, tables) ← placeProgram p
  let (lowered, fills) := fns.foldl (init := (#[], #[])) fun (ls, fills) pf =>
    let (l, f) := emitFn pf.fn
    (ls.push l, fills ++ f)
  return (lowered.toList, tableSlots tables.len fills tables.entries)

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
