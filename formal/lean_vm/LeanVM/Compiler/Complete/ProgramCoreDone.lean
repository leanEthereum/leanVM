/-
  LeanVM.Compiler.Complete.ProgramCoreDone
  Whole-program completeness of the back end from a core run.
-/

module

public import LeanVM.Compiler.Complete.ProgramDone
public import LeanVM.Compiler.Complete.CoreHonest

/-!
# Whole-program completeness from a core run

`program_complete_core : ProgramCompleteCoreStmt`: `honestAt_of_core` gives the re-chosen run
`HonestAt` the back end's data, and `program_complete` runs the bytecode on its honest memory.
-/

namespace LeanVM.Compiler.Complete

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory

@[expose] public section

/-- **Whole-program completeness of the back end from a core run**, for every compiled program
passing the per-function conditions. -/
theorem program_complete_core : ProgramCompleteCoreStmt := by
  intro κ₀ W hW hC keyed hdr T M hT hv hb hp hl h0 h1 hs ha
  obtain ⟨ν, rd, hH⟩ := honestAt_of_core hW hC hv hb hp hl h0 h1 hs ha
  obtain ⟨c, hc, hle⟩ := program_complete W hW hC keyed hdr rd _ (by rw [name_retemp]; exact hT) hH
  exact ⟨ν, c, hc, hle⟩

end
end LeanVM.Compiler.Complete

/-- info: 'LeanVM.Compiler.Complete.program_complete_core' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Compiler.Complete.program_complete_core
