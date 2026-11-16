/-
  LeanVM.Guest.Backend.Complete.ProgramDone

  Whole-program completeness of the back end, for every compiled program.
-/

module

public import LeanVM.Guest.Backend.Complete.ProgRun

/-!
# Whole-program completeness

`program_complete : ProgramCompleteStmt`: the composition `main_runW` at the back end's data,
each function's run `cplRun_B`, the frames of the honest memory `frame_honestB`, the jump tables
`jt_honestB`, and no path calling `main` (`no_main_call`).
-/

namespace LeanVM.Guest.Backend.Complete

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory

@[expose] public section

/-- **Whole-program completeness of the back end**, for every compiled program passing the
per-function conditions. -/
theorem program_complete : ProgramCompleteStmt := by
  intro κ₀ W hW hC keyed hdr rd T hT hH
  exact main_runW (W := W) (FH := FHB W) (ω := fun f σ op => W.fnCost keyed f σ op)
    ⟨cplRun_B hW hC keyed, frame_honestB hW hC, fun _ _ _ hT' hH' => jt_honestB hW hT' hH',
      fun _ htf _ _ _ hw => no_main_call hW htf hw⟩ hdr rd T hT hH

end
end LeanVM.Guest.Backend.Complete

/-- info: 'LeanVM.Guest.Backend.Complete.program_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Backend.Complete.program_complete
