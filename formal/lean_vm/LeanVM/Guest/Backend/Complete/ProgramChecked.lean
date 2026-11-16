/-
  LeanVM.Guest.Backend.Complete.ProgramChecked
  Whole-program completeness of the checked back end from a core run: no per-function
  hypothesis, the checks being inside the back end.
-/

module

public import LeanVM.Guest.Backend.Complete.ProgramCoreDone
public import LeanVM.Guest.Backend.CompileChecked

/-!
# Whole-program completeness of the checked back end

`ProgramCompleteCheckedStmt` is `ProgramCompleteCoreStmt` with `W.Compiled` and the per-function
conditions `FnConds` replaced by: the checked back end accepts the program and gives the world's
code (`compileChecked W.p = .ok (W.fns, W.slots)`), padded to the world's size. Its other
hypotheses are the core run's, unchanged: validity, `BufsOk`, the size bound and the equations in
the memory, the public input, and the two placement conditions `Tree.Placed` and `Tree.LoadsIn`,
which no per-function check replaces (STATUS-wpc.md, phase 4).

`program_complete_checked` is `program_complete_core` through `compileChecked_ok`.
-/

namespace LeanVM.Guest.Backend.Complete

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory

@[expose] public section

/-- **Whole-program completeness of the checked back end from a core run.** -/
def ProgramCompleteCheckedStmt : Prop :=
  ∀ {κ₀ : ℕ} (W : World κ₀), compileChecked W.p = .ok (W.fns, W.slots) →
    (assemble W.fns W.slots).size = 2 ^ W.logSize →
    ∀ (keyed : String → Bool) (hdr : E × E) (T : Tree)
      (M : MemoryImage (logMem (T.total W.fsB))), T.name = "main" →
      T.Valid W.core M.read [] [] → T.BufsOk W.core →
      T.Placed W.core W.fsB W.cellB 0 → T.LoadsIn W.core W.fsB W.cellB (fun i => i < 2) 0 →
      M.read (addressOfIndex 0) = some hdr.1 → M.read (addressOfIndex 1) = some hdr.2 →
      T.total W.fsB ≤ 2 ^ 30 →
      (∀ q ∈ T.eqns W.core, ∃ i : Fin (2 ^ logMem (T.total W.fsB)), q.1 = addressOfIndex i) →
      ∃ ν : ℕ → String → Val → V → E, ∃ c : Opcode → ℕ,
        B2C.RunC W.prog (W.honestB hdr (T.retemp W.core W.fsB ν 0))
          ⟨addressOfIndex (W.ent "main"), 1⟩ (Registers.final W.prog) c ∧
        ∀ op, c op ≤ W.progCost keyed (T.retemp W.core W.fsB ν 0) op

/-- **Whole-program completeness of the checked back end from a core run**: every program the
checked back end accepts. -/
theorem program_complete_checked : ProgramCompleteCheckedStmt := by
  intro κ₀ W hW hs
  exact program_complete_core W (compiled_of_checked hW hs) ((compileChecked_ok hW).2 W rfl)

end
end LeanVM.Guest.Backend.Complete

/-- info: 'LeanVM.Guest.Backend.Complete.program_complete_checked' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Backend.Complete.program_complete_checked
