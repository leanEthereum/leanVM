/-
  LeanVM.Guest.Compiled.Cpl.WholeChecked
  The checked back end accepts the guest, and the guest's completeness from a core run through
  `program_complete_checked`.
-/

module

public import LeanVM.Compiler.Complete.ProgramChecked
public import LeanVM.Guest.Compiled.Cpl.Whole

/-!
# The guest through the checked back end

`guest_compileChecked`: the checked back end accepts the guest's traced program with the code of
`W0`, from `guest_compiles` (`W0_compiled`) and the per-function conditions already decided by the
kernel (`guestConds`, from `CplEval.cplOkAll`); no new evaluation.
`guest_core_complete_checked`: `program_complete_checked` at `W0`.
-/

namespace LeanVM.Guest.Compiled.Cpl

open LeanVM.Compiler LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory

@[expose] public section

/-- **The checked back end accepts the guest.** -/
theorem guest_compileChecked : compileChecked W0.p = .ok (W0.fns, W0.slots) :=
  compileChecked_of W0 W0_compiled.1 guestConds

/-- **The guest is complete through the checked back end from a run of its core IR.** -/
theorem guest_core_complete_checked : ∀ (hdr : E × E) (T : Tree)
    (M : MemoryImage (logMem (T.total W0.fsB))), T.name = "main" →
    T.Valid W0.core M.read [] [] → T.BufsOk W0.core →
    T.Placed W0.core W0.fsB W0.cellB 0 → T.LoadsIn W0.core W0.fsB W0.cellB (fun i => i < 2) 0 →
    M.read (addressOfIndex 0) = some hdr.1 → M.read (addressOfIndex 1) = some hdr.2 →
    T.total W0.fsB ≤ 2 ^ 30 →
    (∀ q ∈ T.eqns W0.core, ∃ i : Fin (2 ^ logMem (T.total W0.fsB)), q.1 = addressOfIndex i) →
    ∃ ν : ℕ → String → Val → V → E, ∃ c : Opcode → ℕ,
      RunC W0.prog (W0.honestB hdr (T.retemp W0.core W0.fsB ν 0))
        ⟨addressOfIndex (W0.ent "main"), 1⟩ (Registers.final W0.prog) c ∧
      ∀ op, c op ≤ W0.progCost (fun _ => false) (T.retemp W0.core W0.fsB ν 0) op :=
  Complete.program_complete_checked W0 guest_compileChecked W0_compiled.2 (fun _ => false)

end
end LeanVM.Guest.Compiled.Cpl

/-- info: 'LeanVM.Guest.Compiled.Cpl.guest_compileChecked' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Compiled.Cpl.guest_compileChecked

/-- info: 'LeanVM.Guest.Compiled.Cpl.guest_core_complete_checked' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Compiled.Cpl.guest_core_complete_checked
