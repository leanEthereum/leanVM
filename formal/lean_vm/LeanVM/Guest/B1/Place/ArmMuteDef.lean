/-
  LeanVM.Guest.B1.Place.ArmMuteDef

  The check that an arm of `open_stacked` pops nothing itself and calls only `level_queries` or functions with no witness hint in their subtrees, and what it gives.
-/

module

public import LeanVM.Guest.B1.Common.NoWitMute
public import LeanVM.Guest.B1.Whir.HelperTables

/-!
# The arms' mute check

* `lqNameB g`: `g` names an entry of `lqTable`;
* `armS g`: `g` is such a name or passes `noWitness`;
* `armMuteOk name j`: function `j` is named `name`, has no witness hint in its body, and each of its callees is an entry of `lqTable` or has no witness hint in its subtree (`noWitCallee j`), decided by the kernel per arm (`ArmMuteA`, `ArmMuteB`);
* `armMute_find`: such a function's body is mute in `armS`.
-/

namespace LeanVM.Guest.B1.Arm

open LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1.Whir

@[expose] public section

/-- `g` names an entry of `lqTable`. -/
def lqNameB (g : String) : Bool := lqTable.any (·.1 == g)

/-- A name of `lqTable`, or a function passing `noWitness`. -/
noncomputable def armS (g : String) : Bool := lqNameB g || noWitS g

/-- **Function `j`, named `name`, pops nothing itself, and calls `level_queries` or functions with no witness
hint in their subtrees.** -/
noncomputable def armMuteOk (name : String) (j : ℕ) : Bool :=
  match coreProgram[j]? with
  | some fn => fn.name == name && Stmt.noWitList fn.body &&
      (Stmt.blockCallees fn.body).all fun g => lqNameB g || noWitCallee j g
  | none => false

theorem armMute_find {name : String} {j : ℕ} (h : armMuteOk name j = true) :
    ∃ fn, coreProgram.find? name = some fn ∧ Stmt.muteList armS fn.body = true := by
  unfold armMuteOk at h
  split at h
  · next fn hj =>
    simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, Bool.or_eq_true] at h
    obtain ⟨⟨hn, hw⟩, hc⟩ := h
    refine ⟨fn, coreProgram_find?_at hj hn, Stmt.muteList_of_noWit fn.body hw fun g hg ↦ ?_⟩
    rcases hc g hg with h | h
    · simp [armS, h]
    · simp [armS, noWitS_of_callee h]
  · exact absurd h Bool.false_ne_true

end
end LeanVM.Guest.B1.Arm
