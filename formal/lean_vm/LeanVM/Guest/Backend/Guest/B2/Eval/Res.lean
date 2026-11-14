/-
  LeanVM.Guest.Backend.Guest.B2.Eval.Res

  The residual table checked against the functions' prologues by the kernel, and the residual
  facts.
-/

module

public import LeanVM.Guest.Backend.Guest.B2.Prologue

namespace LeanVM.Guest.Backend.B2

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core

@[expose] public section

/-- **Every residual entry is written by its function's prologue.** -/
theorem residual_ok : residualOk = true := by decide +kernel

/-- **The residual facts hold**: at every frame where the run from function `j`'s entry halts,
its residual values' cells hold what the table says. -/
theorem residualFacts : ResidualFacts := by
  intro κ L j k fp h1 h2 hs p hp
  unfold resOf at hp
  cases hx : residual.find? (·.1 == (coreOf j).name) with
  | none => simp [hx] at hp
  | some x =>
    rw [hx, Option.map_some, Option.getD_some] at hp
    have hxn : x.1 = (coreOf j).name := by
      have := List.find?_some hx
      simpa using this
    have hrow := List.all_eq_true.mp residual_ok x (List.mem_of_find?_eq_some hx)
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hrow
    obtain ⟨⟨⟨h1', h2'⟩, hn⟩, hok⟩ := hrow
    obtain rfl : x.2.1 = j :=
      coreOf_name_inj h1' h2' h1 h2 ((fn_names h1' h2').1.symm.trans (hn.trans hxn))
    exact resEntryOk_sound (prologue_holds (fnOf_mem h2) hs) (List.all_eq_true.mp hok p hp)

end
end LeanVM.Guest.Backend.B2

/-- info: 'LeanVM.Guest.Backend.B2.residualFacts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Backend.B2.residualFacts
