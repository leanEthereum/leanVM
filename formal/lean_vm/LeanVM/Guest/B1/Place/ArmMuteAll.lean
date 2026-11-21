/-
  LeanVM.Guest.B1.Place.ArmMuteAll

  Every arm of `open_stacked` is mute but for its `level_queries` calls, and the names of its other callees are not `level_queries`'.
-/

module

public import LeanVM.Guest.B1.Place.ArmMuteA
public import LeanVM.Guest.B1.Place.ArmMuteB
public import LeanVM.Guest.B1.Place.OsMean

/-!
# The arms' callees

* `armMute_all`: the arm `m`'s body is mute in `armS` (`ArmMuteA`, `ArmMuteB`);
* `lqNameB_of_kind`, `lqNameB_of_lp`, `lqNameB_of_lr`: a named callee's, a `level_positions`' and a `level_residual`'s names are not `level_queries`' (by the kernel, over the tables).
-/

namespace LeanVM.Guest.B1.Arm

open LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1 LeanVM.Guest.B1.Whir

@[expose] public section

/-- **The arm `m`'s body is mute in `armS`.** -/
theorem armMute_all {m : ℕ} (hm : m < 11) :
    ∃ fn, coreProgram.find? ("open_stacked__L" ++ natStr m) = some fn ∧ Stmt.muteList armS fn.body = true := by
  interval_cases m
  · exact armMute_find armMute0
  · exact armMute_find armMute1
  · exact armMute_find armMute2
  · exact armMute_find armMute3
  · exact armMute_find armMute4
  · exact armMute_find armMute5
  · exact armMute_find armMute6
  · exact armMute_find armMute7
  · exact armMute_find armMute8
  · exact armMute_find armMute9
  · exact armMute_find armMute10

theorem lq_not_named : lqTable.all (fun e ↦ (osKindOf e.1).isNone) = true := by decide +kernel

theorem lp_not_lq : lpTable.all (fun e ↦ !lqNameB e.1) = true := by decide +kernel

theorem lr_not_lq : lrTable.all (fun e ↦ !lqNameB e.1) = true := by decide +kernel

/-- **A named callee is not `level_queries`.** -/
theorem lqNameB_of_kind {g : String} {K : OsKind} (h : osKindOf g = some K) : lqNameB g = false := by
  cases hq : lqNameB g
  · rfl
  · obtain ⟨e, he, hg⟩ := List.any_eq_true.mp hq
    have := List.all_eq_true.mp lq_not_named e he
    rw [beq_iff_eq.mp hg, h] at this
    exact absurd this (by simp)

/-- **`level_positions` is not `level_queries`.** -/
theorem lqNameB_of_lp {g : String} {x : ℕ × String × ℕ × ℕ} (he : (g, x) ∈ lpTable) : lqNameB g = false := by
  simpa using List.all_eq_true.mp lp_not_lq _ he

/-- **`level_residual` is not `level_queries`.** -/
theorem lqNameB_of_lr {g : String} {x : ℕ × ℕ × ℕ × ℕ × String × String} (he : (g, x) ∈ lrTable) :
    lqNameB g = false := by
  simpa using List.all_eq_true.mp lr_not_lq _ he

end
end LeanVM.Guest.B1.Arm
