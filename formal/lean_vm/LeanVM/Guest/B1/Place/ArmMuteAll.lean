/-
  LeanVM.Guest.B1.Place.ArmMuteAll

  Every arm of `open_stacked` is mute but for its `level_queries` calls, and the names of its other callees are not `level_queries`'.
-/

module

public import LeanVM.Guest.B1.Place.ArmMuteA
public import LeanVM.Guest.B1.Place.ArmMute6
public import LeanVM.Guest.B1.Place.ArmMute7
public import LeanVM.Guest.B1.Place.ArmMute8
public import LeanVM.Guest.B1.Place.ArmMute9
public import LeanVM.Guest.B1.Place.ArmMute10
public import LeanVM.Guest.B1.Place.KindPre

/-!
# The arms' callees

* `armMute_all`: the arm `m`'s body is mute in `armS` (`ArmMuteA`, `ArmMute6` to `ArmMute10`);
* `lqNameB_of_kind`, `lqNameB_of_lp`, `lqNameB_of_lr`: a named callee's, a `level_positions`' and a `level_residual`'s names are not `level_queries`' (their prefixes apart, `Place/NamePre`).
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

/-- **A named callee is not `level_queries`.** -/
theorem lqNameB_of_kind {g : String} {K : OsKind} (h : osKindOf g = some K) : lqNameB g = false :=
  List.any_eq_false.mpr fun e he hg ↦ (osKindOf_pre h).2.2 (beq_iff_eq.mp hg ▸ lqTable_hasPre e he)

/-- **`level_positions` is not `level_queries`.** -/
theorem lqNameB_of_lp {g : String} {x : String × ℕ × ℕ} (he : (g, x) ∈ lpTable) : lqNameB g = false :=
  any_name_eq_false apart_pos_queries (lpTable_hasPre _ he) lqTable_hasPre

/-- **`level_residual` is not `level_queries`.** -/
theorem lqNameB_of_lr {g : String} {x : ℕ × ℕ × ℕ × String × String} (he : (g, x) ∈ lrTable) :
    lqNameB g = false :=
  any_name_eq_false apart_res_queries (lrTable_hasPre _ he) lqTable_hasPre

end
end LeanVM.Guest.B1.Arm
