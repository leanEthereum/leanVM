/-
  LeanVM.Guest.B1.Place.ArmMuteAll

  Every arm of `open_stacked` is mute but for its `level_queries` calls, and the names of its other callees are not `level_queries`'.
-/

module

public import LeanVM.Guest.B1.Place.ArmOkA
public import LeanVM.Guest.B1.Place.ArmOkB
public import LeanVM.Guest.B1.Place.ArmFree0
public import LeanVM.Guest.B1.Place.ArmFree1
public import LeanVM.Guest.B1.Place.ArmFree2
public import LeanVM.Guest.B1.Place.ArmFree3
public import LeanVM.Guest.B1.Place.ArmFree4
public import LeanVM.Guest.B1.Place.ArmFree5
public import LeanVM.Guest.B1.Place.OsMean
public import LeanVM.Guest.B1.Place.NamePre

/-!
# The arms' callees

* `armMute_all`: the arm `m`'s body is mute in `armS` (`ArmOkA`, `ArmOkB`; the roots by `nwRootsOk`, `ArmFree0` to
  `ArmFree5`);
* `lqNameB_of_kind`, `lqNameB_of_lp`, `lqNameB_of_lr`: a named callee's, a `level_positions`' and a `level_residual`'s names are not `level_queries`' (their prefixes apart, `Place/NamePre`).
-/

namespace LeanVM.Guest.B1.Arm

open LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1 LeanVM.Guest.B1.Whir

@[expose] public section

/-- **Every root names an entry of `lqTable` or has no witness hint in its subtree.** -/
theorem nwRootsOk : NwRootsOk := nwRootsOk_of armFreeM0 armFreeM1 armFreeM2 armFreeM3 armFreeM4 armFreeM5

/-- **The arm `m`'s body is mute in `armS`.** -/
theorem armMute_all {m : ℕ} (hm : m < 11) :
    ∃ fn, coreProgram.find? ("open_stacked__L" ++ natStr m) = some fn ∧ Stmt.muteList armS fn.body = true := by
  interval_cases m
  · exact armMute_find nwRootsOk armOk0.2
  · exact armMute_find nwRootsOk armOk1.2
  · exact armMute_find nwRootsOk armOk2.2
  · exact armMute_find nwRootsOk armOk3.2
  · exact armMute_find nwRootsOk armOk4.2
  · exact armMute_find nwRootsOk armOk5.2
  · exact armMute_find nwRootsOk armOk6.2
  · exact armMute_find nwRootsOk armOk7.2
  · exact armMute_find nwRootsOk armOk8.2
  · exact armMute_find nwRootsOk armOk9.2
  · exact armMute_find nwRootsOk armOk10.2

/-- **No named callee starts as a `level_queries` specialization**, by the kernel over `osKindTable`. -/
theorem osKindTable_notLq : ∀ e ∈ osKindTable, ¬ HasPre "level_queries__L" e.1 := by decide +kernel

theorem osKindOf_notLq {f : String} {K : OsKind} (h : osKindOf f = some K) : ¬ HasPre "level_queries__L" f :=
  osKindTable_notLq _ (os_mem_of_lookup osKindTable h)

/-- **A named callee is not `level_queries`.** -/
theorem lqNameB_of_kind {g : String} {K : OsKind} (h : osKindOf g = some K) : lqNameB g = false :=
  List.any_eq_false.mpr fun e he hg ↦ osKindOf_notLq h (beq_iff_eq.mp hg ▸ lqTable_hasPre e he)

/-- **`level_positions` is not `level_queries`.** -/
theorem lqNameB_of_lp {g : String} {x : String × ℕ × ℕ} (he : (g, x) ∈ lpTable) : lqNameB g = false :=
  any_name_eq_false apart_pos_queries (lpTable_hasPre _ he) lqTable_hasPre

/-- **`level_residual` is not `level_queries`.** -/
theorem lqNameB_of_lr {g : String} {x : ℕ × ℕ × ℕ × String × String} (he : (g, x) ∈ lrTable) :
    lqNameB g = false :=
  any_name_eq_false apart_res_queries (lrTable_hasPre _ he) lqTable_hasPre

end
end LeanVM.Guest.B1.Arm
