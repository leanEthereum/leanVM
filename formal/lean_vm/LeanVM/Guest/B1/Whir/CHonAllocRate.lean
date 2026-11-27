/-
  LeanVM.Guest.B1.Whir.CHonAllocRate

  The body's allocation statements are the same at every rate.
-/

module

public import LeanVM.Guest.B1.Whir.CHonAlloc
public import LeanVM.Guest.B1.Whir.RateFree

/-!
# The allocations at every rate

A rate changes a level's rate columns alone, and the head, the levels' states, each level's
statements, the closing rounds and `lvAllocsV` read only the levels' rate-free columns (`OsLv.rf`,
`Whir/RateFree`): `bodyAllocs_rf`, at any two level lists with the same rate-free columns, and
`bodyAllocs_rate`, a size's allocations at rate `ri` are its allocations at the first rate.
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Guest.Core LeanVM.Guest

@[expose] public section

section
variable (c : OsCfg) {L L' : List OsLv} (h : L.map OsLv.rf = L'.map OsLv.rf)
include h

theorem length_eq_of_rf : L.length = L'.length := by simpa using congrArg List.length h

theorem getD_rf_eq (i : ℕ) : (L.getD i default).rf = (L'.getD i default).rf := by
  rw [← getD_rf, ← getD_rf, h]

theorem take_rf_eq (l : ℕ) : (L.take l).map OsLv.rf = (L'.take l).map OsLv.rf := by
  rw [List.map_take, List.map_take, h]

theorem osHead_rf : osHead (c.withLevels L) = osHead (c.withLevels L') := by
  have h2 : ∀ i, (L.getD i default).folds = (L'.getD i default).folds := fun i ↦ by
    rw [← OsLv.rf_folds, getD_rf_eq h i, OsLv.rf_folds]
  simp only [osHead, length_eq_of_rf h, h2]

theorem osStAt_rf (l : ℕ) : osStAt (c.withLevels L) l = osStAt (c.withLevels L') l := by
  simp only [osStAt, osStFrom, osLevels_wl, osHead_rf c h]
  simp only [OsCfg.withLevels, take_rf_eq h]

theorem osLvsEnd_rf : osLvsEnd (c.withLevels L) = osLvsEnd (c.withLevels L') := by
  simp only [osLvsEnd, osLevels_wl, osHead_rf c h]
  simp only [OsCfg.withLevels, h]

theorem osLevelAt_rf (l : ℕ) :
    osLevel (c.withLevels L) l ((c.withLevels L).levels.getD l default) (osStAt (c.withLevels L) l) =
    osLevel (c.withLevels L') l ((c.withLevels L').levels.getD l default) (osStAt (c.withLevels L') l) := by
  rw [osLevel_wl c L, osLevel_wl c L', osStAt_rf c h]
  simp only [OsCfg.withLevels, getD_rf_eq h]

theorem lvAllocsV_rf (l : ℕ) : lvAllocsV (c.withLevels L) l = lvAllocsV (c.withLevels L') l := by
  have e1 : ∀ i, (L.getD i default).folds = (L'.getD i default).folds := fun i ↦ by
    rw [← OsLv.rf_folds, getD_rf_eq h i, OsLv.rf_folds]
  have e2 : ∀ i, (L.getD i default).foldsOff = (L'.getD i default).foldsOff := fun i ↦ by
    rw [← OsLv.rf_foldsOff, getD_rf_eq h i, OsLv.rf_foldsOff]
  simp only [lvAllocsV, osRates_wl, osFinalMsg_wl, osPositions_wl, osStAt_rf c h]
  simp only [OsCfg.withLevels, e1, e2, getD_rf_eq h]

omit h in
theorem osTail_wl (s : OsSt) : osTail (c.withLevels L) s = osTail c s := rfl

/-- **The allocations read the levels' rate-free columns alone.** -/
theorem bodyAllocs_rf : BodyAllocs (c.withLevels L) ↔ BodyAllocs (c.withLevels L') := by
  have hl : (c.withLevels L).levels.length = (c.withLevels L').levels.length := length_eq_of_rf h
  unfold BodyAllocs
  rw [osHead_rf c h, osLvsEnd_rf c h, hl, osTail_wl c (L := L), osTail_wl c (L := L')]
  simp only [osLevelAt_rf c h, lvAllocsV_rf c h]

end

/-- **A size's allocations at any rate are its allocations at the first.** -/
theorem bodyAllocs_rate (m ri : ℕ) : BodyAllocs (osCfgR m ri) ↔ BodyAllocs (osCfgR m 0) :=
  bodyAllocs_rf (osCfg m) (by simp only [osLevelsR, List.map_map]; rfl)

end
end LeanVM.Guest.B1.Whir
