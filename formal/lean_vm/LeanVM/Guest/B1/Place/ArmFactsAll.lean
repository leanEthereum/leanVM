/-
  LeanVM.Guest.B1.Place.ArmFactsAll

  open_stacked's per-arm, per-rate decided facts, by name.
-/

module

public import LeanVM.Guest.B1.Place.ArmFactsDec

/-!
# The arms' facts

`os_arm_facts`: every arm's `OsArmFacts` at every rate. Then, at every arm below `osArms` and rate
below `4`, at `osCfgR m ri`: the frames' shapes (`os_kid_shapes`), and of each level `l` the query
positions' slot (`os_posOff`, `os_posCap`, `os_posEnd`), the positions a squeeze gives
(`os_perSq_pos`, `os_queries_le_sq`), the cap's depth (`os_capDepth_le`) and the row weights' fit
(`os_rowLo_fit`, from `osSizesB_all`).
-/

namespace LeanVM.Guest.B1

open LeanVM.Guest.B1.Whir

@[expose] public section

/-- **Every arm's decided facts, at every rate.** -/
theorem os_arm_facts : os_arm_facts_Spec := fun m hm ri hri ↦
  osArmFacts_of hm (armData_all m hm) (armBody_all m hm) (armRate_all m hm ri hri)
    (osSizesB_all m hm ri hri) lpNodup

/-- **The frames' shapes**, at every arm and rate. -/
theorem os_kid_shapes : ∀ m < osArms, ∀ ri < 4, OsKidShapes (osCfgR m ri) := fun m hm ri hri ↦
  (kidShapes_all m hm ri hri).out

theorem os_lvArm {m ri : ℕ} (hm : m < osArms) (hri : ri < 4) {l : ℕ}
    (hl : l < (osCfgR m ri).levels.length) : LvArm (osCfgR m ri) l :=
  ((armRate_all m hm ri hri).2.1 l hl).out

/-- Level `l`'s first query position slot. -/
theorem os_posOff : ∀ m < osArms, ∀ ri < 4, ∀ l < (osCfgR m ri).levels.length,
    (lvAt (osCfgR m ri) l).posOff = l * ligPosCap := fun _ hm _ hri _ hl ↦ (os_lvArm hm hri hl).posOff

/-- The query positions' slots fit a word. -/
theorem os_posCap : ∀ m < osArms, ∀ ri < 4, (osCfgR m ri).levels.length * ligPosCap < 2 ^ 64 - 1 :=
  fun m hm ri hri ↦ (armRate_all m hm ri hri).2.2.2.2

/-- A squeeze gives a position. -/
theorem os_perSq_pos : ∀ m < osArms, ∀ ri < 4, ∀ l < (osCfgR m ri).levels.length,
    0 < 192 / (lvAt (osCfgR m ri) l).depth := fun _ hm _ hri _ hl ↦ (os_lvArm hm hri hl).perSq

/-- The squeezes give every query's position. -/
theorem os_queries_le_sq : ∀ m < osArms, ∀ ri < 4, ∀ l < (osCfgR m ri).levels.length,
    (lvAt (osCfgR m ri) l).queries ≤
      (lvAt (osCfgR m ri) l).squeezes * (192 / (lvAt (osCfgR m ri) l).depth) :=
  fun _ hm _ hri _ hl ↦ (os_lvArm hm hri hl).qSq

/-- The cap lies within the tree. -/
theorem os_capDepth_le : ∀ m < osArms, ∀ ri < 4, ∀ l < (osCfgR m ri).levels.length,
    (lvAt (osCfgR m ri) l).capDepth ≤ (lvAt (osCfgR m ri) l).depth :=
  fun _ hm _ hri _ hl ↦ (os_lvArm hm hri hl).capD

/-- The queries' positions lie within the slots. -/
theorem os_posEnd : ∀ m < osArms, ∀ ri < 4, ∀ l < (osCfgR m ri).levels.length,
    (lvAt (osCfgR m ri) l).posOff + (lvAt (osCfgR m ri) l).queries ≤
      (osCfgR m ri).levels.length * ligPosCap := fun _ hm _ hri _ hl ↦ (os_lvArm hm hri hl).posEnd

/-- The row weights fit `LIG_MAX_INTERLEAVE`. -/
theorem os_rowLo_fit : ∀ m < osArms, ∀ ri < 4, ∀ l < (osCfgR m ri).levels.length,
    rowLo (lvAt (osCfgR m ri) l).interleave +
      (lvAt (osCfgR m ri) l).interleave / rowLo (lvAt (osCfgR m ri) l).interleave ≤
        (osCfgR m ri).maxIl := fun m hm ri hri ↦ (osSizesB_sound (osSizesB_all m hm ri hri)).2

end
end LeanVM.Guest.B1
