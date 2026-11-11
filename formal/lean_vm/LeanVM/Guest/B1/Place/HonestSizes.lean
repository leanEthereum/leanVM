/-
  LeanVM.Guest.B1.Place.HonestSizes

  Every arm's buffers fit its rows at every rate, decided.
-/

module

public import LeanVM.Guest.B1.Whir.BrMemL
public import LeanVM.Guest.B1.Whir.RateCfg
public import LeanVM.Guest.B1.Place.OsBos
public import LeanVM.Guest.B1.Opening.Meaning

/-!
# The arms' sizes, decided

`osSizesB c` checks `OsSizes c` (each level's row of `basis_d` within its stride, its query
positions within its slots of `query_positions`, the final message's log within its cap) and that
each level's row weights fit `LIG_MAX_INTERLEAVE` (`rowLo il + il / rowLo il ≤ maxIl`, the
weights `opening_queries` reads). `osSizesB_sound` turns it into the propositions;
`osSizesB_all` decides it at every arm below `osArms` and every rate below `4`.
-/

namespace LeanVM.Guest.B1

open LeanVM.Guest.B1.Whir

@[expose] public section

/-- `OsSizes c` and the row weights' fit, checked. -/
def osSizesB (c : OsCfg) : Bool :=
  (List.range c.levels.length).all (fun i ↦
    decide ((lvAt c i).logCols ≤ ligColsCap) &&
    decide ((lvAt c i).posOff + (lvAt c i).squeezes * (192 / (lvAt c i).depth) ≤
      if i + 1 < c.levels.length then (lvAt c (i + 1)).posOff else c.levels.length * ligPosCap) &&
    decide (rowLo (lvAt c i).interleave + (lvAt c i).interleave / rowLo (lvAt c i).interleave ≤
      c.maxIl)) &&
  decide (c.yrLog ≤ yrLogCap)

/-- **The check's meaning.** -/
theorem osSizesB_sound {c : OsCfg} (h : osSizesB c = true) :
    OsSizes c ∧ ∀ i < c.levels.length,
      rowLo (lvAt c i).interleave + (lvAt c i).interleave / rowLo (lvAt c i).interleave ≤ c.maxIl := by
  simp only [osSizesB, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range] at h
  obtain ⟨hl, hy⟩ := h
  exact ⟨⟨fun i hi ↦ (hl i hi).1.1, hy, fun i hi ↦ (hl i hi).1.2⟩, fun i hi ↦ (hl i hi).2⟩

/-- **Every arm's sizes, at every rate.** -/
theorem osSizesB_all : ∀ m < osArms, ∀ ri < 4, osSizesB (osCfgR m ri) = true := by
  decide +kernel

end
end LeanVM.Guest.B1
