/-
  LeanVM.Guest.B1.Place.ArmSlow

  The facts of `open_stacked`'s dispatches into `level_residual_slow`, by kernel evaluation.
-/

module

public import LeanVM.Guest.B1.Place.ArmData
public import LeanVM.Guest.B1.Place.ArmXT
public import LeanVM.Guest.B1.Place.ArmMuteDef

/-!
# The slow residuals' facts

`SlowFacts c`: the tail challenges within `yrLogCap`, and at each non-final level its fold
challenges within `fold_challenges` and its `level_residual_slow` neither `armExactS` nor a name of
`lqTable`. `armSlow_ok`: every arm at every rate, by kernel evaluation.
-/

namespace LeanVM.Guest.B1.Arm

open LeanVM.Guest.B1.Whir

@[expose] public section

/-- The facts of an arm's dispatches into `level_residual_slow`. -/
abbrev SlowFacts (c : OsCfg) : Prop :=
  c.yrLog ≤ yrLogCap ∧ ∀ l < c.yrLevel, (osLvA c l).resFoldOff + (osLvA c l).prefixLen ≤ c.nFolds ∧
    armExactS (osSlowName c (osLvA c l)) = false ∧ lqNameB (osSlowName c (osLvA c l)) = false

set_option maxRecDepth 100000 in
theorem armSlow_0 : ∀ ri < 4, SlowFacts (osCfgR 0 ri) := by decide +kernel

set_option maxRecDepth 100000 in
theorem armSlow_1 : ∀ ri < 4, SlowFacts (osCfgR 1 ri) := by decide +kernel

set_option maxRecDepth 100000 in
theorem armSlow_2 : ∀ ri < 4, SlowFacts (osCfgR 2 ri) := by decide +kernel

set_option maxRecDepth 100000 in
theorem armSlow_3 : ∀ ri < 4, SlowFacts (osCfgR 3 ri) := by decide +kernel

set_option maxRecDepth 100000 in
theorem armSlow_4 : ∀ ri < 4, SlowFacts (osCfgR 4 ri) := by decide +kernel

set_option maxRecDepth 100000 in
theorem armSlow_5 : ∀ ri < 4, SlowFacts (osCfgR 5 ri) := by decide +kernel

set_option maxRecDepth 100000 in
theorem armSlow_6 : ∀ ri < 4, SlowFacts (osCfgR 6 ri) := by decide +kernel

set_option maxRecDepth 100000 in
theorem armSlow_7 : ∀ ri < 4, SlowFacts (osCfgR 7 ri) := by decide +kernel

set_option maxRecDepth 100000 in
theorem armSlow_8 : ∀ ri < 4, SlowFacts (osCfgR 8 ri) := by decide +kernel

set_option maxRecDepth 100000 in
theorem armSlow_9 : ∀ ri < 4, SlowFacts (osCfgR 9 ri) := by decide +kernel

set_option maxRecDepth 100000 in
theorem armSlow_10 : ∀ ri < 4, SlowFacts (osCfgR 10 ri) := by decide +kernel

/-- **Every arm's dispatches into `level_residual_slow` have their facts at every rate.** -/
theorem armSlow_ok {m ri : ℕ} (hm : m < 11) (hri : ri < 4) : SlowFacts (osCfgR m ri) := by
  interval_cases m
  · exact armSlow_0 ri hri
  · exact armSlow_1 ri hri
  · exact armSlow_2 ri hri
  · exact armSlow_3 ri hri
  · exact armSlow_4 ri hri
  · exact armSlow_5 ri hri
  · exact armSlow_6 ri hri
  · exact armSlow_7 ri hri
  · exact armSlow_8 ri hri
  · exact armSlow_9 ri hri
  · exact armSlow_10 ri hri

end
end LeanVM.Guest.B1.Arm
