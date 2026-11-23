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
`lqTable`. `armSlow_ok`: every arm at every rate, from `slowFactsB` by kernel evaluation.
-/

namespace LeanVM.Guest.B1.Arm

open LeanVM.Guest.B1.Whir

@[expose] public section

/-- The facts of an arm's dispatches into `level_residual_slow`. -/
abbrev SlowFacts (c : OsCfg) : Prop :=
  c.yrLog ≤ yrLogCap ∧ ∀ l < c.yrLevel, (osLvA c l).resFoldOff + (osLvA c l).prefixLen ≤ c.nFolds ∧
    armExactS (osSlowName c (osLvA c l)) = false ∧ lqNameB (osSlowName c (osLvA c l)) = false

/-- `SlowFacts`, checked. -/
def slowFactsB (c : OsCfg) : Bool :=
  decide (c.yrLog ≤ yrLogCap) && (List.range c.yrLevel).all fun l ↦
    decide ((osLvA c l).resFoldOff + (osLvA c l).prefixLen ≤ c.nFolds) &&
      !armExactS (osSlowName c (osLvA c l)) && !lqNameB (osSlowName c (osLvA c l))

/-- Every arm, every rate, by the kernel. -/
theorem slowFacts_all : ∀ m < 11, ∀ ri < 4, slowFactsB (osCfgR m ri) = true := by decide +kernel

/-- **Every arm's dispatches into `level_residual_slow` have their facts at every rate.** -/
theorem armSlow_ok {m ri : ℕ} (hm : m < 11) (hri : ri < 4) : SlowFacts (osCfgR m ri) := by
  have h := slowFacts_all m hm ri hri
  simp only [slowFactsB, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range,
    Bool.not_eq_true'] at h
  exact ⟨h.1, fun l hl ↦ ⟨(h.2 l hl).1.1, (h.2 l hl).1.2, (h.2 l hl).2⟩⟩

end
end LeanVM.Guest.B1.Arm
