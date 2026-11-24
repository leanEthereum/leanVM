/-
  LeanVM.Guest.B1.Place.ArmSlow

  The facts of `open_stacked`'s dispatches into `level_residual_slow`, by kernel evaluation.
-/

module

public import LeanVM.Guest.B1.Place.ArmData
public import LeanVM.Guest.B1.Place.ArmXT
public import LeanVM.Guest.B1.Place.ArmMuteDef
public import LeanVM.Guest.B1.Place.NamePre

/-!
# The slow residuals' facts

`SlowFacts c`: the tail challenges within `yrLogCap`, and at each non-final level its fold
challenges within `fold_challenges` and its `level_residual_slow` neither `armExactS` nor a name of
`lqTable`. `armSlow_ok`: every arm at every rate, its numbers from `slowFactsB` by kernel evaluation,
its names by their prefixes (`Place/NamePre`).
-/

namespace LeanVM.Guest.B1.Arm

open LeanVM.Guest.B1.Whir

@[expose] public section

/-- The facts of an arm's dispatches into `level_residual_slow`. -/
abbrev SlowFacts (c : OsCfg) : Prop :=
  c.yrLog ≤ yrLogCap ∧ ∀ l < c.yrLevel, (osLvA c l).resFoldOff + (osLvA c l).prefixLen ≤ c.nFolds ∧
    armExactS (osSlowName c (osLvA c l)) = false ∧ lqNameB (osSlowName c (osLvA c l)) = false

/-- `SlowFacts`' numbers, checked: its names hold at every configuration (`slowName_not_exact`,
`slowName_not_lq`). -/
def slowFactsB (c : OsCfg) : Bool :=
  decide (c.yrLog ≤ yrLogCap) && (List.range c.yrLevel).all fun l ↦
    decide ((osLvA c l).resFoldOff + (osLvA c l).prefixLen ≤ c.nFolds)

/-- Every arm, every rate, by the kernel. -/
theorem slowFacts_all : ∀ m < 11, ∀ ri < 4, slowFactsB (osCfgR m ri) = true := by decide +kernel

/-- A `level_residual_slow` specialization is neither `is_zero` nor `level_positions`. -/
theorem slowName_not_exact (c : OsCfg) (lv : OsLv) : armExactS (osSlowName c lv) = false := by
  have hz : Apart "level_residual_slow__L" "is_zero" := by decide +kernel
  have h1 : (osSlowName c lv == "is_zero") = false :=
    beq_eq_false_iff_ne.mpr (ne_of_hasPre hz (osSlowName_hasPre c lv) (List.prefix_refl _))
  simp only [armExactS, h1, any_name_eq_false apart_slow_pos (osSlowName_hasPre c lv) lpTable_hasPre,
    Bool.or_false]

/-- A `level_residual_slow` specialization is not `level_queries`. -/
theorem slowName_not_lq (c : OsCfg) (lv : OsLv) : lqNameB (osSlowName c lv) = false :=
  any_name_eq_false apart_slow_queries (osSlowName_hasPre c lv) lqTable_hasPre

/-- **Every arm's dispatches into `level_residual_slow` have their facts at every rate.** -/
theorem armSlow_ok {m ri : ℕ} (hm : m < 11) (hri : ri < 4) : SlowFacts (osCfgR m ri) := by
  have h := slowFacts_all m hm ri hri
  simp only [slowFactsB, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range] at h
  exact ⟨h.1, fun l hl ↦ ⟨h.2 l hl, slowName_not_exact _ _, slowName_not_lq _ _⟩⟩

end
end LeanVM.Guest.B1.Arm
