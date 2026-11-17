/-
  LeanVM.Protocol.Whir.Params.DescentCheck

  At every admissible shape, every round's threshold of every level is at least the level's degree
  plus three, so the descent's near tuples are unique.
-/

module

public import LeanVM.Protocol.Whir.Params.Deployed

/-!
# The descent's thresholds

The agreement-set extractor decodes, at each round going back, the near tuple of the unfolded
word on an agreement set of at least the round's threshold; near tuples are unique on at least
`d + 3` columns (`Sound.nearT_unique`). `descentOK` checks, for every level of a shape,
`d + 3 ≤ thr 1 = A − (k − 1)`, the smallest threshold of a round, and `descentOK_all` that every
admissible shape passes. `codesOf_thr` reads it on the codes.
-/

namespace LeanVM.Protocol.Whir.Params

open LeanVM.Parameters LeanVM.Protocol.Whir LeanVM.Protocol.Whir.Sound

@[expose] public section

/-- **The descent's check of a shape**: every level's degree plus three is at most its first
round's threshold. -/
def descentOK (μ R : ℕ) : Bool :=
  (levelsOf μ R).all fun lv ↦ decide (degOf lv + 3 + lv.2.2.1 ≤ lv.2.2.2.1 + 1)

/-- **Every admissible shape passes.** -/
theorem descentOK_all : ∀ μ < Whir.maxLogStack + 1, ∀ R < 5, Whir.Admissible μ R →
    descentOK μ R = true := by
  decide +kernel

/-- **Every round's threshold is at least the level's degree plus three**, at every admissible
shape. -/
theorem codesOf_thr {μ R : ℕ} (h : Whir.Admissible μ R) (i j : ℕ) (h1 : 1 ≤ j)
    (h2 : j ≤ (codesOf μ R i).ℓ) : (codesOf μ R i).deg + 3 ≤ (codesOf μ R i).thr j := by
  have hok := descentOK_all μ (Nat.lt_succ_of_le h.2.1) R (Nat.lt_succ_of_le h.2.2.2) h
  unfold codesOf at h2 ⊢
  rcases lt_or_ge i (levelsOf μ R).length with hi | hi
  · rw [List.getD_eq_getElem _ _ hi] at h2 ⊢
    have hlv := List.all_eq_true.mp hok _ (List.getElem_mem hi)
    simp only [decide_eq_true_eq] at hlv
    set lv := (levelsOf μ R)[i]
    by_cases hm : lv.1 + lv.2.1 ≤ 64 ∧ 1 ≤ lv.2.1
    · rw [mkCode_eq hm] at h2 ⊢
      simp only [LevelCode.deg, LevelCode.thr] at h2 ⊢
      unfold degOf at hlv
      omega
    · simp only [mkCode, hm, ↓reduceDIte] at h2
      omega
  · rw [List.getD_eq_default _ _ hi] at h2
    simp [mkCode, junkLv] at h2
    omega

end
end LeanVM.Protocol.Whir.Params
