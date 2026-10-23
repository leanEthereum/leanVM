/-
  LeanVM.Parameters.Whir

  The structure of leanVM's WHIR parameters (`LeanVM.Spec.Verifier`): every admissible stack
  size and rate has a ladder, one level per tabulated query count, and its blocks fit.
-/

module

public import LeanVM.Spec.Verifier

/-!
# The structure of the WHIR parameters

The parameters are defined with the verifier that reads them, in `LeanVM.Spec.Verifier` (Part
1). This module proves what the proofs need of them: the folds and reductions are ordered, and on
the 56 admissible pairs of stack size and rate the ladder exists (`ladder_isSome`), has one level
per tabulated query count, and leaves a residual of at most `residualMaxLog` variables.
-/

namespace LeanVM.Parameters.Whir

@[expose] public section

/-- `whir_config.rs:80`: the first reduction never exceeds the first fold. -/
theorem initialReduction_le_initialFold : initialReduction ≤ initialFold := by decide

/-- `whir_config.rs:81`: a later reduction never exceeds a later fold. -/
theorem subsequentReduction_le_subsequentFold : subsequentReduction ≤ subsequentFold := by
  decide

/-- `whir_config.rs:92`: the residual is never longer than the lane fold. -/
theorem residualMaxLog_le_initialFold : residualMaxLog ≤ initialFold := by decide

/-! ## Structure of the table

Each fact below is decided over the 56 admissible pairs; the general statement follows by
bounding the quantifiers. -/

private theorem admissible_bounded {μ logInvRate : ℕ} (h : Admissible μ logInvRate) :
    μ < maxLogStack + 1 ∧ logInvRate < maxLogInvRate + 1 := by
  obtain ⟨_, h2, _, h4⟩ := h
  exact ⟨Nat.lt_succ_of_le h2, Nat.lt_succ_of_le h4⟩

/-- The table has one query count per level of the geometry: `ladder` is defined on the whole
window. -/
theorem ladder_isSome {μ logInvRate : ℕ} (h : Admissible μ logInvRate) :
    (ladder μ logInvRate).isSome := by
  have key : ∀ μ < maxLogStack + 1, ∀ r < maxLogInvRate + 1, Admissible μ r → (ladder μ r).isSome :=
    by decide +kernel
  obtain ⟨h1, h2⟩ := admissible_bounded h
  exact key μ h1 logInvRate h2 h

/-- Every ladder has at least two levels (`whir_config.rs:281-283`). -/
theorem ladder_length {μ logInvRate : ℕ} (h : Admissible μ logInvRate) :
    ∀ levels, ladder μ logInvRate = some levels → 2 ≤ levels.length := by
  have key : ∀ μ < maxLogStack + 1, ∀ r < maxLogInvRate + 1, Admissible μ r →
      ∀ levels, ladder μ r = some levels → 2 ≤ levels.length := by decide +kernel
  obtain ⟨h1, h2⟩ := admissible_bounded h
  exact key μ h1 logInvRate h2 h

/-- The residual is at most `residualMaxLog` variables. -/
theorem residualLog_le {μ logInvRate : ℕ} (h : Admissible μ logInvRate) :
    residualLog μ logInvRate ≤ residualMaxLog := by
  have key : ∀ μ < maxLogStack + 1, ∀ r < maxLogInvRate + 1, Admissible μ r →
      residualLog μ r ≤ residualMaxLog := by decide +kernel
  obtain ⟨h1, h2⟩ := admissible_bounded h
  exact key μ h1 logInvRate h2 h

/-- Every level's code fits in `K`: its block length is at most `2^64` (Annex B, §B.2 requires
`κ_i + R_i ≤ 64`), and its query count is at most its block length (`whir_config.rs:641`). -/
theorem ladder_blocks {μ logInvRate : ℕ} (h : Admissible μ logInvRate) :
    ∀ levels, ladder μ logInvRate = some levels →
      ∀ p ∈ List.zip (blockLogs μ levels) levels, p.1 ≤ 64 ∧ p.2.queries ≤ 2 ^ p.1 := by
  have key : ∀ μ < maxLogStack + 1, ∀ r < maxLogInvRate + 1, Admissible μ r →
      ∀ levels, ladder μ r = some levels →
        (List.zip (blockLogs μ levels) levels).all
          (fun p ↦ decide (p.1 ≤ 64 ∧ p.2.queries ≤ 2 ^ p.1)) = true := by
    decide +kernel
  obtain ⟨h1, h2⟩ := admissible_bounded h
  intro levels hl p hp
  exact of_decide_eq_true ((List.all_eq_true.mp (key μ h1 logInvRate h2 h levels hl)) p hp)

end
end LeanVM.Parameters.Whir
