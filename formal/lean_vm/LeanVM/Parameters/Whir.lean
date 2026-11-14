/-
  LeanVM.Parameters.Whir

  The structure of leanVM's WHIR parameters (`Statement.LeanVmVerifier`): every admissible stack
  size and rate has a ladder, one level per tabulated query count, and its blocks fit.
-/

module

public import Statement.LeanVmVerifier
public import LeanVM.Facts.Verifier
public import Statement.Fast.Keccak
public import Statement.Fast.QuadExt
public import Statement.Fast.FieldWords

/-!
# The structure of the WHIR parameters

The parameters are defined with the verifier that reads them, in `Statement.LeanVmVerifier` (Part
1). This module proves what the proofs need of them: the folds and reductions are ordered, and on
the 60 admissible pairs of stack size and rate the ladder exists (`ladder_isSome`), has one level
per tabulated query count, and leaves a residual of at most `residualMaxLog` variables.
-/

namespace LeanVM.Parameters.Whir

@[expose] public section

/-! ## Structure of the table

Each fact below is decided over the 60 admissible pairs; the general statement follows by
bounding the quantifiers. -/

private theorem admissible_bounded {μ logInvRate : ℕ} (h : Admissible μ logInvRate) :
    μ < maxLogStack + 1 ∧ logInvRate < 5 := by
  obtain ⟨_, h2, _, h4⟩ := h
  exact ⟨Nat.lt_succ_of_le h2, Nat.lt_succ_of_le h4⟩

/-- The table has one query count per level of the geometry: `ladder` is defined on the whole
window. -/
theorem ladder_isSome {μ logInvRate : ℕ} (h : Admissible μ logInvRate) :
    (ladder μ logInvRate).isSome := by
  have key : ∀ μ < maxLogStack + 1, ∀ r < 5, Admissible μ r → (ladder μ r).isSome :=
    by decide +kernel
  obtain ⟨h1, h2⟩ := admissible_bounded h
  exact key μ h1 logInvRate h2 h

end
end LeanVM.Parameters.Whir
