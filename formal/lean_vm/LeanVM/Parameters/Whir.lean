/-
  LeanVM.Parameters.Whir

  The structure of leanVM's WHIR parameters (`Statement.LeanVmVerifier`): every admissible stack
  size and rate has a ladder, one level per tabulated query count, and its blocks fit.
-/

module

public import Statement.LeanVmVerifier
public import LeanVM.Facts.Verifier
public import Statement.Fast.Keccak
public import Statement.Fast.CubicExt
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

/-! ## Parameters no end statement reaches, moved here from the statement -/

/-- Out-of-domain samples taken after a level's commitment: none at level 0, whose commitment the
opening's own evaluation claim binds, and one at every later level (`whir_config.rs:107-114`).
The Rust production test fixes the count for stack sizes 22 to 28 (`whir_config.rs:974, 986`);
for 16 to 21 it is the deployed verifier's, which takes one sample per level after the first
(`crates/verifier/src/whir.rs:174-183`). -/
def oodSamples (level : ℕ) : ℕ := if level = 0 then 0 else 1

/-- The variables left after every fold: the size of the residual sent in the clear. -/
def residualLog (μ logInvRate : ℕ) : ℕ := μ - ((ladderShape μ logInvRate).map Prod.fst).sum

/-- The log block lengths `κ_i + R_i` of the levels' codes: the message log after a level's fold
plus its rate exponent (`LevelShapes.block_len`, `whir_config.rs:121-156`). -/
def blockLogs (μ : ℕ) : List Level → List ℕ
  | [] => []
  | l :: rest => (μ - l.fold + l.logInvRate) :: blockLogs (μ - l.fold) rest

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

/-- Every ladder has at least two levels (`whir_config.rs:281-283`). -/
theorem ladder_length {μ logInvRate : ℕ} (h : Admissible μ logInvRate) :
    ∀ levels, ladder μ logInvRate = some levels → 2 ≤ levels.length := by
  have key : ∀ μ < maxLogStack + 1, ∀ r < 5, Admissible μ r →
      ∀ levels, ladder μ r = some levels → 2 ≤ levels.length := by decide +kernel
  obtain ⟨h1, h2⟩ := admissible_bounded h
  exact key μ h1 logInvRate h2 h

end
end LeanVM.Parameters.Whir
