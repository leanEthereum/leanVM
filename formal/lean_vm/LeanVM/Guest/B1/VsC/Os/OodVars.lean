/-
  LeanVM.Guest.B1.VsC.Os.OodVars

  Every deployed ladder leaves each non-final level's out-of-domain point a variable.
-/

module

public import Statement.LeanVmVerifier

/-!
# The ladders' out-of-domain variables

Restored from `formal-bus-archive`'s `Protocol/EndToEnd/Sound/Moves.lean` (`oodVarsPos`,
`ladder_oodVarsPos`), the only part of it the opening's backwards run takes.
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Parameters LeanVM.Protocol.Verifier

@[expose] public section

/-- Every non-final level of a ladder leaves a variable for its out-of-domain point. -/
def oodVarsPos : ℕ → List Whir.Level → Bool
  | _, [] => true
  | _, [_] => true
  | μ, level :: rest => decide (μ - level.fold ≠ 0) && oodVarsPos (μ - level.fold) rest

/-- `oodVarsPos` of a shape's ladder, `true` where there is none. -/
def oodVarsOK (μ R : ℕ) : Bool :=
  match Whir.ladder μ R with
  | some config => oodVarsPos μ config
  | none => true

theorem oodVarsOK_all : ∀ μ < Whir.maxLogStack + 1, ∀ R < 5, oodVarsOK μ R = true := by
  decide +kernel

/-- **Every deployed ladder leaves its out-of-domain point a variable.** -/
theorem ladder_oodVarsPos {μ R : ℕ} {config : List Whir.Level}
    (h : Whir.ladder μ R = some config) : oodVarsPos μ config = true := by
  have hadm : Whir.Admissible μ R := by
    unfold Whir.ladder at h
    exact Classical.byContradiction fun ha => by simp [ha] at h
  have key := oodVarsOK_all μ (Nat.lt_succ_of_le hadm.2.1) R (Nat.lt_succ_of_le hadm.2.2.2)
  simpa only [oodVarsOK, h] using key

end
end LeanVM.Guest.B1.Whir
