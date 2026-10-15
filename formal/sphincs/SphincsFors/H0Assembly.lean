import SphincsFors.H0Majorant
import SphincsBase.Proof.Base.BinomialMoments

/-! The count price `Z(D) = Σ_l κ cnt_l^24` of a multiset of views, generic in the view type, and
the Touchard polynomials `T_n(μ) = E[Poisson(μ)^n]`. -/

open ENNReal

namespace SphincsFors.Security.H0

open Domination

set_option linter.unusedSectionVars false

variable {V ι : Type} [DecidableEq ι] [Fintype ι] (idx : V → ι)

/-- The count price `Σ_l κ cnt_l^24`. -/
noncomputable def countPrice (κ : ℝ≥0∞) (d : Multiset V) : ℝ≥0∞ := ∑ l, κ * (cnt idx d l : ℝ≥0∞) ^ 24

/-- Touchard polynomial `T_n(μ) = E[Poisson(μ)^n]`. -/
noncomputable def touchard (n : ℕ) (μ : ℝ≥0∞) : ℝ≥0∞ :=
  ∑ j ∈ Finset.range (n + 1), (Nat.stirlingSecond n j : ℝ≥0∞) * μ ^ j

end SphincsFors.Security.H0
