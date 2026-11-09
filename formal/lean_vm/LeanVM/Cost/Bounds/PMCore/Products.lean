module

public import LeanVM.Cost.Extractor.PMEval
public import LeanVM.Cost.Bounds.PMBasis.Defs

/-!
# The PM-basis's matrices: degree and size bounds

`DegLe M d`: every entry of `M` of degree at most `d`, the form of the product lemmas'
hypotheses (`Bounds/PMFFT/EvalCost.lean`: `mulEvalPC_cost`, `mulTruncEvalPC_cost`); `SizeLe M D`:
every entry of at most `D` coefficients.
-/

namespace LeanVM.Cost.Bounds.PMCore

open LeanVM.Cost LeanVM.Cost.Extractor LeanVM.Parameters LeanVM.Cost.Bounds.PMBasis
open CompPoly CompPoly.PolynomialMatrix

public section

/-- Every entry of `M` has degree at most `d`. -/
@[expose] def DegLe (M : PolynomialMatrix K) (d : ℕ) : Prop :=
  ∀ i j, (rowGet (M.getD i #[]) j).natDegree ≤ d

/-- Every entry of `M` has at most `D` coefficients. -/
@[expose] def SizeLe (M : PolynomialMatrix K) (D : ℕ) : Prop :=
  ∀ i j, (rowGet (M.getD i #[]) j).val.size ≤ D

end

end LeanVM.Cost.Bounds.PMCore
