module

public import LeanVM.Cost.FastLib
import all CompPoly.LinearAlgebra.PolynomialMatrix.Shifted
import all CompPoly.LinearAlgebra.PolynomialMatrix.Basic
import all CompPoly.Univariate.Basic

/-!
# Rewrites for the extractor's compilation

Equations through which the compiler compiles CompPoly's definitions (CompPoly:
github.com/Verified-zkEVM/CompPoly, Apache-2.0, "Copyright (c) 2026 CompPoly Contributors";
compiled, not copied), each proved:

* `shiftedEntryDegree?_eq`: an entry's shifted degree tests the entry for zero by its size (one
  word operation), not by `==` on polynomials, which the compiler otherwise reaches through the
  arrays' `==` (`Rewrite.arrBEq`): the coefficients listed and compared with the empty list,
  `O(|p|)` for every entry, at every shifted-degree read of a row (a factor of the entries' size
  on the cost of the rows' leading positions).
-/

namespace LeanVM.Cost.ExtractorRewrites

open LeanVM.Cost CompPoly CompPoly.PolynomialMatrix

public section

theorem shiftedEntryDegree?_eq {F : Type} [Zero F] [BEq F] (row : PolynomialRow F)
    (shift : Array ℕ) (j : ℕ) :
    shiftedEntryDegree? row shift j =
      if (rowGet row j).val.size = 0 then none
      else some ((rowGet row j).natDegree + shift.getD j 0) := by
  unfold shiftedEntryDegree?
  simp only [CompPolyLib.beqZero, decide_eq_true_eq]

cost_rewrite shiftedEntryDegree?_eq

end

end LeanVM.Cost.ExtractorRewrites
