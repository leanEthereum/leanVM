module

public import CompPoly.Bivariate.GuruswamiSudan.Interpolation.LeeOSullivan.Correctness
public import CompPoly.Bivariate.ToPoly
public import LeanVM.Protocol.Extraction.Extractor
public import LeanVM.Protocol.Extraction.Fast.PMBasis.DegreeRecursion
import all CompPoly.Univariate.Basic

/-!
# Polynomial degrees and sizes

A canonical polynomial of degree `d` is an array of at most `d + 1` coefficients
(`PMDegree.val_size_le_natDegree_add_one`); the vanishing polynomial of `n` points has degree at
most `n` (`natDegree_vanishingPolynomialArray`): the size of the lanes' `G`.
-/

namespace LeanVM.Cost.Bounds

open CompPoly CompPoly.PolynomialMatrix

public section

variable {F : Type*} [Field F] [BEq F] [LawfulBEq F] [DecidableEq F]

/-! ## The degrees of `G` and `R` -/

omit [DecidableEq F] in
theorem natDegree_one_cpoly : (1 : CPolynomial F).natDegree = 0 := by
  rw [CPolynomial.natDegree_toPoly, CPolynomial.toPoly_one, Polynomial.natDegree_one]

omit [DecidableEq F] in
theorem natDegree_linearFactor (x : F) : (CPolynomial.linearFactor x).natDegree ≤ 1 := by
  rw [CPolynomial.natDegree_toPoly, CPolynomial.linearFactor, CPolynomial.toPoly_add,
    CPolynomial.C_toPoly, CPolynomial.X_toPoly]
  exact (Polynomial.natDegree_add_le _ _).trans
    (max_le (by simp) Polynomial.natDegree_X_le)

omit [DecidableEq F] in
theorem natDegree_foldl_linearFactor (l : List F) (acc : CPolynomial F) :
    (l.foldl (fun acc x ↦ acc * CPolynomial.linearFactor x) acc).natDegree ≤
      acc.natDegree + l.length := by
  induction l generalizing acc with
  | nil => simp
  | cons x l ih =>
    rw [List.foldl_cons, List.length_cons]
    have := (CPolynomial.natDegree_mul_le acc (CPolynomial.linearFactor x)).trans
      (Nat.add_le_add_left (natDegree_linearFactor x) _)
    have := ih (acc * CPolynomial.linearFactor x)
    omega

omit [DecidableEq F] in
/-- **The vanishing polynomial of `n` points has degree at most `n`.** -/
theorem natDegree_vanishingPolynomialArray (xs : Array F) :
    (CPolynomial.vanishingPolynomialArray xs).natDegree ≤ xs.size := by
  rw [CPolynomial.vanishingPolynomialArray, ← Array.foldl_toList]
  have := natDegree_foldl_linearFactor xs.toList 1
  rw [natDegree_one_cpoly, Array.length_toList] at this
  omega

end

end LeanVM.Cost.Bounds
