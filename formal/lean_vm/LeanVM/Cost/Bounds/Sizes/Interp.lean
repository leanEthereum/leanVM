module

public import LeanVM.Cost.Bounds.PolyDegrees
public import LeanVM.Cost.Bounds.Sizes.Lane
public import LeanVM.Protocol.Extraction.Fast.LeeRows
import all CompPoly.Univariate.Basic

/-!
# Sizes along the decoder: the interpolation's polynomials

The sizes of `G` and `R`, the vanishing and the interpolating polynomials of a lane's
interpolation (`vanishingFast`, `interpolateCoefficientFormWithVanishing` by Horner's
evaluations), on `n` points:

* the vanishing polynomial `G` has degree at most `n`, so at most `n + 1` coefficients
  (`vanishingFast_natDegree_le`, `vanishingFast_size_le`); the interpolating polynomial `R` degree
  at most `deg G − 1`, so at most `max 1 n` coefficients (`interpolate_natDegree_le_pred`,
  `interpolate_size_le`).
-/

namespace LeanVM.Cost.Bounds

open CompPoly CompPoly.GuruswamiSudan CompPoly.PolynomialMatrix LeanVM.Extraction.Fast
open LeanVM.Extraction LeanVM.Parameters

open LeanVM.Extraction.Fast.PMDegree (val_size_le_natDegree_add_one)

public section

variable {F : Type*} [Field F] [BEq F] [LawfulBEq F] [DecidableEq F]

/-! ## The vanishing and interpolating polynomials -/

omit [DecidableEq F] in
theorem vanishingFast_natDegree_le (xs : Array F) : (vanishingFast xs).natDegree ≤ xs.size := by
  rw [vanishingFast_eq]; exact natDegree_vanishingPolynomialArray xs

omit [DecidableEq F] in
/-- **The vanishing polynomial of `n` points has at most `n + 1` coefficients.** -/
theorem vanishingFast_size_le (xs : Array F) : (vanishingFast xs).val.size ≤ xs.size + 1 :=
  (val_size_le_natDegree_add_one _).trans (Nat.add_le_add_right (vanishingFast_natDegree_le xs) 1)

omit [DecidableEq F] in
theorem natDegree_divByLinearFactor_le_pred (p : CPolynomial F) (x : F) :
    (CPolynomial.divByLinearFactor p x).natDegree ≤ p.natDegree - 1 := by
  have htp : (CPolynomial.linearFactor x).toPoly = Polynomial.X + Polynomial.C (-x) := by
    rw [CPolynomial.linearFactor, CPolynomial.toPoly_add, CPolynomial.C_toPoly,
      CPolynomial.X_toPoly, add_comm]
  have hmonic : (CPolynomial.linearFactor x).monic := by
    rw [CPolynomial.monic_toPoly_iff, htp]
    exact Polynomial.monic_X_add_C _
  rw [CPolynomial.divByLinearFactor_eq_divByMonic, CPolynomial.natDegree_toPoly,
    CPolynomial.divByMonic_toPoly_eq_divByMonic _ _ hmonic,
    Polynomial.natDegree_divByMonic _ ((CPolynomial.monic_toPoly_iff _).1 hmonic), htp,
    Polynomial.natDegree_X_add_C, ← CPolynomial.natDegree_toPoly]

/-- **The interpolating polynomial has degree at most `deg G − 1`.** -/
theorem interpolate_natDegree_le_pred (E : CPolynomial.BatchEvalContext F) (G : CPolynomial F)
    (points : Array (F × F)) :
    (CPolynomial.interpolateCoefficientFormWithVanishing E G points).natDegree ≤
      G.natDegree - 1 := by
  rw [CPolynomial.interpolateCoefficientFormWithVanishing]
  generalize (E.evalBatchWith _ _) = dv
  have h : ∀ (l : List ℕ) (acc : CPolynomial F), acc.natDegree ≤ G.natDegree - 1 →
      (l.foldl (fun acc i ↦ acc + CPolynomial.interpolationTermWithVanishing G
        (points.getD i (0, 0)) (dv.getD i 0)) acc).natDegree ≤ G.natDegree - 1 := by
    intro l
    induction l with
    | nil => intro acc h; exact h
    | cons i l ih =>
      intro acc hacc
      refine ih _ ((CPolynomial.natDegree_add_le _ _).trans (max_le hacc ?_))
      rw [CPolynomial.interpolationTermWithVanishing]
      refine (CPolynomial.natDegree_mul_le _ _).trans ?_
      rw [CPolynomial.natDegree_C, Nat.zero_add]
      exact natDegree_divByLinearFactor_le_pred G _
  exact h _ 0 (by rw [CPolynomial.natDegree_toPoly, CPolynomial.toPoly_zero]; simp)

/-- **The interpolating polynomial of `n` points has at most `max 1 n` coefficients.** -/
theorem interpolate_size_le (E : CPolynomial.BatchEvalContext F) (points : Array (F × F)) :
    (CPolynomial.interpolateCoefficientFormWithVanishing E
      (vanishingFast (points.map fun p ↦ p.1)) points).val.size ≤ max 1 points.size := by
  have h1 := interpolate_natDegree_le_pred E (vanishingFast (points.map fun p ↦ p.1)) points
  have h2 := vanishingFast_natDegree_le (points.map fun p ↦ p.1)
  have h3 := val_size_le_natDegree_add_one
    (CPolynomial.interpolateCoefficientFormWithVanishing E
      (vanishingFast (points.map fun p ↦ p.1)) points)
  simp only [Array.size_map] at h2
  omega

/-! ## Lee–O'Sullivan's rows -/

/-! ## The normalization -/

omit [DecidableEq F] in
theorem ofFn_size_le {R : Type*} [Zero R] [BEq R] [LawfulBEq R] {n : ℕ} (f : Fin n → R) :
    (CPolynomial.ofFn f).val.size ≤ n :=
  cpoly_val_size_le_of_coeff _ n fun i hi ↦ by
    rw [CPolynomial.coeff_ofFn]
    simp [show ¬ i < n by omega]

end

end LeanVM.Cost.Bounds
