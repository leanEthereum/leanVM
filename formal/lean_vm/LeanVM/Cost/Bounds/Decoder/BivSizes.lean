module

public import LeanVM.Cost.Bounds.Decoder.Interp
import all CompPoly.Univariate.Raw.Core
import all CompPoly.Univariate.Raw.Ops
import all CompPoly.Univariate.Basic
import all CompPoly.Data.Array.Lemmas
import all CompPoly.Bivariate.GuruswamiSudan.Polynomial
import all CompPoly.Bivariate.FactorMonic
import all CompPoly.Bivariate.CoeffRows

/-!
# Bound: sizes of bivariate polynomials, and `ofArray` over `K[X]`

Facts the decoder's bounds share: a trimmed bivariate polynomial keeps its entries' bound
(`InnerLe.trim`), the sizes of a constant, a negation and `1` (`size_C_le`, `neg_val_size`,
`size_one_K`), and the price of `ofArray` over `K[X]` (`ofArrayB_cost`).
-/

namespace LeanVM.Cost.Bounds.Decoder

open LeanVM.Cost LeanVM.Cost.Bounds LeanVM.Cost.Library
open LeanVM.Cost.Extractor LeanVM.Parameters CompPoly LeanVM.Extraction.Fast

/-! The functions compiled on demand, by their short names. -/
open LeanVM.Cost.Auto.CompPoly.CPolynomial.Raw

open LeanVM.Extraction.Fast.PMDegree (val_size_le_natDegree_add_one)

public section

variable (P : MachineProgram)

theorem InnerLe.trim {p : CPolynomial.Raw (CPolynomial K)} {A : ℕ} (h : InnerLe p A) :
    InnerLe p.trim A := by
  intro x hx
  rw [CompPolyLib.trim_eq] at hx
  obtain ⟨j, hj, rfl⟩ := Array.getElem_of_mem hx
  rw [Array.getElem_extract]
  exact h _ (Array.getElem_mem _)

theorem size_C_le (f : CPolynomial K) : (CPolynomial.C f).val.size ≤ 1 :=
  (raw_trim_size_le _).trans (by simp [CPolynomial.Raw.C])

theorem neg_val_size {R : Type} [Ring R] [BEq R] [LawfulBEq R] (y : CPolynomial R) :
    (-y).val.size = y.val.size := by
  show (Array.map (fun a ↦ -a) y.val).size = y.val.size
  simp

theorem size_one_K : (1 : CPolynomial K).val.size ≤ 1 := by
  have := val_size_le_natDegree_add_one (1 : CPolynomial K)
  rw [CPolynomial.natDegree_one] at this
  exact this

/-- `ofArray` over `K[X]`, entries of at most `A` coefficients: at most `(3·A + 32)·n + 14`. -/
theorem ofArrayB_cost (hP : Includes P Auto.CompPoly.CPolynomial.ofArray.c88.costDeps)
    (coeffs : Array (CPolynomial K)) (A : ℕ) (hA : ∀ x ∈ coeffs, x.val.size ≤ A)
    (hs : coeffs.size < 2 ^ 63) :
    machineCost P Auto.CompPoly.CPolynomial.ofArray.c88.costIdx [encodeValue coeffs] ≤
      (3 * A + 32) * coeffs.size + 14 := by
  rw [Auto.CompPoly.CPolynomial.ofArray.c88.costEq P hP]
  have := trimLenB_cost P (by includes) coeffs A hA coeffs.size hs
  have : (coeffs.extract 0 (CompPolyLib.trimLen coeffs coeffs.size)).size ≤ coeffs.size := by
    simp
  have e : (3 * A + 32) * coeffs.size = (3 * A + 31) * coeffs.size + coeffs.size := by ring
  omega

end

end LeanVM.Cost.Bounds.Decoder
