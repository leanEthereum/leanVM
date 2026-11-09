module

public import CompPoly.Univariate.ToPoly
public import CompPoly.Univariate.Context
public import LeanVM.Protocol.Extraction.Fast.RothRuckenstein
public import CompPoly.Univariate.Raw.Proofs
import all CompPoly.Univariate.Raw.Core
import all CompPoly.Univariate.Basic

/-!
# Karatsuba multiplication of polynomials

`karatsuba fuel p q`: split both at `h = ⌈max |p| |q| / 2⌉`, `p = p₀ + X^h·p₁`, `q = q₀ + X^h·q₁`,
and `p·q = z₀ + X^h·(z₁ − z₀ − z₂) + X^(2h)·z₂` with `z₀ = p₀q₀`, `z₂ = p₁q₁`,
`z₁ = (p₀ + p₁)(q₀ + q₁)`: three products of half the size, so `O(n^log₂3)` operations, down to
schoolbook products below `karatsubaCutoff` coefficients. **`karatsuba_eq`**:
`karatsuba fuel p q = p * q` (through `toPoly`, injective and multiplicative onto Mathlib's
polynomials); `karatsubaMulContext` is CompPoly's `MulContext` for it, at the fuel `64`.
-/

namespace LeanVM.Extraction.Fast

open CompPoly

public section

variable {F : Type*} [Field F] [BEq F] [LawfulBEq F]

/-- Coefficients `[lo, hi)` of `p`. -/
@[expose] def coeffsBetween (p : CPolynomial F) (lo hi : ℕ) : CPolynomial F :=
  CPolynomial.ofArray (p.val.extract lo hi)

/-- Below this many coefficients, the schoolbook product. -/
@[expose] def karatsubaCutoff : ℕ := 32

/-- **Karatsuba's product**, `fuel` levels of splitting at most. -/
@[expose] def karatsuba : ℕ → CPolynomial F → CPolynomial F → CPolynomial F
  | 0, p, q => p * q
  | fuel + 1, p, q =>
    let n := max p.val.size q.val.size
    if n ≤ karatsubaCutoff then p * q
    else
      let h := (n + 1) / 2
      let p₀ := coeffsBetween p 0 h
      let p₁ := coeffsBetween p h n
      let q₀ := coeffsBetween q 0 h
      let q₁ := coeffsBetween q h n
      let z₀ := karatsuba fuel p₀ q₀
      let z₂ := karatsuba fuel p₁ q₁
      let z₁ := karatsuba fuel (p₀ + p₁) (q₀ + q₁)
      z₀ + shiftX h (z₁ - z₀ - z₂) + shiftX (2 * h) z₂

theorem coeff_coeffsBetween (p : CPolynomial F) (lo hi i : ℕ) :
    (coeffsBetween p lo hi).coeff i = if i < hi - lo then p.coeff (lo + i) else 0 := by
  rw [coeffsBetween, CPolynomial.coeff_ofArray, Array.getD_eq_getD_getElem?, Array.getElem?_extract]
  simp only [CPolynomial.coeff, CPolynomial.Raw.coeff, Array.getD_eq_getD_getElem?]
  by_cases h1 : i < hi - lo
  · by_cases h2 : i < min hi p.val.size - lo
    · simp [h1, h2]
    · have : p.val.size ≤ lo + i := by omega
      simp [h1, h2, Array.getElem?_eq_none this]
  · have h2 : ¬ i < min hi p.val.size - lo := by omega
    simp [h1, h2]

theorem toPoly_shiftX (t : ℕ) (r : CPolynomial F) :
    (shiftX t r).toPoly = Polynomial.X ^ t * r.toPoly := by
  ext i
  rw [CPolynomial.toPoly_coeff, coeff_shiftX, Polynomial.coeff_X_pow_mul', CPolynomial.toPoly_coeff]

theorem toPoly_split (p : CPolynomial F) {h n : ℕ} (hh : h ≤ n) (hn : p.val.size ≤ n) :
    p.toPoly = (coeffsBetween p 0 h).toPoly + Polynomial.X ^ h * (coeffsBetween p h n).toPoly := by
  ext i
  simp only [Polynomial.coeff_add, Polynomial.coeff_X_pow_mul', CPolynomial.toPoly_coeff,
    coeff_coeffsBetween, Nat.sub_zero, Nat.zero_add]
  by_cases hi : i < h
  · simp [hi, show ¬ h ≤ i by omega]
  · simp only [hi, ↓reduceIte, zero_add, show h ≤ i by omega]
    by_cases hi' : i - h < n - h
    · simp only [hi', ↓reduceIte, show h + (i - h) = i by omega]
    · simp only [hi', ↓reduceIte]
      exact CPolynomial.coeff_eq_zero_of_size_le _ (by omega)

theorem karatsuba_eq (fuel : ℕ) (p q : CPolynomial F) : karatsuba fuel p q = p * q := by
  induction fuel generalizing p q with
  | zero => rfl
  | succ fuel ih =>
    rw [karatsuba]
    split
    · rfl
    · rename_i hn
      simp only [ih]
      apply CPolynomial.toPoly_injective
      set n := max p.val.size q.val.size
      set h := (n + 1) / 2
      have hp := toPoly_split p (h := h) (n := n) (by omega) (le_max_left _ _)
      have hq := toPoly_split q (h := h) (n := n) (by omega) (le_max_right _ _)
      simp only [CPolynomial.toPoly_add, CPolynomial.toPoly_mul, CPolynomial.toPoly_sub,
        toPoly_shiftX]
      rw [hp, hq]
      ring

/-- CompPoly's multiplication context for Karatsuba's product. -/
@[expose] def karatsubaMulContext : CPolynomial.MulContext F where
  mul := karatsuba 64
  mul_eq_mul := karatsuba_eq 64

/-- The low `k` coefficients of a product of raw polynomials, by Karatsuba's product. -/
@[expose] def karatsubaMulLow (k : ℕ) (p q : CPolynomial.Raw F) : CPolynomial.Raw F :=
  (karatsuba 64 (CPolynomial.ofArray p) (CPolynomial.ofArray q)).val.extract 0 k

theorem coeff_karatsubaMulLow (k : ℕ) (p q : CPolynomial.Raw F) (i : ℕ) (hi : i < k) :
    (karatsubaMulLow k p q).coeff i = (p * q).coeff i := by
  rw [karatsubaMulLow, karatsuba_eq, ← CPolynomial.Raw.mul_trim_eq_mul p q]
  show CPolynomial.Raw.coeff (Array.extract (p.trim * q.trim) 0 k) i =
    CPolynomial.Raw.coeff (p.trim * q.trim) i
  simp only [CPolynomial.Raw.coeff, Array.getD_eq_getD_getElem?, Array.getElem?_extract]
  by_cases h : i < min k (p.trim * q.trim).size
  · simp [h]
  · have : (p.trim * q.trim).size ≤ i := by omega
    simp [h, Array.getElem?_eq_none this]

/-- CompPoly's low-product context for Karatsuba's product. -/
@[expose] def karatsubaMulLowContext : CPolynomial.Raw.MulLowContext F where
  mulLow := karatsubaMulLow
  size_le k p q := by simp [karatsubaMulLow]
  coeff_of_lt := coeff_karatsubaMulLow

/-- CompPoly's monic-remainder context by reversal, on Karatsuba's low products. -/
@[expose] def karatsubaModContext : CPolynomial.ModContext F :=
  CPolynomial.ModContext.reversal karatsubaMulLowContext

end

end LeanVM.Extraction.Fast
