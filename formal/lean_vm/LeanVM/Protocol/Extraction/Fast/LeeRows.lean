module

public import CompPoly.Bivariate.GuruswamiSudan.Interpolation.LeeOSullivan.Basic
public import CompPoly.Univariate.ToPoly.Equiv
public import CompPoly.Univariate.ToPoly.Impl
import all CompPoly.Univariate.Basic
import all CompPoly.Univariate.Raw.Core

/-!
# Lee–O'Sullivan's basis rows, the powers computed once

CompPoly's `leeOSullivanBasisRowsWithRG R G params` builds row `i < ℓ + 1` of the interpolation's
basis matrix from `P_i = Y^(i−t)·(Y − R)^t·G^(m−t)`, `t = min i m`, each power computed anew by
repeated squaring: `ℓ + 1` times the powers of `Y − R` and of `G`, each squaring a product of the
largest operands. `leeRowsFast` computes the powers `(Y − R)^t` and `G^j`, `t, j ≤ m`, once, each
from the previous by one product with the short factor first (`powersFrom`), then row `i ≤ m` as
`G^(m−i)·(Y − R)^i` (the `Y`-constant factor first) and row `i > m` as `(Y − R)^m` shifted by
`Y^(i−m)` (`shiftY`: zeros prepended, no product).

* `getD_powersFrom`: entry `i` of `powersFrom a x n` is `a^i·x`;
* `shiftY_eq`: `shiftY k P = Y^k·P`;
* **`leeRowsFast_eq`**: `leeRowsFast R G params = leeOSullivanBasisRowsWithRG R G params`.

Credits: CompPoly (github.com/Verified-zkEVM/CompPoly at `572f997390aa4fc131ef30b1186fa1dcf292ca10`,
Apache-2.0, "Copyright (c) 2026 CompPoly Contributors"): `leeRowsFast` restates
`leeOSullivanBasisRowsWithRG` and `leeOSullivanBasisPolynomial`
(`Bivariate/GuruswamiSudan/Interpolation/LeeOSullivan/Basic.lean`, Valerii Huhnin); its lemmas
`coeff_toPoly`, `toPoly_mul`, `toPoly_pow`, `monomial_toPoly`, `coeff_ofArray` are used.
-/

namespace LeanVM.Extraction.Fast

open CompPoly CompPoly.GuruswamiSudan

public section

/-- `[x, a·x, a²·x, …]`, `n` entries, each from the previous by one product `a · _`. -/
@[expose] def powersFrom {α : Type*} [Mul α] (a : α) : α → ℕ → List α
  | _, 0 => []
  | x, n + 1 => x :: powersFrom a (a * x) n

theorem getD_powersFrom {α : Type*} [Monoid α] [Zero α] (a x : α) (n : ℕ) {i : ℕ}
    (hi : i < n) : (powersFrom a x n).getD i 0 = a ^ i * x := by
  induction n generalizing x i with
  | zero => omega
  | succ n ih =>
    rcases i with _ | i
    · simp [powersFrom]
    · rw [powersFrom, List.getD_cons_succ, ih (a * x) (by omega), pow_succ, mul_assoc]

variable {F : Type*} [Field F] [BEq F] [LawfulBEq F] [DecidableEq F]

/-- `Y^k·P`: `k` zero coefficients prepended. -/
@[expose] def shiftY (k : ℕ) (P : CBivariate F) : CBivariate F :=
  CPolynomial.ofArray (Array.replicate k 0 ++ P.val)

omit [DecidableEq F] in
theorem coeff_shiftY (k : ℕ) (P : CBivariate F) (j : ℕ) :
    CPolynomial.coeff (shiftY k P) j = if k ≤ j then CPolynomial.coeff P (j - k) else 0 := by
  rw [shiftY, CPolynomial.coeff_ofArray]
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_append, Array.size_replicate]
  split <;> rename_i h
  · simp [h, show ¬ k ≤ j by omega]
  · simp only [show k ≤ j by omega, ↓reduceIte]

theorem shiftY_eq (k : ℕ) (P : CBivariate F) : shiftY k P = CBivariate.Y ^ k * P := by
  refine CPolynomial.eq_iff_coeff.2 fun j ↦ ?_
  rw [coeff_shiftY, CPolynomial.coeff_toPoly (CBivariate.Y ^ k * P), CPolynomial.toPoly_mul,
    CPolynomial.toPoly_pow, CBivariate.Y, CPolynomial.monomial_toPoly, CPolynomial.C_one,
    Polynomial.monomial_one_one_eq_X, Polynomial.coeff_X_pow_mul', CPolynomial.coeff_toPoly]

/-- **Lee–O'Sullivan's basis rows, the powers computed once.** -/
@[expose] def leeRowsFast (R G : CPolynomial F) (params : GSInterpParams) : PolynomialMatrix F :=
  let width := leeOSullivanWidth params
  let m := params.multiplicity
  let linearPowers := (powersFrom (CBivariate.linearYDivisor R) 1 (m + 1)).toArray
  let vanishingPowers := (powersFrom (CBivariate.ofYConstant G) 1 (m + 1)).toArray
  (List.range width).map
    (fun i ↦ CBivariate.toCoeffRow width
      (if i ≤ m then vanishingPowers.getD (m - i) 0 * linearPowers.getD i 0
      else shiftY (i - m) (linearPowers.getD m 0))) |>.toArray

theorem leeRowsFast_eq (R G : CPolynomial F) (params : GSInterpParams) :
    leeRowsFast R G params = leeOSullivanBasisRowsWithRG R G params := by
  rw [leeRowsFast, leeOSullivanBasisRowsWithRG]
  congr 1
  refine List.map_congr_left fun i _ ↦ ?_
  congr 1
  rw [leeOSullivanBasisPolynomial, leeOSullivanT]
  simp only [Array.getD_eq_getD_getElem?, List.getElem?_toArray, ← List.getD_eq_getElem?_getD]
  split <;> rename_i h
  · rw [getD_powersFrom _ _ _ (by omega), getD_powersFrom _ _ _ (by omega), min_eq_left h,
      Nat.sub_self, pow_zero, one_mul, mul_one, mul_one, mul_comm]
  · rw [getD_powersFrom _ _ _ (by omega), min_eq_right (by omega), Nat.sub_self, pow_zero,
      mul_one, mul_one, shiftY_eq]

end

end LeanVM.Extraction.Fast
