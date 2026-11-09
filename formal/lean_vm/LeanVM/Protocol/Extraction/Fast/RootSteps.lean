module

public import CompPoly.Bivariate.GuruswamiSudan.Root.RothRuckenstein.Lemmas
public import CompPoly.Bivariate.GuruswamiSudan.Root.Common
import all CompPoly.Univariate.Basic
import all CompPoly.Univariate.Raw.Core

/-!
# Roth–Ruckenstein's steps on `X`-adic orders, restated

Each step of Roth–Ruckenstein's recursion strips the `X`-adic factor of the bivariate polynomial
and reads its coefficients at `X^0`. CompPoly's code for both costs more than the algorithm needs,
so each is restated, proved equal on every input:

* **The equation for the next coefficient** (`initialCoeffFast`, **`initialCoeffFast_eq`**).
  CompPoly's `initialCoefficientPolynomial Q` adds the monomials `Q_y(0)·Y^y`, `y < |Q|`, one by
  one to an accumulator, each addition costing the accumulator's size: about `|Q|²/2`.
  `initialCoeffFast` reads the `|Q|` coefficients into one array.
* **Dropping `X^n`** (`dropXPowerFast`, **`dropXPowerFast_eq`**). CompPoly's `dropXPower p n`
  divides by `X` `n` times, each a copy of the array: `n·|p|`. `dropXPowerFast` copies the
  coefficients from `n` on once. With it: `divXPowerFast` (**`divXPowerFast_eq`**) and the
  stripping of the `X`-adic factor, `stripFast` (**`stripFast_eq`**).

Credits: `cpoly_coeff_dropXPower`, `initialCoefficientPolynomial_coeff_fold`,
`initialCoefficientPolynomial_coeff_of_lt` and `cbivar_coeff_eq_zero_of_y_size_le` are CompPoly's
(github.com/Verified-zkEVM/CompPoly at `572f997390aa4fc131ef30b1186fa1dcf292ca10`, Apache-2.0,
"Copyright (c) 2026 CompPoly Contributors"; `Bivariate/GuruswamiSudan/Root/RothRuckenstein/Lemmas.lean`,
Valerii Huhnin), used, not copied; `stripFast` is the text of CompPoly's `stripXAdicFactor`
(`Bivariate/GuruswamiSudan/Polynomial.lean`) with `divXPowerFast`.
-/

namespace LeanVM.Extraction.Fast

open CompPoly CompPoly.GuruswamiSudan

public section

variable {F : Type*} [Field F] [BEq F] [LawfulBEq F]

theorem coeff_initialCoefficientPolynomial [DecidableEq F] (Q : CBivariate F) (j : ℕ) :
    (initialCoefficientPolynomial Q).coeff j = CBivariate.coeff Q 0 j := by
  by_cases hj : j < Q.val.size
  · exact initialCoefficientPolynomial_coeff_of_lt Q hj
  · unfold initialCoefficientPolynomial
    rw [initialCoefficientPolynomial_coeff_fold Q j (List.range Q.val.size) 0 List.nodup_range,
      CPolynomial.coeff_zero, cbivar_coeff_eq_zero_of_y_size_le Q (by omega)]
    simp

/-- **`initialCoefficientPolynomial`, fast**: `Σ_y Q_y(0)·Y^y`, the coefficients read into one
array. -/
@[expose] def initialCoeffFast (Q : CBivariate F) : CPolynomial F :=
  CPolynomial.ofArray (Q.val.map fun c ↦ c.coeff 0)

theorem initialCoeffFast_eq [DecidableEq F] (Q : CBivariate F) :
    initialCoeffFast Q = initialCoefficientPolynomial Q := by
  refine CPolynomial.eq_iff_coeff.2 fun j ↦ ?_
  rw [initialCoeffFast, CPolynomial.coeff_ofArray, coeff_initialCoefficientPolynomial,
    CBivariate.coeff_eq_coeff_coeff]
  simp only [CPolynomial.coeff, CPolynomial.Raw.coeff, Array.getD_eq_getD_getElem?,
    Array.getElem?_map]
  cases Q.val[j]? <;> rfl

/-- **`dropXPower`, fast**: the coefficients from `n` on, copied once. -/
@[expose] def dropXPowerFast {R : Type*} [Zero R] [BEq R] [LawfulBEq R] (p : CPolynomial R)
    (n : ℕ) : CPolynomial R :=
  CPolynomial.ofArray (p.val.extract n p.val.size)

theorem dropXPowerFast_eq {R : Type*} [Zero R] [BEq R] [LawfulBEq R] (p : CPolynomial R)
    (n : ℕ) : dropXPowerFast p n = CPolynomial.dropXPower p n := by
  refine CPolynomial.eq_iff_coeff.2 fun i ↦ ?_
  rw [dropXPowerFast, CPolynomial.coeff_ofArray, cpoly_coeff_dropXPower]
  simp only [CPolynomial.coeff, CPolynomial.Raw.coeff, Array.getD_eq_getD_getElem?,
    Array.getElem?_extract]
  by_cases h : i < p.val.size - n
  · simp [h, Nat.add_comm]
  · simp only [min_self, h, ↓reduceIte, Option.getD_none]
    rw [Array.getElem?_eq_none (by omega), Option.getD_none]

/-- **`CBivariate.divXPower`, fast**: `dropXPowerFast` on each `Y`-coefficient. -/
@[expose] def divXPowerFast (Q : CBivariate F) (n : ℕ) : CBivariate F :=
  CPolynomial.ofArray (Q.val.map fun c ↦ dropXPowerFast c n)

theorem divXPowerFast_eq (Q : CBivariate F) (n : ℕ) :
    divXPowerFast Q n = CBivariate.divXPower Q n := by
  simp only [divXPowerFast, CBivariate.divXPower, dropXPowerFast_eq]

/-- **`CBivariate.stripXAdicFactor`, fast**: with `divXPowerFast`. -/
@[expose] def stripFast (Q : CBivariate F) : CBivariate F :=
  match CBivariate.xAdicOrder? Q with
  | none => default
  | some order => divXPowerFast Q order

theorem stripFast_eq (Q : CBivariate F) : stripFast Q = CBivariate.stripXAdicFactor Q := by
  rw [stripFast, CBivariate.stripXAdicFactor]
  cases CBivariate.xAdicOrder? Q with
  | none => rfl
  | some order => exact divXPowerFast_eq Q order

end

end LeanVM.Extraction.Fast
