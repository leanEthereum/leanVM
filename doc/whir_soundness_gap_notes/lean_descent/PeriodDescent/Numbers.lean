/-
The arithmetic of note 39 section 1 ("Numbers") and of section 1.5 of note 46, at `N = 25`,
`k = 2^24`, `T = ⌈0.64 n⌉ = 21474837`, `Δ = T - k + 1 = 4697622`, `J = 24`,
`N J - J (J - 1) / 2 = 324`, on explicit numerals.

* `bound_f7`, `bound_f16`, `bound_f133`, `bound_f134`: with `j₀ = J = 24` the bound
  `C(f + 1, 3)^24 2^324 (n / Δ + 1)` is at most `2^467`, `2^553`, `2^773`, `2^774` for
  `f = 7, 16, 133, 134` (the notes: `2^466.4`, `2^552.9`, `2^773.0`, `2^773.7`), and above
  `2^466`, `2^552`, `2^772`, `2^773`.
* `theoremR_N25_f7`: Theorem R at these parameters with `f = 7`: at most `2^467` codewords.
* `baseB_20_le`, `bound_f7_j20`, `theoremR_N25_f7_j20`: with the stopping level `j₀ = 20`
  (quotients of 32 points, degree bound 15), `B_{20} ≤ 328734` and the bound is at most `2^445`
  (note 46: `2^444.5`).
* `bound_f16_j20`, `bound_f134_j20`: the same level for `f = 16` and `f = 134`: `2^517` and `2^701`
  (note 46: `2^516.5`, `2^700.6`).
* `bound_sharp_f7`, `bound_sharp_f7_j20`: with `C(f, 2)` in place of `C(f + 1, 3)` the bound for
  `f = 7` is at most `2^433` at `j₀ = 24` and `2^417` at `j₀ = 20`.
-/
import PeriodDescent.TheoremR
import PeriodDescent.Johnson3

open Polynomial Finset
open scoped Classical

namespace PeriodDescent

/-! ### The parameters -/

/-- `T = ⌈0.64 · 2^25⌉ = 21474837`. -/
theorem T_eq : (21474837 : ℚ) - 1 < 0.64 * 2 ^ 25 ∧ (0.64 : ℚ) * 2 ^ 25 ≤ 21474837 := by
  norm_num

/-- `Δ = T - k + 1 = 4697622`. -/
theorem Delta_eq : 21474837 - 2 ^ 24 + 1 = 4697622 := by norm_num

/-- `N J - J (J - 1) / 2 = 324`. -/
theorem expo_24 : 25 * 24 - 24 * (24 - 1) / 2 = 324 := by norm_num

/-- `N j₀ - j₀ (j₀ - 1) / 2 = 310` for `j₀ = 20`. -/
theorem expo_20 : 25 * 20 - 20 * (20 - 1) / 2 = 310 := by norm_num

theorem choose_8_3 : (7 + 1).choose 3 = 56 := by decide

theorem choose_7_2 : (7).choose 2 = 21 := by decide

theorem choose_17_3 : (16 + 1).choose 3 = 680 := by decide

theorem choose_134_3 : (133 + 1).choose 3 = 392084 := by
  have h := six_mul_choose_three 134
  show Nat.choose 134 3 = 392084
  omega

theorem choose_135_3 : (134 + 1).choose 3 = 400995 := by
  have h := six_mul_choose_three 135
  show Nat.choose 135 3 = 400995
  omega

/-! ### The bounds at `j₀ = J = 24` -/

set_option exponentiation.threshold 1000 in
/-- `f = 7`: `C(8, 3)^24 2^324 (n / Δ + 1) ≤ 2^467`. -/
theorem bound_f7 : (56 : ℚ) ^ 24 * 2 ^ 324 * ((2 : ℚ) ^ 25 / 4697622 + 1) ≤ 2 ^ 467 := by
  norm_num

set_option exponentiation.threshold 1000 in
theorem bound_f7_lower :
    (2 : ℚ) ^ 466 < (56 : ℚ) ^ 24 * 2 ^ 324 * ((2 : ℚ) ^ 25 / 4697622 + 1) := by
  norm_num

set_option exponentiation.threshold 1000 in
/-- `f = 16`: `C(17, 3)^24 2^324 (n / Δ + 1) ≤ 2^553`. -/
theorem bound_f16 : (680 : ℚ) ^ 24 * 2 ^ 324 * ((2 : ℚ) ^ 25 / 4697622 + 1) ≤ 2 ^ 553 := by
  norm_num

set_option exponentiation.threshold 1000 in
theorem bound_f16_lower :
    (2 : ℚ) ^ 552 < (680 : ℚ) ^ 24 * 2 ^ 324 * ((2 : ℚ) ^ 25 / 4697622 + 1) := by
  norm_num

set_option exponentiation.threshold 1000 in
/-- `f = 133`: `C(134, 3)^24 2^324 (n / Δ + 1) ≤ 2^773`. -/
theorem bound_f133 : (392084 : ℚ) ^ 24 * 2 ^ 324 * ((2 : ℚ) ^ 25 / 4697622 + 1) ≤ 2 ^ 773 := by
  norm_num

set_option exponentiation.threshold 1000 in
theorem bound_f133_lower :
    (2 : ℚ) ^ 772 < (392084 : ℚ) ^ 24 * 2 ^ 324 * ((2 : ℚ) ^ 25 / 4697622 + 1) := by
  norm_num

set_option exponentiation.threshold 1000 in
/-- `f = 134`: `C(135, 3)^24 2^324 (n / Δ + 1) ≤ 2^774`. -/
theorem bound_f134 : (400995 : ℚ) ^ 24 * 2 ^ 324 * ((2 : ℚ) ^ 25 / 4697622 + 1) ≤ 2 ^ 774 := by
  norm_num

set_option exponentiation.threshold 1000 in
theorem bound_f134_lower :
    (2 : ℚ) ^ 773 < (400995 : ℚ) ^ 24 * 2 ^ 324 * ((2 : ℚ) ^ 25 / 4697622 + 1) := by
  norm_num

set_option exponentiation.threshold 1000 in
/-- The sharper constant `C(7, 2) = 21`: at most `2^433`. -/
theorem bound_sharp_f7 : (21 : ℚ) ^ 24 * 2 ^ 324 * ((2 : ℚ) ^ 25 / 4697622 + 1) ≤ 2 ^ 433 := by
  norm_num

/-! ### Theorem R at these parameters -/

/-- **Theorem R at `N = 25`, `k = 2^24`, `T = ⌈0.64 n⌉`, `f = 7`, `j₀ = 24`.** On every subspace
of dimension 25 of every field of characteristic two, under PL`(7, 24)` every word has at most
`2^467` polynomials of degree `< 2^24` agreeing with it on at least `21474837` points. -/
theorem theoremR_N25_f7 {F : Type*} [Field F] [CharP F 2] (D : Finset F) (hD : IsSubspace D)
    (hN : D.card = 2 ^ 25) (hPL : PLsub D (2 ^ 24) 4697622 7 24) (w : F → F) (S : Finset F[X])
    (hdeg : ∀ P ∈ S, P.degree < ((2 ^ 24 : ℕ) : WithBot ℕ))
    (hagr : ∀ P ∈ S, 21474837 ≤ (D.filter (fun x => P.eval x = w x)).card) :
    (S.card : ℚ) ≤ 2 ^ 467 := by
  have h := theoremR_top D hD 25 (2 ^ 24) 21474837 7 24 hN (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) le_rfl (by rw [Delta_eq]; exact hPL) w S hdeg hagr
  rw [choose_8_3, expo_24, Delta_eq] at h
  exact h.trans (by exact_mod_cast bound_f7)

/-! ### The stopping level `j₀ = 20` -/

/-- The degree bound of the level 20 is `⌊(2^24 - 1) / 2^20⌋ = 15`. -/
theorem kappa_20 : (2 ^ 24 - 1) / 2 ^ 20 = 15 := by norm_num

/-- `B_{20} ≤ 328734`: the lists of the level 20 (quotients of 32 points, degree at most 15, slack
`Δ`) have at most `328733` members. -/
theorem baseB_20_le : baseB (2 ^ 25) 4697622 (2 ^ 20) 15 ≤ 328734 := by
  unfold baseB
  refine Finset.sup'_le _ _ fun κ hκ => ?_
  rw [Finset.mem_range] at hκ
  interval_cases κ <;> norm_num [Finset.prod_range_succ]

set_option exponentiation.threshold 1000 in
/-- `f = 7`, `j₀ = 20`: `C(8, 3)^20 2^310 (B_{20} + 1) ≤ 2^445`. -/
theorem bound_f7_j20 : (56 : ℚ) ^ 20 * 2 ^ 310 * (328734 + 1) ≤ 2 ^ 445 := by
  norm_num

set_option exponentiation.threshold 1000 in
/-- `f = 16`, `j₀ = 20`: `C(17, 3)^20 2^310 (B_{20} + 1) ≤ 2^517` (note 46: `2^516.5`). -/
theorem bound_f16_j20 : (680 : ℚ) ^ 20 * 2 ^ 310 * (328734 + 1) ≤ 2 ^ 517 := by
  norm_num

set_option exponentiation.threshold 1000 in
/-- `f = 134`, `j₀ = 20`: `C(135, 3)^20 2^310 (B_{20} + 1) ≤ 2^701` (note 46: `2^700.6`). -/
theorem bound_f134_j20 : (400995 : ℚ) ^ 20 * 2 ^ 310 * (328734 + 1) ≤ 2 ^ 701 := by
  norm_num

set_option exponentiation.threshold 1000 in
/-- The sharper constant at `j₀ = 20`, `f = 7`: `C(7, 2)^20 2^310 (B_{20} + 1) ≤ 2^417`. -/
theorem bound_sharp_f7_j20 : (21 : ℚ) ^ 20 * 2 ^ 310 * (328734 + 1) ≤ 2 ^ 417 := by
  norm_num

/-- **Theorem R at `N = 25`, `k = 2^24`, `T = ⌈0.64 n⌉`, `f = 7`, with the stopping level
`j₀ = 20`.** Under PL`(7, 20)`, which concerns the quotients of 64 points and more only, every word
has at most `2^445` polynomials of degree `< 2^24` agreeing with it on at least `21474837`
points. -/
theorem theoremR_N25_f7_j20 {F : Type*} [Field F] [CharP F 2] (D : Finset F) (hD : IsSubspace D)
    (hN : D.card = 2 ^ 25) (hPL : PLsub D (2 ^ 24) 4697622 7 20) (w : F → F) (S : Finset F[X])
    (hdeg : ∀ P ∈ S, P.degree < ((2 ^ 24 : ℕ) : WithBot ℕ))
    (hagr : ∀ P ∈ S, 21474837 ≤ (D.filter (fun x => P.eval x = w x)).card) :
    (S.card : ℚ) ≤ 2 ^ 445 := by
  have h := theoremR D hD 25 (2 ^ 24) 21474837 7 20 hN (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by rw [Delta_eq]; exact hPL) w S hdeg hagr
  rw [choose_8_3, expo_20, Delta_eq, kappa_20] at h
  have h1 : ((56 : ℕ) : ℚ) ^ 20 * 2 ^ 310 * (baseB (2 ^ 25) 4697622 (2 ^ 20) 15 + 1)
      ≤ (56 : ℚ) ^ 20 * 2 ^ 310 * (328734 + 1) := by
    have h2 := baseB_20_le
    have h3 : (0 : ℚ) ≤ ((56 : ℕ) : ℚ) ^ 20 * 2 ^ 310 := by positivity
    have h4 : ((56 : ℕ) : ℚ) = 56 := by norm_num
    rw [← h4]
    exact mul_le_mul_of_nonneg_left (by linarith) h3
  exact h.trans (h1.trans bound_f7_j20)

end PeriodDescent
