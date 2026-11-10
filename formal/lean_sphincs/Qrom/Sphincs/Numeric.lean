module

public import Qrom.Sphincs.Security

@[expose] public section

/-!
# The numbers

For the parameters of `FORS.Lifetimes.h26Params` (`h = 26`, `d = 3`, `k = 24`, `a = 10`,
`1,182,000,000` signatures), the cover bound is `lamS ≤ 1122 · 2^-137` (`Qrom.Sphincs.lamS_h26`),
its second-moment correction `lamS2 ≤ 2^-250` (`Qrom.Sphincs.lamS2_h26`), and an adversary making at
most `n` calls forges with probability at most `((n + 2048) / 2^61.8)²`
(`Qrom.Sphincs.winProb_le_h26`; term by term, `Qrom.Sphincs.winProb_le_h26_terms`).
-/

open OracleComp OracleSpec FORS FORS.Security Concrete Quantum
open scoped ENNReal

noncomputable section

set_option linter.unusedSectionVars false

namespace Qrom.Sphincs

/-- The parameters of `FORS.Lifetimes.h26Params`. -/
abbrev params26 : Params :=
  .layered (h := 26) (d := 3) (ℓ := 8) (k := 24) (a := 10) (N := 1_182_000_000)

section h26

local instance : Params := params26

theorem lamS_h26 : lamS ≤ 1122 * (2 : ℝ)⁻¹ ^ 137 := by
  have h : lamS ≤ ((1122 : ℕ) : ℝ) * (2 : ℝ)⁻¹ ^ 137 := lamS_le (by
    simp only [Fintype.card_fun, Fintype.card_fin, ← stirRow_getD]
    decide +kernel)
  simpa using h

theorem lamS2_h26 : lamS2 ≤ (2 : ℝ)⁻¹ ^ 250 := by
  have h : lamS2 ≤ ((1 : ℕ) : ℝ) * (2 : ℝ)⁻¹ ^ 250 := lamS2_le (by
    simp only [Fintype.card_fun, Fintype.card_fin, ← stirRow_getD]
    decide +kernel)
  simpa using h

theorem lamC_h26 : lamC ≤ 1123 * (2 : ℝ)⁻¹ ^ 137 := by
  have h1 : lamS ^ 2 ≤ (1122 * (2 : ℝ)⁻¹ ^ 137) ^ 2 := pow_le_pow_left₀ lamS_nonneg lamS_h26 2
  unfold lamC
  calc lamS + 3 * (lamS ^ 2 + lamS2)
      ≤ 1122 * (2 : ℝ)⁻¹ ^ 137 + 3 * ((1122 * (2 : ℝ)⁻¹ ^ 137) ^ 2 + (2 : ℝ)⁻¹ ^ 250) := by
        gcongr
        · exact lamS_h26
        · exact lamS2_h26
    _ ≤ 1123 * (2 : ℝ)⁻¹ ^ 137 := by
        have e : ∀ m : ℕ, (2 : ℝ)⁻¹ ^ m = 1 / 2 ^ m := fun m ↦ by rw [inv_pow, one_div]
        rw [e, e]
        norm_num

theorem verifyQueries_h26 : verifyQueries = 879 := by decide

/-- The h26 bound, term by term: an adversary from the register `A` in the state `ρ`, making at
most `n` calls in all, forges with probability at most
`(√((4 · 2^-130 (√(2 + 4 · 2^-128) (n + 880) + 1758)² + 1123 · 2^-137 (√2 (n + 1) + 2)²
+ 879 · 2^-128) tr ρ) + (n + 880) √(4 · 2^-128 tr ρ))²`. -/
theorem winProb_le_h26_terms {A : QReg} (adv : Adversary A) {n : ℕ}
    (hadv : ∀ pk, (adv pk).IsTotalQueryBound n) (ρ : SubState A) :
    winProb adv ρ ≤ ((ENNReal.ofReal (4 * (2 : ℝ)⁻¹ ^ 130 *
        (√(2 + 4 * (2 : ℝ)⁻¹ ^ 128) * (n + 880) + 1758) ^ 2 +
        1123 * (2 : ℝ)⁻¹ ^ 137 * (√2 * (n + 1) + 2) ^ 2 + 879 * (2 : ℝ)⁻¹ ^ 128) *
        ENNReal.ofReal ρ.matrix.trace.re) ^ (2⁻¹ : ℝ) + ((n + 880 : ℕ) : ℝ≥0∞) *
      (4 * ENNReal.ofReal ((2 : ℝ)⁻¹ ^ 128) * ENNReal.ofReal ρ.matrix.trace.re) ^ (2⁻¹ : ℝ)) ^ 2 := by
  refine (winProb_le adv hadv ρ).trans ?_
  have hN : (1 + n + verifyQueries : ℕ) = n + 880 := by rw [verifyQueries_h26]; omega
  rw [hN]
  gcongr
  set K := searchK n
  set K1 := searchK1 n
  have hK : K = (√(2 + 4 * (2 : ℝ)⁻¹ ^ 128) * (n + 880) + 1758) ^ 2 := by
    simp only [K, searchK, verifyQueries_h26]
    push_cast
    ring_nf
  have hK1 : K1 = (√2 * (n + 1) + 2) ^ 2 := by
    simp only [K1, searchK1]
    push_cast
    ring_nf
  have hK0 : 0 ≤ K := sq_nonneg _
  have hK10 : 0 ≤ K1 := sq_nonneg _
  unfold epsHid
  gcongr ?_ * _
  calc ENNReal.ofReal (verifyQueries * (2 : ℝ)⁻¹ ^ 128) + ENNReal.ofReal ((2 : ℝ)⁻¹ ^ 128 * K) +
        ENNReal.ofReal (lamC * K1) ≤
      ENNReal.ofReal (879 * (2 : ℝ)⁻¹ ^ 128) + ENNReal.ofReal ((2 : ℝ)⁻¹ ^ 128 * K) +
        ENNReal.ofReal (1123 * (2 : ℝ)⁻¹ ^ 137 * K1) := by
        rw [verifyQueries_h26]
        push_cast
        gcongr
        exact lamC_h26
    _ = ENNReal.ofReal (879 * (2 : ℝ)⁻¹ ^ 128 + (2 : ℝ)⁻¹ ^ 128 * K +
          1123 * (2 : ℝ)⁻¹ ^ 137 * K1) := by
        rw [ENNReal.ofReal_add (by positivity) (by positivity),
          ENNReal.ofReal_add (by positivity) (by positivity)]
    _ ≤ _ := by
        rw [← hK, ← hK1]
        refine ENNReal.ofReal_le_ofReal (le_of_eq ?_)
        have h1 : (2 : ℝ)⁻¹ ^ 128 = 4 * (2 : ℝ)⁻¹ ^ 130 := by norm_num
        rw [h1]
        ring

/-- `2^61.8` is at most `2^65 / 9.18`. -/
theorem two_rpow_le : (2 : ℝ) ^ (61.8 : ℝ) ≤ 2 ^ 65 / (918 / 100) := by
  have h5 : ((918 / 100 : ℝ) ^ 5) ≤ 2 ^ 16 := by norm_num
  have hx : (918 / 100 : ℝ) ≤ (2 : ℝ) ^ ((16 : ℝ) / 5) := by
    have e1 : ((918 / 100 : ℝ) ^ 5) ^ ((5 : ℝ)⁻¹) = 918 / 100 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
      norm_num
    have e2 : ((2 : ℝ) ^ 16) ^ ((5 : ℝ)⁻¹) = (2 : ℝ) ^ ((16 : ℝ) / 5) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
      norm_num
    rw [← e1, ← e2]
    exact Real.rpow_le_rpow (by positivity) h5 (by norm_num)
  have e : (2 : ℝ) ^ (61.8 : ℝ) = 2 ^ 65 / (2 : ℝ) ^ ((16 : ℝ) / 5) := by
    rw [show (61.8 : ℝ) = (65 : ℕ) - (16 : ℝ) / 5 by norm_num, Real.rpow_sub (by norm_num),
      Real.rpow_natCast]
  rw [e]
  gcongr

/-- The terms of the h26 bound are at most `(n + 2048) / 2^61.8`. -/
theorem h26_terms_le (n : ℕ) {T : ℝ} (hT1 : T ≤ 1) :
    √((4 * (2 : ℝ)⁻¹ ^ 130 * (√(2 + 4 * (2 : ℝ)⁻¹ ^ 128) * (n + 880) + 1758) ^ 2 +
        1123 * (2 : ℝ)⁻¹ ^ 137 * (√2 * (n + 1) + 2) ^ 2 + 879 * (2 : ℝ)⁻¹ ^ 128) * T) +
      (n + 880) * √(4 * (2 : ℝ)⁻¹ ^ 128 * T) ≤ (n + 2048) / (2 : ℝ) ^ (61.8 : ℝ) := by
  set u : ℝ := (2 : ℝ)⁻¹ ^ 65
  have hu : 0 < u := by positivity
  have h128 : (2 : ℝ)⁻¹ ^ 128 = 4 * u ^ 2 := by simp only [u]; norm_num
  have h130 : (2 : ℝ)⁻¹ ^ 130 = u ^ 2 := by simp only [u]; norm_num
  have h137 : (2 : ℝ)⁻¹ ^ 137 = u ^ 2 / 128 := by simp only [u]; norm_num
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  set s₁ := √(2 + 4 * (2 : ℝ)⁻¹ ^ 128)
  have hs₁ : s₁ ≤ 141422 / 100000 := Real.sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩
  have hs₂ : √2 ≤ s₁ := Real.sqrt_le_sqrt (by
    have : (0 : ℝ) ≤ 4 * (2 : ℝ)⁻¹ ^ 128 := by positivity
    linarith)
  have hs0 : 0 ≤ √2 := Real.sqrt_nonneg 2
  set A : ℝ := s₁ * (n + 880) + 1758
  set B : ℝ := √2 * (n + 1) + 2
  have hB0 : 0 ≤ B := by positivity
  have hA0 : 1758 ≤ A := by simp only [A]; nlinarith [Real.sqrt_nonneg (2 + 4 * (2 : ℝ)⁻¹ ^ 128)]
  have hBA : B ≤ A := by
    simp only [A, B]
    nlinarith [mul_le_mul_of_nonneg_right hs₂ (by linarith : (0 : ℝ) ≤ n + 1)]
  have hA : A ≤ 141422 / 100000 * (n + 880) + 1758 := by
    simp only [A]
    nlinarith [mul_le_mul_of_nonneg_right hs₁ (by linarith : (0 : ℝ) ≤ n + 880)]
  rw [h128, h130, h137]
  have h1 : √((4 * u ^ 2 * A ^ 2 + 1123 * (u ^ 2 / 128) * B ^ 2 + 879 * (4 * u ^ 2)) * T) ≤
      u * (35741 / 10000 * A + 1) := by
    refine Real.sqrt_le_iff.mpr ⟨by positivity, ?_⟩
    have hE : 0 ≤ 4 * u ^ 2 * A ^ 2 + 1123 * (u ^ 2 / 128) * B ^ 2 + 879 * (4 * u ^ 2) := by
      positivity
    have hBB : B ^ 2 ≤ A ^ 2 := pow_le_pow_left₀ hB0 hBA 2
    calc (4 * u ^ 2 * A ^ 2 + 1123 * (u ^ 2 / 128) * B ^ 2 + 879 * (4 * u ^ 2)) * T
        ≤ 4 * u ^ 2 * A ^ 2 + 1123 * (u ^ 2 / 128) * B ^ 2 + 879 * (4 * u ^ 2) :=
          mul_le_of_le_one_right hE hT1
      _ ≤ u ^ 2 * (35741 / 10000 * A + 1) ^ 2 := by
          nlinarith [sq_nonneg u, mul_le_mul_of_nonneg_left hBB (sq_nonneg u),
            mul_le_mul_of_nonneg_left hA0 (sq_nonneg u)]
      _ = (u * (35741 / 10000 * A + 1)) ^ 2 := by ring
  have h2 : √(4 * (4 * u ^ 2) * T) ≤ 4 * u := by
    refine Real.sqrt_le_iff.mpr ⟨by positivity, ?_⟩
    nlinarith [sq_nonneg u]
  have h3 : (n + 880 : ℝ) * √(4 * (4 * u ^ 2) * T) ≤ (n + 880) * (4 * u) :=
    mul_le_mul_of_nonneg_left h2 (by positivity)
  have h61 : 918 / 100 * u * (n + 2048) ≤ (n + 2048) / (2 : ℝ) ^ (61.8 : ℝ) := by
    have hp : 0 < (2 : ℝ) ^ (61.8 : ℝ) := by positivity
    rw [le_div_iff₀ hp]
    have hu65 : u * 2 ^ 65 = 1 := by simp only [u]; norm_num
    calc 918 / 100 * u * (n + 2048) * (2 : ℝ) ^ (61.8 : ℝ)
        ≤ 918 / 100 * u * (n + 2048) * (2 ^ 65 / (918 / 100)) := by
          gcongr
          exact two_rpow_le
      _ = (n + 2048) * (u * 2 ^ 65) := by field_simp
      _ = n + 2048 := by rw [hu65, mul_one]
  refine le_trans ?_ h61
  have k1 := mul_le_mul_of_nonneg_left hA hu.le
  calc _ ≤ u * (35741 / 10000 * A + 1) + (n + 880) * (4 * u) := add_le_add h1 h3
    _ ≤ 918 / 100 * u * (n + 2048) := by nlinarith [k1, mul_nonneg hu.le hn, hu.le]

/-- **leanSPHINCS in the QROM, for the parameters of `FORS.Lifetimes.h26Params`: 61.8 bits.** An
adversary from the register `A` in the state `ρ`, making at most `n` calls in all (hash queries,
quantum or classical, and signing requests), forges with probability at most
`((n + 2048) / 2^61.8)²`. -/
theorem winProb_le_h26 {A : QReg} (adv : Adversary A) {n : ℕ}
    (hadv : ∀ pk, (adv pk).IsTotalQueryBound n) (ρ : SubState A) :
    winProb adv ρ ≤ ((n + 2048 : ℝ≥0∞) / 2 ^ (61.8 : ℝ)) ^ 2 := by
  refine (winProb_le_h26_terms adv hadv ρ).trans ?_
  set T := ρ.matrix.trace.re
  have hT0 : 0 ≤ T := SubState.trace_re_nonneg _
  have hT1 : T ≤ 1 := ρ.trace_re_le_one
  have hE : 0 ≤ 4 * (2 : ℝ)⁻¹ ^ 130 * (√(2 + 4 * (2 : ℝ)⁻¹ ^ 128) * (n + 880) + 1758) ^ 2 +
      1123 * (2 : ℝ)⁻¹ ^ 137 * (√2 * (n + 1) + 2) ^ 2 + 879 * (2 : ℝ)⁻¹ ^ 128 := by positivity
  have hR : ((n + 2048 : ℝ≥0∞) / 2 ^ (61.8 : ℝ)) =
      ENNReal.ofReal ((n + 2048) / (2 : ℝ) ^ (61.8 : ℝ)) := by
    rw [ENNReal.ofReal_div_of_pos (by positivity), ENNReal.ofReal_add (Nat.cast_nonneg _)
      (by norm_num), ENNReal.ofReal_natCast, ENNReal.ofReal_ofNat,
      ← ENNReal.ofReal_rpow_of_pos (by norm_num), ENNReal.ofReal_ofNat]
  have hsq : ∀ x : ℝ, x ^ (2⁻¹ : ℝ) = √x := fun x ↦ by rw [Real.sqrt_eq_rpow]; norm_num
  rw [hR, ← ENNReal.ofReal_mul hE, ← ENNReal.ofReal_ofNat 4, ← ENNReal.ofReal_mul (by norm_num),
    ← ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num),
    ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num), hsq, hsq, ← ENNReal.ofReal_natCast,
    ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add (by positivity) (by positivity),
    ← ENNReal.ofReal_pow (by positivity), ← ENNReal.ofReal_pow (by positivity)]
  refine ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (by positivity) ?_ 2)
  push_cast
  exact h26_terms_le n hT1

end h26

end Qrom.Sphincs
