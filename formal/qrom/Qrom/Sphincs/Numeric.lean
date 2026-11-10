module

public import Qrom.Sphincs.Security
public import Qrom.Sphincs.Bound.LamCov

@[expose] public section

/-!
# The numbers

With the cover probability bounded (`Qrom.Sphincs.lamF_le`), the forgery bound is explicit
(`Qrom.Sphincs.winProb_le_lamS`). For the parameters of `FORS.h26_layered` (`h = 26`, `d = 3`,
`k = 24`, `a = 10`, `1,182,000,000` signatures), `λ_full ≤ 9 · 2^-130` (`Qrom.Sphincs.lamS_h26`), and
an adversary making at most `n` calls forges with probability at most `((n + 2048) / 2^61)²`
(`Qrom.Sphincs.winProb_le_h26`; term by term, `Qrom.Sphincs.winProb_le_h26_terms`).
-/

open OracleComp OracleSpec FORS FORS.Security Concrete Quantum
open scoped ENNReal

noncomputable section

set_option linter.unusedSectionVars false

namespace Qrom.Sphincs

section generic

variable [Params]

/-- The weight of a win in the hidden game, with the cover probability bounded. -/
def epsB (n : ℕ) (t : ℝ) : ℝ≥0∞ :=
  (ENNReal.ofReal (verifyQueries * (2 : ℝ)⁻¹ ^ 128) + ENNReal.ofReal ((2 : ℝ)⁻¹ ^ 128 * searchK n) +
    ENNReal.ofReal lamS * ENNReal.ofReal (searchK1 n)) * ENNReal.ofReal t

theorem epsHid_le (n : ℕ) (t : ℝ) : epsHid n t ≤ epsB n t := by
  unfold epsHid epsB
  gcongr
  exact lamF_le

/-- **leanSPHINCS in the QROM, explicitly**: an adversary making at most `n` calls in all forges with
probability at most `(√ε + (n + 1 + verifyQueries) √(4 · 2^-128 tr ρ))²`, where `ε` is `epsB`. -/
theorem winProb_le_lamS {A : QReg} (adv : Adversary A) {n : ℕ}
    (hadv : ∀ pk, (adv pk).IsTotalQueryBound n) (ρ : SubState A) :
    winProb adv ρ ≤ (epsB n ρ.matrix.trace.re ^ (2⁻¹ : ℝ) + ((1 + n + verifyQueries : ℕ) : ℝ≥0∞) *
      (4 * ENNReal.ofReal ((2 : ℝ)⁻¹ ^ 128) * ENNReal.ofReal ρ.matrix.trace.re) ^ (2⁻¹ : ℝ)) ^ 2 := by
  refine (winProb_le adv hadv ρ).trans ?_
  gcongr
  exact epsHid_le n _

end generic

/-- The parameters of `FORS.h26_layered`. -/
abbrev params26 : Params :=
  .layered (h := 26) (d := 3) (ℓ := 8) (k := 24) (a := 10) (N := 1_182_000_000)

section h26

local instance : Params := params26

theorem lamS_h26 : lamS ≤ 9 * (2 : ℝ)⁻¹ ^ 130 := by
  have h : lamS ≤ ((9 : ℕ) : ℝ) * (2 : ℝ)⁻¹ ^ 130 := lamS_le (by
    simp only [Fintype.card_fun, Fintype.card_fin, ← stirRow_getD]
    decide +kernel)
  simpa using h

theorem verifyQueries_h26 : verifyQueries = 879 := by decide

/-- The h26 bound, term by term: an adversary from the register `A` in the state `ρ`, making at
most `n` calls in all, forges with probability at most
`(√((4 · 2^-130 (√6 (n + 880) + 1758)² + 9 · 2^-130 (√6 (n + 880) + 2)² + 879 · 2^-128) tr ρ) + (n + 880) √(4 · 2^-128 tr ρ))²`. -/
theorem winProb_le_h26_terms {A : QReg} (adv : Adversary A) {n : ℕ}
    (hadv : ∀ pk, (adv pk).IsTotalQueryBound n) (ρ : SubState A) :
    winProb adv ρ ≤ ((ENNReal.ofReal (4 * (2 : ℝ)⁻¹ ^ 130 * (√6 * (n + 880) + 1758) ^ 2 +
        9 * (2 : ℝ)⁻¹ ^ 130 * (√6 * (n + 880) + 2) ^ 2 + 879 * (2 : ℝ)⁻¹ ^ 128) *
        ENNReal.ofReal ρ.matrix.trace.re) ^ (2⁻¹ : ℝ) + ((n + 880 : ℕ) : ℝ≥0∞) *
      (4 * ENNReal.ofReal ((2 : ℝ)⁻¹ ^ 128) * ENNReal.ofReal ρ.matrix.trace.re) ^ (2⁻¹ : ℝ)) ^ 2 := by
  refine (winProb_le_lamS adv hadv ρ).trans ?_
  have hN : (1 + n + verifyQueries : ℕ) = n + 880 := by rw [verifyQueries_h26]; omega
  rw [hN]
  gcongr
  set K := searchK n
  set K1 := searchK1 n
  have hK : K = (√6 * (n + 880) + 1758) ^ 2 := by
    simp only [K, searchK, verifyQueries_h26]
    push_cast
    ring_nf
  have hK1 : K1 = (√6 * (n + 880) + 2) ^ 2 := by
    simp only [K1, searchK1, verifyQueries_h26]
    push_cast
    ring_nf
  have hK0 : 0 ≤ K := sq_nonneg _
  have hK10 : 0 ≤ K1 := sq_nonneg _
  unfold epsB
  gcongr ?_ * _
  calc ENNReal.ofReal (verifyQueries * (2 : ℝ)⁻¹ ^ 128) + ENNReal.ofReal ((2 : ℝ)⁻¹ ^ 128 * K) +
        ENNReal.ofReal lamS * ENNReal.ofReal K1 ≤
      ENNReal.ofReal (879 * (2 : ℝ)⁻¹ ^ 128) + ENNReal.ofReal ((2 : ℝ)⁻¹ ^ 128 * K) +
        ENNReal.ofReal (9 * (2 : ℝ)⁻¹ ^ 130 * K1) := by
        rw [verifyQueries_h26]
        push_cast
        gcongr
        rw [ENNReal.ofReal_mul (by positivity)]
        gcongr
        exact lamS_h26
    _ = ENNReal.ofReal (879 * (2 : ℝ)⁻¹ ^ 128 + (2 : ℝ)⁻¹ ^ 128 * K + 9 * (2 : ℝ)⁻¹ ^ 130 * K1) := by
        rw [ENNReal.ofReal_add (by positivity) (by positivity),
          ENNReal.ofReal_add (by positivity) (by positivity)]
    _ ≤ _ := by
        rw [← hK, ← hK1]
        refine ENNReal.ofReal_le_ofReal (le_of_eq ?_)
        have h1 : (2 : ℝ)⁻¹ ^ 128 = 4 * (2 : ℝ)⁻¹ ^ 130 := by norm_num
        rw [h1]
        ring

/-- The terms of the h26 bound are at most `(n + 2048) / 2^61`. -/
theorem h26_terms_le (n : ℕ) {T : ℝ} (hT1 : T ≤ 1) :
    √((4 * (2 : ℝ)⁻¹ ^ 130 * (√6 * (n + 880) + 1758) ^ 2 +
        9 * (2 : ℝ)⁻¹ ^ 130 * (√6 * (n + 880) + 2) ^ 2 + 879 * (2 : ℝ)⁻¹ ^ 128) * T) +
      (n + 880) * √(4 * (2 : ℝ)⁻¹ ^ 128 * T) ≤ (n + 2048) / 2 ^ 61 := by
  set u : ℝ := (2 : ℝ)⁻¹ ^ 65
  have hu : 0 < u := by positivity
  have h128 : (2 : ℝ)⁻¹ ^ 128 = 4 * u ^ 2 := by simp only [u]; norm_num
  have h130 : (2 : ℝ)⁻¹ ^ 130 = u ^ 2 := by simp only [u]; norm_num
  have h61 : (n + 2048 : ℝ) / 2 ^ 61 = 16 * u * (n + 2048) := by simp only [u]; ring_nf
  have hs0 : 0 ≤ √6 := Real.sqrt_nonneg 6
  have hs : √6 ≤ 49 / 20 := Real.sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  set A : ℝ := √6 * (n + 880) + 1758
  set B : ℝ := √6 * (n + 880) + 2
  have hB0 : 0 ≤ B := by positivity
  have hBA : B ≤ A := by simp only [A, B]; linarith
  have hA : A ≤ 49 / 20 * (n + 880) + 1758 := by
    simp only [A]
    nlinarith [mul_le_mul_of_nonneg_right hs (by linarith : (0 : ℝ) ≤ n + 880)]
  rw [h128, h130]
  have h1 : √((4 * u ^ 2 * A ^ 2 + 9 * u ^ 2 * B ^ 2 + 879 * (4 * u ^ 2)) * T) ≤ u * (4 * A + 60) := by
    refine Real.sqrt_le_iff.mpr ⟨by positivity, ?_⟩
    have hE : 0 ≤ 4 * u ^ 2 * A ^ 2 + 9 * u ^ 2 * B ^ 2 + 879 * (4 * u ^ 2) := by positivity
    have hBB : B ^ 2 ≤ A ^ 2 := pow_le_pow_left₀ hB0 hBA 2
    calc (4 * u ^ 2 * A ^ 2 + 9 * u ^ 2 * B ^ 2 + 879 * (4 * u ^ 2)) * T
        ≤ 4 * u ^ 2 * A ^ 2 + 9 * u ^ 2 * B ^ 2 + 879 * (4 * u ^ 2) :=
          mul_le_of_le_one_right hE hT1
      _ ≤ u ^ 2 * (4 * A + 60) ^ 2 := by nlinarith [sq_nonneg u, mul_nonneg (sq_nonneg u) (hB0.trans hBA)]
      _ = (u * (4 * A + 60)) ^ 2 := by ring
  have h2 : √(4 * (4 * u ^ 2) * T) ≤ 4 * u := by
    refine Real.sqrt_le_iff.mpr ⟨by positivity, ?_⟩
    nlinarith [sq_nonneg u]
  have h3 : (n + 880 : ℝ) * √(4 * (4 * u ^ 2) * T) ≤ (n + 880) * (4 * u) :=
    mul_le_mul_of_nonneg_left h2 (by positivity)
  rw [h61]
  nlinarith [mul_le_mul_of_nonneg_left hA hu.le, mul_nonneg hu.le hn]

/-- **leanSPHINCS in the QROM, for the parameters of `FORS.h26_layered`: 61 bits.** An adversary
from the register `A` in the state `ρ`, making at most `n` calls in all (hash queries, quantum or
classical, and signing requests), forges with probability at most `((n + 2048) / 2^61)²`. -/
theorem winProb_le_h26 {A : QReg} (adv : Adversary A) {n : ℕ}
    (hadv : ∀ pk, (adv pk).IsTotalQueryBound n) (ρ : SubState A) :
    winProb adv ρ ≤ ((n + 2048 : ℝ≥0∞) / 2 ^ 61) ^ 2 := by
  refine (winProb_le_h26_terms adv hadv ρ).trans ?_
  set T := ρ.matrix.trace.re
  have hT0 : 0 ≤ T := SubState.trace_re_nonneg _
  have hT1 : T ≤ 1 := ρ.trace_re_le_one
  have hE : 0 ≤ 4 * (2 : ℝ)⁻¹ ^ 130 * (√6 * (n + 880) + 1758) ^ 2 +
      9 * (2 : ℝ)⁻¹ ^ 130 * (√6 * (n + 880) + 2) ^ 2 + 879 * (2 : ℝ)⁻¹ ^ 128 := by positivity
  have hR : ((n + 2048 : ℝ≥0∞) / 2 ^ 61) = ENNReal.ofReal ((n + 2048) / 2 ^ 61) := by
    rw [ENNReal.ofReal_div_of_pos (by positivity), ENNReal.ofReal_add (Nat.cast_nonneg _) (by norm_num),
      ENNReal.ofReal_natCast, ENNReal.ofReal_ofNat, ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_ofNat]
  have hsq : ∀ x : ℝ, x ^ (2⁻¹ : ℝ) = √x := fun x ↦ by rw [Real.sqrt_eq_rpow]; norm_num
  rw [hR, ← ENNReal.ofReal_mul hE, ← ENNReal.ofReal_ofNat 4, ← ENNReal.ofReal_mul (by norm_num),
    ← ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num),
    ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num), hsq, hsq, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_add (by positivity) (by positivity), ← ENNReal.ofReal_pow (by positivity),
    ← ENNReal.ofReal_pow (by positivity)]
  refine ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (by positivity) ?_ 2)
  push_cast
  exact h26_terms_le n hT1

end h26

end Qrom.Sphincs
