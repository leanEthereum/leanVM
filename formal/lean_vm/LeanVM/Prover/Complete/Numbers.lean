/-
  LeanVM.Prover.Complete.Numbers

  The completeness bound at the statement's fuel: below `2^-256`.
-/

module

public import LeanVM.Prover.Complete.Pow
public import LeanVM.Protocol.ErrorBounds

/-!
# The numbers

At `2^35` nonces per proof of work of at most `17` bits, a search fails with probability
`missK 17 ^ 2^35 ≤ (1 - 2^-18)^(2^35) ≤ 2^-163840` (`missProb_pow_four_le`), so `Q ≤ 2^120` queries
leave `2^-257`; with at most `2^125` permutation calls the transfer costs `rpmError N ≤ 2^-258`
(`completenessBound_le`).
-/

@[expose] public section

namespace LeanVM.Prover

open LeanVM.Protocol.Compile.Rom
open scoped ENNReal

/-- A `17`-bit proof of work that also asks its challenge to lie outside `K` misses at most as
often as one of `18` bits: `1 - 2^-17 (1 - 2^-64) ≤ 1 - 2^-18`. -/
theorem missK_le_missProb : missK 17 ≤ missProb 18 := by
  have h1 : missK 17 = ENNReal.ofReal (1 - (1 / 2 : ℝ) ^ 17 * (1 - (1 / 2 : ℝ) ^ 64)) := by
    rw [ENNReal.ofReal_sub _ (by norm_num), ENNReal.ofReal_one,
      ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_sub _ (by norm_num), ENNReal.ofReal_one,
      ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_pow (by norm_num), missK, qK, one_div,
      ENNReal.ofReal_inv_of_pos (by norm_num)]
    norm_num
  rw [h1, missProb_eq_ofReal]
  exact ENNReal.ofReal_le_ofReal (by norm_num)

/-- `2^120 · 2^-377 = 2^-257`. -/
theorem two_pow_mul_inv_pow : (2 : ℝ≥0∞) ^ 120 * 2⁻¹ ^ 377 = 2⁻¹ ^ 257 := by
  rw [show (377 : ℕ) = 120 + 257 by norm_num, pow_add, ← mul_assoc, ← mul_pow,
    ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_pow, one_mul]

/-- **The completeness bound** at `2^35` nonces and `17`-bit proofs of work: `Q ≤ 2^120` queries
and `N ≤ 2^125` permutation calls give at most `2^-256`. -/
theorem completenessBound_le {Q N : ℕ} (hQ : Q ≤ 2 ^ 120) (hN : N ≤ 2 ^ 125) :
    (Q : ℝ≥0∞) * missK 17 ^ (2 ^ 35) + rpmError N ≤ 2⁻¹ ^ 256 := by
  have hmiss : missK 17 ^ (2 ^ 35) ≤ 2⁻¹ ^ 377 := by
    calc missK 17 ^ (2 ^ 35) ≤ missProb 18 ^ (2 ^ 35) := pow_le_pow_left₀ bot_le missK_le_missProb _
      _ = missProb 18 ^ (2 ^ 18 * 4 * 2 ^ 15) := by norm_num
      _ ≤ 2⁻¹ ^ (5 * 2 ^ 15) := missProb_pow_four_le 18 (2 ^ 15)
      _ ≤ 2⁻¹ ^ 377 := pow_le_pow_right_of_le_one' (by norm_num) (by norm_num)
  have h1 : (Q : ℝ≥0∞) * missK 17 ^ (2 ^ 35) ≤ 2⁻¹ ^ 257 := by
    rw [← two_pow_mul_inv_pow]
    exact mul_le_mul' (by exact_mod_cast hQ) hmiss
  have h2 : rpmError N ≤ 2⁻¹ ^ 257 := by
    have hN2 : N ^ 2 ≤ 2 ^ 250 := by
      calc N ^ 2 ≤ (2 ^ 125) ^ 2 := Nat.pow_le_pow_left hN 2
        _ = 2 ^ 250 := by norm_num
    calc rpmError N = ((N ^ 2 : ℕ) : ℝ≥0∞) / ((2 ^ 508 : ℕ) : ℝ≥0∞) := rpmError_eq N
      _ ≤ ((2 ^ 250 : ℕ) : ℝ≥0∞) / ((2 ^ 508 : ℕ) : ℝ≥0∞) :=
        ENNReal.div_le_div_right (by exact_mod_cast hN2) _
      _ = 2⁻¹ ^ 258 := (inv_two_pow_eq_div 258 508 (by norm_num)).symm
      _ ≤ 2⁻¹ ^ 257 := pow_le_pow_right_of_le_one' (by norm_num) (by norm_num)
  calc (Q : ℝ≥0∞) * missK 17 ^ (2 ^ 35) + rpmError N ≤ 2⁻¹ ^ 257 + 2⁻¹ ^ 257 :=
        add_le_add h1 h2
    _ = 2⁻¹ ^ 256 := by
        rw [← two_mul, pow_succ, ← mul_assoc, mul_comm 2, mul_assoc,
          ENNReal.mul_inv_cancel (by norm_num) (by norm_num), mul_one]

end LeanVM.Prover

end
