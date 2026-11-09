module

public import Mathlib.Basic.ENNReal.Real
public import Mathlib.Tactic

@[expose] public section

/-!
# The arithmetic of the code-binding bound

From Benedikt Wagner's squared bound `(P - T)² ≤ (Q + 2) (ε₂ + δ)` with the collision term
`ε₂ ≤ F² / 2^256` (`F ≤ 2 (Q + 2^20)`) and the membership test's
`δ = (2^14 - 1) / 2^192 + 2^-384`, the code-binding probability `P` is at most `T` plus
`x / 2^95 + x² / 2^159 + (Q + 2) / 2^89` for `x = Q + 2^20` (`le_of_sq_tsub_le`, `fork_sq_le`):
`(Q + 2) F² / 2^256 ≤ 4 x³ / 2^256 ≤ (x / 2^95 + x² / 2^159)²` (the arithmetic and geometric
means), and `(Q + 2) δ ≤ (Q + 2) / 2^178 ≤ ((Q + 2) / 2^89)²`.

This module is part of the instantiation of Benedikt Wagner's framework for erasure code
commitments (`PqDas`, ported from https://github.com/b-wagn/fv-pq-da) with LeanDA.
-/

open scoped ENNReal

namespace LeanDa

/-- **A squared bound read as a bound**: `(P - T)² ≤ U²` gives `P ≤ T + U`. -/
theorem le_of_sq_tsub_le {P T U V : ℝ≥0∞} (h : (P - T) ^ 2 ≤ V) (hV : V ≤ U ^ 2) : P ≤ T + U := by
  rw [← tsub_le_iff_left]
  exact (ENNReal.pow_le_pow_left_iff (by norm_num)).mp (h.trans hV)

theorem toReal_natCast_div_pow (n k : ℕ) :
    ((n : ℝ≥0∞) / 2 ^ k).toReal = (n : ℝ) / 2 ^ k := by
  rw [ENNReal.toReal_div, ENNReal.toReal_pow]
  simp

/-- **The forking term**: for `F ≤ 2 (Q + 2^20)`, the right side of Wagner's squared bound is at
most the square of `x / 2^95 + x² / 2^159 + (Q + 2) / 2^89`, `x = Q + 2^20`. -/
theorem fork_sq_le (Q F : ℕ) (hF : F ≤ 2 * (Q + 2 ^ 20)) :
    ((Q : ℝ≥0∞) + 2) * ((F : ℝ≥0∞) ^ 2 / 2 ^ 256 + (2 ^ 14 - 1) / 2 ^ 192 + (2 ^ 384)⁻¹) ≤
      (((Q + 2 ^ 20 : ℕ) : ℝ≥0∞) / 2 ^ 95 + ((Q + 2 ^ 20 : ℕ) : ℝ≥0∞) ^ 2 / 2 ^ 159 +
        ((Q + 2 : ℕ) : ℝ≥0∞) / 2 ^ 89) ^ 2 := by
  have hδ : ((2 : ℝ≥0∞) ^ 14 - 1) / 2 ^ 192 + (2 ^ 384)⁻¹ ≤ 1 / 2 ^ 178 := by
    have h1 : ((2 : ℝ≥0∞) ^ 384)⁻¹ ≤ (2 ^ 192)⁻¹ :=
      ENNReal.inv_le_inv.mpr (pow_le_pow_right₀ (by norm_num) (by norm_num))
    have h2 : ((2 : ℝ≥0∞) ^ 14 - 1) + 1 = 2 ^ 14 :=
      tsub_add_cancel_of_le (one_le_pow₀ (by norm_num))
    calc ((2 : ℝ≥0∞) ^ 14 - 1) / 2 ^ 192 + (2 ^ 384)⁻¹
        ≤ ((2 : ℝ≥0∞) ^ 14 - 1) / 2 ^ 192 + 1 / 2 ^ 192 := by rw [one_div]; exact add_le_add le_rfl h1
      _ = 2 ^ 14 / 2 ^ 192 := by rw [ENNReal.div_add_div_same, h2]
      _ = 1 / 2 ^ 178 := by
          rw [ENNReal.div_eq_div_iff (by positivity) (by simp) (by positivity) (by simp), mul_one,
            ← pow_add]
  have hF2 : (F : ℝ≥0∞) ^ 2 ≤ (2 * ((Q + 2 ^ 20 : ℕ) : ℝ≥0∞)) ^ 2 := by
    gcongr; exact_mod_cast hF
  calc ((Q : ℝ≥0∞) + 2) * ((F : ℝ≥0∞) ^ 2 / 2 ^ 256 + (2 ^ 14 - 1) / 2 ^ 192 + (2 ^ 384)⁻¹)
      ≤ ((Q + 2 : ℕ) : ℝ≥0∞) * ((2 * ((Q + 2 ^ 20 : ℕ) : ℝ≥0∞)) ^ 2 / 2 ^ 256 + 1 / 2 ^ 178) := by
        rw [add_assoc]
        push_cast
        gcongr
        exact_mod_cast hF
    _ ≤ _ := by
        rw [← ENNReal.toReal_le_toReal (by finiteness) (by finiteness)]
        simp only [ENNReal.toReal_mul, ENNReal.toReal_add, ENNReal.toReal_pow, ENNReal.toReal_div,
          ENNReal.toReal_natCast, ENNReal.toReal_ofNat, ENNReal.toReal_one, ne_eq,
          ENNReal.div_eq_top, ENNReal.natCast_ne_top, ENNReal.pow_eq_top_iff, ENNReal.ofNat_ne_top,
          false_and, and_false, or_self, not_false_eq_true, ENNReal.mul_eq_top, pow_eq_zero_iff,
          OfNat.ofNat_ne_zero, ENNReal.add_eq_top, ENNReal.one_ne_top]
        push_cast
        set x : ℝ := (Q : ℝ) + 2 ^ 20 with hx
        have hq : (0 : ℝ) ≤ Q := Nat.cast_nonneg Q
        have hqx : (Q : ℝ) + 2 ≤ x := by rw [hx]; norm_num
        have hx0 : 0 ≤ x := by positivity
        have ha : 0 ≤ x / 2 ^ 95 := by positivity
        have hb : 0 ≤ x ^ 2 / 2 ^ 159 := by positivity
        have hc : 0 ≤ ((Q : ℝ) + 2) / 2 ^ 89 := by positivity
        have h4 : 4 * x ^ 3 / 2 ^ 254 ≤ (x / 2 ^ 95 + x ^ 2 / 2 ^ 159) ^ 2 := by
          have := sq_nonneg (x / 2 ^ 95 - x ^ 2 / 2 ^ 159)
          have e : 4 * (x / 2 ^ 95) * (x ^ 2 / 2 ^ 159) = 4 * x ^ 3 / 2 ^ 254 := by ring
          nlinarith
        have h5 : ((Q : ℝ) + 2) * ((2 * x) ^ 2 / 2 ^ 256) ≤ 4 * x ^ 3 / 2 ^ 254 := by
          have : ((Q : ℝ) + 2) * (2 * x) ^ 2 ≤ x * (4 * x ^ 2) := by nlinarith
          have e1 : ((Q : ℝ) + 2) * ((2 * x) ^ 2 / 2 ^ 256) = ((Q : ℝ) + 2) * (2 * x) ^ 2 / 2 ^ 256 := by
            ring
          rw [e1, div_le_div_iff₀ (by positivity) (by positivity)]
          nlinarith [pow_pos (show (0 : ℝ) < 2 by norm_num) 254]
        have h6 : ((Q : ℝ) + 2) * (1 / 2 ^ 178) ≤ (((Q : ℝ) + 2) / 2 ^ 89) ^ 2 := by
          have : (1 : ℝ) ≤ (Q : ℝ) + 2 := by linarith
          rw [div_pow, ← pow_mul]
          rw [mul_one_div]
          gcongr
          nlinarith
        nlinarith [mul_nonneg ha hc, mul_nonneg hb hc]

/-- **The remaining terms**, each at most a multiple of `y² / 2^256` or of `x / 2^95`. -/
theorem rest_le (Q K W x y : ℕ) (hK : K ≤ y) (hW : W ≤ y) (hx : x ≤ y) (hQ15 : Q + 3 ≤ y)
    (hQ2 : Q + 2 ≤ x) :
    (Q ^ 2 : ℝ≥0∞) / 2 ^ 508 + 2 * ((Q + 3 : ℕ) : ℝ≥0∞) ^ 2 / 2 ^ 576 +
        ((K : ℝ≥0∞) ^ 2 / 2 ^ 508 + 2 * ((Q + 3 : ℕ) : ℝ≥0∞) ^ 2 / 2 ^ 576) +
        (W : ℝ≥0∞) ^ 2 / 2 ^ 256 +
        ((x : ℝ≥0∞) / 2 ^ 95 + (x : ℝ≥0∞) ^ 2 / 2 ^ 159 + ((Q + 2 : ℕ) : ℝ≥0∞) / 2 ^ 89) ≤
      (x : ℝ≥0∞) / 2 ^ 88 + (y : ℝ≥0∞) ^ 2 / 2 ^ 158 := by
  rw [← ENNReal.toReal_le_toReal (by finiteness) (by finiteness)]
  simp only [ENNReal.toReal_mul, ENNReal.toReal_add, ENNReal.toReal_pow, ENNReal.toReal_div,
    ENNReal.toReal_natCast, ENNReal.toReal_ofNat, ne_eq, ENNReal.div_eq_top,
    ENNReal.natCast_ne_top, ENNReal.pow_eq_top_iff, ENNReal.ofNat_ne_top, false_and, and_false,
    or_self, not_false_eq_true, ENNReal.mul_eq_top, pow_eq_zero_iff, OfNat.ofNat_ne_zero,
    ENNReal.add_eq_top]
  push_cast
  have hK' : (K : ℝ) ≤ y := by exact_mod_cast hK
  have hW' : (W : ℝ) ≤ y := by exact_mod_cast hW
  have hx' : (x : ℝ) ≤ y := by exact_mod_cast hx
  have hQ15' : (Q : ℝ) + 3 ≤ y := by exact_mod_cast hQ15
  have hQ2' : (Q : ℝ) + 2 ≤ x := by exact_mod_cast hQ2
  have hQ0 : (0 : ℝ) ≤ Q := Nat.cast_nonneg Q
  have hK0 : (0 : ℝ) ≤ K := Nat.cast_nonneg K
  have hW0 : (0 : ℝ) ≤ W := Nat.cast_nonneg W
  have hx0 : (0 : ℝ) ≤ x := Nat.cast_nonneg x
  have hy2 : (Q : ℝ) ^ 2 ≤ (y : ℝ) ^ 2 := by nlinarith
  have hK2 : (K : ℝ) ^ 2 ≤ (y : ℝ) ^ 2 := by nlinarith
  have hW2 : (W : ℝ) ^ 2 ≤ (y : ℝ) ^ 2 := by nlinarith
  have hx2 : (x : ℝ) ^ 2 ≤ (y : ℝ) ^ 2 := by nlinarith
  have h152 : ((Q : ℝ) + 3) ^ 2 ≤ (y : ℝ) ^ 2 := by nlinarith
  have hy0 : (0 : ℝ) ≤ (y : ℝ) ^ 2 := sq_nonneg _
  have e1 : (Q : ℝ) ^ 2 / 2 ^ 508 ≤ (y : ℝ) ^ 2 / 2 ^ 508 := by gcongr
  have e2 : 2 * ((Q : ℝ) + 3) ^ 2 / 2 ^ 576 ≤ 2 * (y : ℝ) ^ 2 / 2 ^ 576 := by gcongr
  have e3 : (K : ℝ) ^ 2 / 2 ^ 508 ≤ (y : ℝ) ^ 2 / 2 ^ 508 := by gcongr
  have e4 : (W : ℝ) ^ 2 / 2 ^ 256 ≤ (y : ℝ) ^ 2 / 2 ^ 256 := by gcongr
  have e5 : (x : ℝ) ^ 2 / 2 ^ 159 ≤ (y : ℝ) ^ 2 / 2 ^ 159 := by gcongr
  have e6 : ((Q : ℝ) + 2) / 2 ^ 89 ≤ (x : ℝ) / 2 ^ 89 := by gcongr
  have hsum : (y : ℝ) ^ 2 / 2 ^ 508 + 2 * (y : ℝ) ^ 2 / 2 ^ 576 + ((y : ℝ) ^ 2 / 2 ^ 508 +
      2 * (y : ℝ) ^ 2 / 2 ^ 576) + (y : ℝ) ^ 2 / 2 ^ 256 + (y : ℝ) ^ 2 / 2 ^ 159 ≤
        (y : ℝ) ^ 2 / 2 ^ 158 := by
    have c1 : (y : ℝ) ^ 2 / 2 ^ 508 ≤ (y : ℝ) ^ 2 / 2 ^ 256 :=
      div_le_div_of_nonneg_left hy0 (by positivity) (pow_le_pow_right₀ (by norm_num) (by norm_num))
    have c2 : 2 * (y : ℝ) ^ 2 / 2 ^ 576 ≤ (y : ℝ) ^ 2 / 2 ^ 256 := by
      rw [div_le_div_iff₀ (by positivity) (by positivity), mul_comm (2 : ℝ), mul_assoc,
        ← pow_succ']
      exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by norm_num) (by norm_num)) hy0
    have c3 : 5 * ((y : ℝ) ^ 2 / 2 ^ 256) + (y : ℝ) ^ 2 / 2 ^ 159 ≤ (y : ℝ) ^ 2 / 2 ^ 158 := by
      have h : (5 : ℝ) / 2 ^ 256 + 1 / 2 ^ 159 ≤ 1 / 2 ^ 158 := by norm_num
      have := mul_le_mul_of_nonneg_left h hy0
      calc 5 * ((y : ℝ) ^ 2 / 2 ^ 256) + (y : ℝ) ^ 2 / 2 ^ 159
          = (y : ℝ) ^ 2 * (5 / 2 ^ 256 + 1 / 2 ^ 159) := by ring
        _ ≤ (y : ℝ) ^ 2 * (1 / 2 ^ 158) := this
        _ = (y : ℝ) ^ 2 / 2 ^ 158 := by ring
    generalize (y : ℝ) ^ 2 / 2 ^ 508 = A at c1 ⊢
    generalize 2 * (y : ℝ) ^ 2 / 2 ^ 576 = B at c2 ⊢
    generalize (y : ℝ) ^ 2 / 2 ^ 256 = C at c1 c2 c3 ⊢
    linarith only [c1, c2, c3]

  have hlin : (x : ℝ) / 2 ^ 95 + (x : ℝ) / 2 ^ 89 ≤ (x : ℝ) / 2 ^ 88 := by
    have : (1 : ℝ) / 2 ^ 95 + 1 / 2 ^ 89 ≤ 1 / 2 ^ 88 := by norm_num
    have := mul_le_mul_of_nonneg_left this hx0
    ring_nf at this ⊢
    linarith
  generalize (Q : ℝ) ^ 2 / 2 ^ 508 = a₁ at e1 ⊢
  generalize (K : ℝ) ^ 2 / 2 ^ 508 = a₂ at e3 ⊢
  generalize 2 * ((Q : ℝ) + 3) ^ 2 / 2 ^ 576 = a₃ at e2 ⊢
  generalize (y : ℝ) ^ 2 / 2 ^ 508 = b₁ at e1 e3 hsum
  generalize 2 * (y : ℝ) ^ 2 / 2 ^ 576 = b₂ at e2 hsum
  linarith only [e1, e2, e3, e4, e5, e6, hsum, hlin]

end LeanDa
