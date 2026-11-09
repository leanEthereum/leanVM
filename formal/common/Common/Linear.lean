module

public import Mathlib.Basic.ENNReal.Inv
public import Mathlib.Tactic.GCongr
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.NormNum

@[expose] public section

/-!
# A quadratic transfer term, linear under a query cap

The random-permutation transfers and the sponge's indifferentiability cost `q² / 2^n` for `q`
permutation calls, with `n` about `508`. Under a cap `q ≤ 2^k` this is at most `q · 2^-(n - k)`, a
term linear in `q` (`sq_div_le_mul_inv_pow`, with `n = k + e`). The end statements state their
bounds in bits: `bits_add_sq_le` and `sq_add_sq_le` fold the transfer terms into them.
-/

open scoped ENNReal

namespace Common

/-- **A quadratic term, linear under a cap**: for `q ≤ 2^k`, `q² / 2^(k + e) ≤ q · 2^-e`. -/
theorem sq_div_le_mul_inv_pow {q k : ℕ} (e : ℕ) (hq : q ≤ 2 ^ k) :
    (q : ℝ≥0∞) ^ 2 / 2 ^ (k + e) ≤ (q : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ e := by
  have hq' : (q : ℝ≥0∞) ≤ 2 ^ k := by exact_mod_cast hq
  have h2k : (2 : ℝ≥0∞) ^ k ≠ 0 := pow_ne_zero _ two_ne_zero
  have h2k' : (2 : ℝ≥0∞) ^ k ≠ ⊤ := ENNReal.pow_ne_top ENNReal.ofNat_ne_top
  calc (q : ℝ≥0∞) ^ 2 / 2 ^ (k + e) ≤ (q : ℝ≥0∞) * 2 ^ k / (2 ^ e * 2 ^ k) := by
        rw [pow_two, pow_add, mul_comm ((2 : ℝ≥0∞) ^ k) ((2 : ℝ≥0∞) ^ e)]
        gcongr
    _ = (q : ℝ≥0∞) / 2 ^ e := ENNReal.mul_div_mul_right _ _ h2k h2k'
    _ = (q : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ e := by rw [div_eq_mul_inv, ENNReal.inv_pow]

/-- `2^a · 2^-(a + b) = 2^-b`. -/
theorem two_pow_mul_inv_pow (a b : ℕ) :
    (2 : ℝ≥0∞) ^ a * (2 : ℝ≥0∞)⁻¹ ^ (a + b) = (2 : ℝ≥0∞)⁻¹ ^ b := by
  rw [pow_add, ← mul_assoc, ← mul_pow,
    ENNReal.mul_inv_cancel two_ne_zero ENNReal.ofNat_ne_top, one_pow, one_mul]

/-- `2^-b ≤ 2^-a` for `a ≤ b`. -/
theorem inv_two_pow_le_of_le {a b : ℕ} (h : a ≤ b) : (2 : ℝ≥0∞)⁻¹ ^ b ≤ (2 : ℝ≥0∞)⁻¹ ^ a :=
  pow_le_pow_of_le_one zero_le (ENNReal.inv_le_one.2 one_le_two) h

/-- `1 ≤ x · 2^-b` once `2^b ≤ x`: a bound past one, which every probability meets. -/
theorem one_le_mul_inv_two_pow {x : ℝ≥0∞} {b : ℕ} (h : (2 : ℝ≥0∞) ^ b ≤ x) :
    1 ≤ x * (2 : ℝ≥0∞)⁻¹ ^ b :=
  calc (1 : ℝ≥0∞) = (2 : ℝ≥0∞) ^ b * (2 : ℝ≥0∞)⁻¹ ^ b := by
        rw [← mul_pow, ENNReal.mul_inv_cancel two_ne_zero ENNReal.ofNat_ne_top, one_pow]
    _ ≤ x * (2 : ℝ≥0∞)⁻¹ ^ b := mul_le_mul_left h _

/-- **The bound `(Q + 1) · 2^-bits` past `Q = 2^128`**, for `bits ≤ 128`: it is at least one, so
every probability `p` meets it. -/
theorem le_succ_mul_inv_two_pow_of_lt {p : ℝ≥0∞} (hp : p ≤ 1) {Q bits : ℕ} (hb : bits ≤ 128)
    (hQ : 2 ^ 128 < Q) : p ≤ ((Q : ℝ≥0∞) + 1) * (2 : ℝ≥0∞)⁻¹ ^ bits := by
  refine hp.trans (one_le_mul_inv_two_pow ?_)
  calc (2 : ℝ≥0∞) ^ bits ≤ 2 ^ 128 := pow_le_pow_right₀ one_le_two hb
    _ ≤ (Q : ℝ≥0∞) := by exact_mod_cast hQ.le
    _ ≤ (Q : ℝ≥0∞) + 1 := le_self_add

/-- **A signature bound in bits**: for `Q ≤ 2^128` and `bits ≤ 253`,
`Q / 2^bits + Q² / 2^509 ≤ (Q + 1) · 2^-bits`. -/
theorem bits_add_sq_le {Q bits : ℕ} (hQ : Q ≤ 2 ^ 128) (hb : bits ≤ 253) :
    (Q : ℝ≥0∞) / ((2 ^ bits : ℕ) : ℝ≥0∞) + (Q : ℝ≥0∞) ^ 2 / 2 ^ 509 ≤
      ((Q : ℝ≥0∞) + 1) * (2 : ℝ≥0∞)⁻¹ ^ bits := by
  have h1 : (Q : ℝ≥0∞) / ((2 ^ bits : ℕ) : ℝ≥0∞) = (Q : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ bits := by
    rw [Nat.cast_pow, Nat.cast_ofNat, div_eq_mul_inv, ENNReal.inv_pow]
  have h2 : (Q : ℝ≥0∞) ^ 2 / 2 ^ 509 ≤ (2 : ℝ≥0∞)⁻¹ ^ bits :=
    calc (Q : ℝ≥0∞) ^ 2 / 2 ^ 509 ≤ (Q : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ 381 :=
          sq_div_le_mul_inv_pow (k := 128) 381 hQ
      _ ≤ (2 : ℝ≥0∞) ^ 128 * (2 : ℝ≥0∞)⁻¹ ^ 381 := by
          gcongr
          exact_mod_cast hQ
      _ = (2 : ℝ≥0∞)⁻¹ ^ 253 := two_pow_mul_inv_pow 128 253
      _ ≤ (2 : ℝ≥0∞)⁻¹ ^ bits := inv_two_pow_le_of_le hb
  calc (Q : ℝ≥0∞) / ((2 ^ bits : ℕ) : ℝ≥0∞) + (Q : ℝ≥0∞) ^ 2 / 2 ^ 509
      ≤ (Q : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ bits + (2 : ℝ≥0∞)⁻¹ ^ bits := by
        rw [h1]
        exact add_le_add le_rfl h2
    _ = ((Q : ℝ≥0∞) + 1) * (2 : ℝ≥0∞)⁻¹ ^ bits := by rw [add_mul, one_mul]

/-- **A birthday bound and a transfer term in bits**: for `Q ≤ 2^128`,
`Q² / 2^256 + Q² / 2^508 ≤ (Q + 1)² · 2^-256`. -/
theorem sq_add_sq_le {Q : ℕ} (hQ : Q ≤ 2 ^ 128) :
    (Q : ℝ≥0∞) ^ 2 / 2 ^ 256 + (Q : ℝ≥0∞) ^ 2 / 2 ^ 508 ≤
      ((Q : ℝ≥0∞) + 1) ^ 2 * (2 : ℝ≥0∞)⁻¹ ^ 256 := by
  have h2 : (Q : ℝ≥0∞) ^ 2 / 2 ^ 508 ≤ (Q : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ 256 :=
    (sq_div_le_mul_inv_pow (k := 128) 380 hQ).trans (by
      gcongr _ * ?_
      exact inv_two_pow_le_of_le (by norm_num))
  have h3 : (Q : ℝ≥0∞) ^ 2 + Q ≤ ((Q : ℝ≥0∞) + 1) ^ 2 := by
    have h : ((Q ^ 2 + Q : ℕ) : ℝ≥0∞) ≤ (((Q + 1) ^ 2 : ℕ) : ℝ≥0∞) :=
      Nat.cast_le.2 (by rw [show (Q + 1) ^ 2 = Q ^ 2 + Q + (Q + 1) by ring]; exact Nat.le_add_right _ _)
    push_cast at h
    exact h
  calc (Q : ℝ≥0∞) ^ 2 / 2 ^ 256 + (Q : ℝ≥0∞) ^ 2 / 2 ^ 508
      ≤ (Q : ℝ≥0∞) ^ 2 * (2 : ℝ≥0∞)⁻¹ ^ 256 + (Q : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ 256 := by
        rw [div_eq_mul_inv ((Q : ℝ≥0∞) ^ 2) ((2 : ℝ≥0∞) ^ 256), ENNReal.inv_pow]
        exact add_le_add le_rfl h2
    _ = ((Q : ℝ≥0∞) ^ 2 + Q) * (2 : ℝ≥0∞)⁻¹ ^ 256 := (add_mul _ _ _).symm
    _ ≤ ((Q : ℝ≥0∞) + 1) ^ 2 * (2 : ℝ≥0∞)⁻¹ ^ 256 := by gcongr

end Common
