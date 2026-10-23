import XmssSecurity.Scan.Moment
import Mathlib.Basic.ENNReal.Real
import Mathlib.Basic.ENNReal.Operations

/-!
# The quadratic potential in `ℝ≥0∞`

`F3` is `Λ + A n` with the remaining budget `Q - k`, and `⊤` once the count passes the budget. It is a
supermartingale of an encoding step up to `A`, and bounds `V (p n + (1 - p) V)` by `p² F3`.
-/

open ENNReal

namespace XmssSecurity.Partner

noncomputable def F3 (p : ℝ) (Q n v k : ℕ) : ℝ≥0∞ :=
  if n ≤ Q then ENNReal.ofReal (Λ p Q v n n (Q - k) + momentA p Q * n) else ⊤

variable {p : ℝ} {Q : ℕ}

theorem F3_zero (p : ℝ) (Q : ℕ) : F3 p Q 0 0 0 = 0 := by
  simp [F3, Λ_zero]

theorem Λ_add_nonneg (hp0 : 0 < p) (hp1 : p ≤ 1) {n v : ℕ} (k : ℕ) (hn : n ≤ Q) :
    0 ≤ Λ p Q v n n (Q - k) + momentA p Q * n := by
  have h := final_bound (V := v) (C := n) (Q - k) (by linarith) hn
  have : 0 ≤ (v / p : ℝ) * n + (1 - p) * (v / p) ^ 2 := by
    have : (0 : ℝ) ≤ 1 - p := by linarith
    positivity
  linarith

theorem F3_budget {n v k : ℕ} (hk : k < Q) : F3 p Q n v (k + 1) ≤ F3 p Q n v k := by
  unfold F3
  split_ifs
  · refine ENNReal.ofReal_le_ofReal ?_
    have h := budget_step p (V := v) (C := n) (n := n) (Q := Q) (F := Q - k) (by omega)
    rw [show Q - k - 1 = Q - (k + 1) by omega] at h
    linarith
  · exact le_rfl

theorem F3_encoding (hp : 1 / 2 ^ 21 ≤ p) (hp' : p ≤ 1 / 2 ^ 20) (hQ : Q ≤ 2 ^ 127) {n v k : ℕ}
    (hn : n ≤ k) (hk : k < Q) :
    ENNReal.ofReal p * F3 p Q (n + 1) (v + 1) (k + 1) + ENNReal.ofReal (1 - p) * F3 p Q (n + 1) v (k + 1) ≤
      F3 p Q n v k + ENNReal.ofReal (momentA p Q) := by
  have hp0 : 0 < p := lt_of_lt_of_le (by positivity) hp
  have hp1 : p ≤ 1 := hp'.trans (by norm_num)
  have hn1 : n + 1 ≤ Q := by omega
  have hnQ : n ≤ Q := by omega
  have hA : 0 ≤ momentA p Q := by unfold momentA momentK; have : (0 : ℝ) ≤ 2 - p := by linarith
                                  positivity
  unfold F3
  rw [ite_eq_left hn1, ite_eq_left hn1, ite_eq_left hnQ, ← ENNReal.ofReal_mul hp0.le, ← ENNReal.ofReal_mul (by linarith),
    ← ENNReal.ofReal_add (mul_nonneg hp0.le (Λ_add_nonneg hp0 hp1 _ hn1))
      (mul_nonneg (by linarith) (Λ_add_nonneg hp0 hp1 _ hn1)),
    ← ENNReal.ofReal_add (Λ_add_nonneg hp0 hp1 _ hnQ) hA]
  refine ENNReal.ofReal_le_ofReal ?_
  have h := encoding_step (V := v) (C := n) (n := n) (F := Q - k) hp hp' hQ le_rfl (by omega) (by omega)
  rw [show Q - k - 1 = Q - (k + 1) by omega] at h
  push_cast
  nlinarith

/-- **The pointwise bound.** -/
theorem ofReal_le_F3 (hp0 : 0 < p) (hp1 : p ≤ 1) (n v k : ℕ) :
    ENNReal.ofReal (p * v * n + (1 - p) * v ^ 2) ≤ ENNReal.ofReal (p ^ 2) * F3 p Q n v k := by
  unfold F3
  split_ifs with hn
  · rw [← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    have h := final_bound (V := v) (C := n) (Q - k) (by linarith) hn
    have hid : p * v * n + (1 - p) * v ^ 2 = p ^ 2 * ((v / p : ℝ) * n + (1 - p) * (v / p) ^ 2) := by
      field_simp
    rw [hid]
    exact mul_le_mul_of_nonneg_left h (by positivity)
  · rw [ENNReal.mul_top (ENNReal.ofReal_pos.mpr (by positivity)).ne']
    exact le_top

end XmssSecurity.Partner
