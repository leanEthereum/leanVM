module

public import Quantum.Qrom.Sphincs.Costs.Total

@[expose] public section

/-!
# The classical costs of the `n`-user leanSPHINCS runtime 2: the closed form

With the memo no counter search reads a selected key, so the averaged costs bound is the pinned
`twBoundQ` at re-grind weights `0`, with the recorded unselected mass `tauUN q K = q 2^-128 +
K 2^-1000` (first reveals per owner, failed searches).

* `twBoundQ_tauUN_le`: for `q ≤ 2^64` and `K ≤ 2^98` classical calls,
  `twBoundQ encC encEps q K (tauUN q K) 0 0 ≤ ((257.1 √q + 0.1) / 2^64)²`.
-/

open scoped ENNReal

namespace Quantum.Qrom.Sphincs.Multi

/-- **The averaged recorded unselected mass of `n` users**: `q 2^-128 + K 2^-1000`. -/
noncomputable def tauUN (q K : ℕ) : ℝ≥0∞ :=
  q * (2 ^ 128 : ℝ≥0∞)⁻¹ + K * (2 ^ 1000 : ℝ≥0∞)⁻¹

/-- `aCap` at `tauUN` without re-grind weights, over the reals. -/
noncomputable def aRN (q K : ℕ) : ℝ :=
  (2 ^ 127)⁻¹ * (2 ^ 15 * ((q : ℝ) + 4 * ((q + K : ℕ) : ℝ) * (q * (2 ^ 128)⁻¹ +
    K * (2 ^ 1000)⁻¹) + ((q + K : ℕ) : ℝ) * K * (2 ^ 510)⁻¹) + (2 ^ 128)⁻¹ * ((0 : ℕ) : ℝ)) +
    2 / Fintype.card PairOut * K

theorem aCap_tauUN_eq (q K : ℕ) :
    aCap encC encEps q K (tauUN q K) 0 = ENNReal.ofReal (aRN q K) := by
  rw [aCap, encCap, encC, encEps, tauUN, aRN]
  ofReal_pushS

theorem pCap_tauUN_eq (q K : ℕ) :
    pCap (tauUN q K) 0 = ENNReal.ofReal ((q : ℝ) * (2 ^ 128)⁻¹ + K * (2 ^ 1000)⁻¹ +
      (2 ^ 128)⁻¹ * ((0 : ℕ) : ℝ)) := by
  rw [pCap, tauUN]
  ofReal_pushS

set_option exponentiation.threshold 2048 in
theorem aRN_le {q K : ℕ} (hq : q ≤ 2 ^ 64) (hK : K ≤ 2 ^ 98) :
    aRN q K ≤ (1.0001 * (2 ^ 56)⁻¹) ^ 2 * q + ((2 ^ 80)⁻¹) ^ 2 := by
  have hqR : (q : ℝ) ≤ 2 ^ 64 := by exact_mod_cast hq
  have hKR : (K : ℝ) ≤ 2 ^ 98 := by exact_mod_cast hK
  have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  have hK0 : (0 : ℝ) ≤ K := Nat.cast_nonneg K
  have hqK : ((q + K : ℕ) : ℝ) ≤ 2 ^ 64 + 2 ^ 98 := by push_cast; linarith
  have hqK0 : (0 : ℝ) ≤ ((q + K : ℕ) : ℝ) := Nat.cast_nonneg _
  have h1 : ((q + K : ℕ) : ℝ) * (q * (2 ^ 128)⁻¹ + K * (2 ^ 1000)⁻¹) ≤
      (2 ^ 64 + 2 ^ 98) * (q * (2 ^ 128)⁻¹ + 2 ^ 98 * (2 ^ 1000)⁻¹) :=
    mul_le_mul hqK (by nlinarith) (by positivity) (by positivity)
  have h2 : ((q + K : ℕ) : ℝ) * K ≤ (2 ^ 64 + 2 ^ 98) * 2 ^ 98 :=
    mul_le_mul hqK hKR hK0 (by positivity)
  have hc : (2 : ℝ) / Fintype.card PairOut = 2 * (2 ^ 512)⁻¹ := by
    rw [card_pairOut_real, div_eq_mul_inv]
    norm_num
  unfold aRN
  rw [hc]
  push_cast
  nlinarith

set_option exponentiation.threshold 2048 in
theorem pRN_le {q K : ℕ} (hK : K ≤ 2 ^ 98) :
    (q : ℝ) * (2 ^ 128)⁻¹ + K * (2 ^ 1000)⁻¹ + (2 ^ 128)⁻¹ * ((0 : ℕ) : ℝ) ≤
      ((2 ^ 64)⁻¹) ^ 2 * q + ((2 ^ 451)⁻¹) ^ 2 := by
  have hKR : (K : ℝ) ≤ 2 ^ 98 := by exact_mod_cast hK
  have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  push_cast
  nlinarith

set_option exponentiation.threshold 2048 in
/-- **The closed form of the averaged costs of `n` users**: for `q ≤ 2^64` and `K ≤ 2^98`,
`twBoundQ encC encEps q K (tauUN q K) 0 0 ≤ ((257.1 √q + 0.1) / 2^64)²`. -/
theorem twBoundQ_tauUN_le {q K : ℕ} (hq : q ≤ 2 ^ 64) (hK : K ≤ 2 ^ 98) :
    twBoundQ encC encEps q K (tauUN q K) 0 0 ≤
      ENNReal.ofReal (((257.1 * √(q : ℝ) + 0.1) / 2 ^ 64) ^ 2) := by
  have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  refine (twBoundQ_le_of (c₁ := 1.0001 * (2 ^ 56)⁻¹) (c₂ := (2 ^ 64)⁻¹) (a₀ := (2 ^ 80)⁻¹)
    (p₀ := (2 ^ 451)⁻¹) (by positivity) (by positivity) (by positivity) (by positivity) ?_ ?_).trans
    ?_
  · rw [aCap_tauUN_eq]
    exact ENNReal.ofReal_le_ofReal (aRN_le hq hK)
  · rw [pCap_tauUN_eq]
    exact ENNReal.ofReal_le_ofReal (pRN_le hK)
  · refine ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (by positivity) ?_ 2)
    rw [le_div_iff₀ (by positivity)]
    nlinarith [Real.sqrt_nonneg (q : ℝ)]

end Quantum.Qrom.Sphincs.Multi

end
