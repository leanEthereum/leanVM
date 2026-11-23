module

public import Quantum.Qrom.Xmss.Multi.Security
public import Quantum.Qrom.Xmss.BoundValue

@[expose] public section

/-!
# The size of the multi-user leanXMSS QROM bound

Security's `xmssQromMuBound n total q` in closed form for `total, q ≤ 2^64` and every `n`
(`xmssQromMuBound_le`):
`xmssQromMuBound n total q ≤ 1.5 n² / 2^128 + ((4.45 q + 0.61 · 2^17 √q + 2^9) / 2^64)²`.
Nothing depends on `n` or `total` but the collision term. Each term is bounded by a real number:

* the collisions `collTermN n = 3 · C(n, 2) · 2^-128 ≤ 1.5 n² 2^-128` (`collTermN_le`);
* the single-user terms (`advTermQ_le`, `verTermQ_le`, `verLinQ_le`, `readErrQ_le`,
  `hybTermQ_le`);
* the prefix's classical costs `clsBoundQN n total q ≤ ((0.6 · 2^17 √q + 1) / 2^64)²` (Costs'
  `twBoundQ_le_mu`, `clsCapN n total ≤ 2^98`).

Corollaries: at most `2^-62` for `q ≤ 2^30` and `n ≤ 2^31`, `2^-43` for `q ≤ 2^40` and
`n ≤ 2^32`, `2^-23` for `q ≤ 2^50` and `n ≤ 2^40`, all for `total ≤ 2^64`; for one user
(`xmssQromMuBound_one_le`) `((4.45 q + 0.61 · 2^17 √q + 2^9) / 2^64)²`, below the single-user
`xmssQromBound`'s closed form.
-/

open scoped ENNReal

namespace Quantum.Qrom.Xmss.Multi

open Quantum QuantumRuntime Quantum.Xmss.Hybrid
open LeanXmss HashSig

variable {n total q : ℕ}

/-! ## The terms -/

section terms

set_option exponentiation.threshold 1100

/-- **The collision term**: `collTermN n ≤ 1.5 n² 2^-128`. -/
theorem collTermN_le (n : ℕ) : collTermN n ≤ ENNReal.ofReal (1.5 * (n : ℝ) ^ 2 / 2 ^ 128) := by
  have hc : ((n.choose 2 : ℕ) : ℝ) ≤ (n : ℝ) ^ 2 / 2 := by
    rw [Nat.cast_choose_two]
    nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  unfold collTermN
  simp (disch := positivity) only [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_ofNat,
    ← ENNReal.ofReal_pow, ← ENNReal.ofReal_inv_of_pos, ← ENNReal.ofReal_mul]
  refine ENNReal.ofReal_le_ofReal ?_
  have h2 : (0 : ℝ) < (2 ^ 128)⁻¹ := by positivity
  rw [div_eq_mul_inv]
  nlinarith

/-- **The prefix's classical costs** (Costs' `twBoundQ_le_mu`): for `total, q ≤ 2^64`,
`clsBoundQN n total q ≤ ((0.6 · 2^17 √q + 1) / 2^64)²`. -/
theorem clsBoundQN_le (ht : total ≤ 2 ^ 64) (hq : q ≤ 2 ^ 64) :
    clsBoundQN n total q ≤ ENNReal.ofReal (((0.6 * 2 ^ 17 * √(q : ℝ) + 1) / 2 ^ 64) ^ 2) :=
  twBoundQ_le_mu hq (clsCapN_le ht)

/-- **The square-rooted event term**: for `total, q ≤ 2^64`, `√eventTermQN n total q ≤
2.45 q 2^-64 + 384 · 2^-64 + ((0.6 · 2^17 √q + 1) / 2^64 + 20 · 2^-64) + 2^-120`. -/
theorem eventTermQN_rpow_le (ht : total ≤ 2 ^ 64) (hq : q ≤ 2 ^ 64) :
    eventTermQN n total q ^ (2⁻¹ : ℝ) ≤ ENNReal.ofReal (2.45 * q / 2 ^ 64 + 384 / 2 ^ 64 +
      ((0.6 * 2 ^ 17 * √(q : ℝ) + 1) / 2 ^ 64 + 20 / 2 ^ 64) + 1 / 2 ^ 120) := by
  have hr := rpow_inv_two_le_ofRealQ (a := 1 / 2 ^ 120) (by positivity) readErrQ_le
    (by norm_num)
  have hc := rpow_inv_two_le_ofRealQ (by positivity) (clsBoundQN_le (n := n) ht hq) le_rfl
  have hv := rpow_inv_two_le_ofRealQ (a := 20 / 2 ^ 64) (by positivity) verLinQ_le
    (by norm_num)
  have hcv : (clsBoundQN n total q + verLinQ) ^ (2⁻¹ : ℝ) ≤
      ENNReal.ofReal ((0.6 * 2 ^ 17 * √(q : ℝ) + 1) / 2 ^ 64 + 20 / 2 ^ 64) := by
    rw [ENNReal.ofReal_add (by positivity) (by positivity)]
    exact (ENNReal.rpow_add_le_add_rpow _ _ (by norm_num) (by norm_num)).trans
      (add_le_add hc hv)
  unfold eventTermQN
  refine (sq_add_rpow_inv_two_leQ _ _).trans ((add_le_add (add_le_add (add_le_add
    (advTermQ_le q) verTermQ_le) hcv) hr).trans_eq ?_)
  rw [← ENNReal.ofReal_add (by positivity) (by positivity),
    ← ENNReal.ofReal_add (by positivity) (by positivity),
    ← ENNReal.ofReal_add (by positivity) (by positivity)]

end terms

/-! ## The closed form -/

section closed

/-- The arithmetic of the closed form. -/
theorem root_le_closedQN (q : ℕ) :
    2.45 * q / 2 ^ 64 + 384 / 2 ^ 64 +
      ((0.6 * 2 ^ 17 * √(q : ℝ) + 1) / 2 ^ 64 + 20 / 2 ^ 64) + 1 / 2 ^ 120 +
        (2 * q / 2 ^ 64 + 20 / 2 ^ 64) ≤
      (4.45 * q + 0.61 * 2 ^ 17 * √(q : ℝ) + 2 ^ 9) / 2 ^ 64 := by
  have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  have hs0 := Real.sqrt_nonneg (q : ℝ)
  linarith

/-- The square-rooted part of the bound, without the collisions. -/
theorem rpow_add_hybTermQ_le (ht : total ≤ 2 ^ 64) (hq : q ≤ 2 ^ 64) :
    (eventTermQN n total q ^ (2⁻¹ : ℝ) + hybTermQ q) ^ 2 ≤
      ENNReal.ofReal (((4.45 * q + 0.61 * 2 ^ 17 * √(q : ℝ) + 2 ^ 9) / 2 ^ 64) ^ 2) := by
  rw [ENNReal.ofReal_pow (by positivity)]
  refine pow_le_pow_left₀ zero_le ((add_le_add (eventTermQN_rpow_le (n := n) ht hq)
    (hybTermQ_le q)).trans ?_) 2
  rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
  exact ENNReal.ofReal_le_ofReal (root_le_closedQN q)

/-- **The multi-user leanXMSS QROM bound in closed form**: for `total, q ≤ 2^64`,
`xmssQromMuBound n total q ≤ 1.5 n² / 2^128 + ((4.45 q + 0.61 · 2^17 √q + 2^9) / 2^64)²`. -/
theorem xmssQromMuBound_le (ht : total ≤ 2 ^ 64) (hq : q ≤ 2 ^ 64) :
    xmssQromMuBound n total q ≤ ENNReal.ofReal (1.5 * (n : ℝ) ^ 2 / 2 ^ 128 +
      ((4.45 * q + 0.61 * 2 ^ 17 * √(q : ℝ) + 2 ^ 9) / 2 ^ 64) ^ 2) := by
  rw [ENNReal.ofReal_add (by positivity) (by positivity)]
  exact add_le_add (collTermN_le n) (rpow_add_hybTermQ_le ht hq)

/-- **One user**: for `q ≤ 2^64`,
`xmssQromMuBound 1 lifetime q ≤ ((4.45 q + 0.61 · 2^17 √q + 2^9) / 2^64)²`, the bound of
`leanXmss_qrom_security_one`. -/
theorem xmssQromMuBound_one_le (hq : q ≤ 2 ^ 64) :
    xmssQromMuBound 1 lifetime q ≤
      ENNReal.ofReal (((4.45 * q + 0.61 * 2 ^ 17 * √(q : ℝ) + 2 ^ 9) / 2 ^ 64) ^ 2) := by
  have h0 : collTermN 1 = 0 := by simp [collTermN]
  unfold xmssQromMuBound
  rw [h0, zero_add]
  exact rpow_add_hybTermQ_le (by rw [lifetime_eq]; norm_num) hq

/-- The closed form at bounded `n` and `q`. -/
theorem xmssQromMuBound_le_of_le {N Q : ℝ} {k : ℕ} (ht : total ≤ 2 ^ 64) (hq : q ≤ 2 ^ 64)
    (hN : (n : ℝ) ≤ N) (hQ : (q : ℝ) ≤ Q ^ 2) (hQ0 : 0 ≤ Q)
    (h : 1.5 * N ^ 2 / 2 ^ 128 + ((4.45 * Q ^ 2 + 0.61 * 2 ^ 17 * Q + 2 ^ 9) / 2 ^ 64) ^ 2 ≤
      1 / 2 ^ k) :
    xmssQromMuBound n total q ≤ (2 ^ k : ℝ≥0∞)⁻¹ := by
  have hs : √(q : ℝ) ≤ Q := (Real.sqrt_le_sqrt hQ).trans_eq (Real.sqrt_sq hQ0)
  refine (xmssQromMuBound_le ht hq).trans ?_
  rw [inv_two_pow_eq_ofRealQ]
  refine ENNReal.ofReal_le_ofReal (le_trans ?_ h)
  gcongr

set_option exponentiation.threshold 1100 in
/-- **At most `2^30` hash calls and `2^31` users**: `xmssQromMuBound n total q ≤ 2^-62`. -/
theorem xmssQromMuBound_two_pow_30_le (hn : n ≤ 2 ^ 31) (ht : total ≤ 2 ^ 64)
    (hq : q ≤ 2 ^ 30) : xmssQromMuBound n total q ≤ (2 ^ 62 : ℝ≥0∞)⁻¹ :=
  xmssQromMuBound_le_of_le (N := 2 ^ 31) (Q := 2 ^ 15) ht (hq.trans (by norm_num))
    (by exact_mod_cast hn)
    ((by exact_mod_cast hq : (q : ℝ) ≤ 2 ^ 30).trans_eq (by norm_num)) (by norm_num) (by norm_num)

set_option exponentiation.threshold 1100 in
/-- **At most `2^40` hash calls and `2^32` users**: `xmssQromMuBound n total q ≤ 2^-43`. -/
theorem xmssQromMuBound_two_pow_40_le (hn : n ≤ 2 ^ 32) (ht : total ≤ 2 ^ 64)
    (hq : q ≤ 2 ^ 40) : xmssQromMuBound n total q ≤ (2 ^ 43 : ℝ≥0∞)⁻¹ :=
  xmssQromMuBound_le_of_le (N := 2 ^ 32) (Q := 2 ^ 20) ht (hq.trans (by norm_num))
    (by exact_mod_cast hn)
    ((by exact_mod_cast hq : (q : ℝ) ≤ 2 ^ 40).trans_eq (by norm_num)) (by norm_num) (by norm_num)

set_option exponentiation.threshold 1100 in
/-- **At most `2^50` hash calls and `2^40` users**: `xmssQromMuBound n total q ≤ 2^-23`. -/
theorem xmssQromMuBound_two_pow_50_le (hn : n ≤ 2 ^ 40) (ht : total ≤ 2 ^ 64)
    (hq : q ≤ 2 ^ 50) : xmssQromMuBound n total q ≤ (2 ^ 23 : ℝ≥0∞)⁻¹ :=
  xmssQromMuBound_le_of_le (N := 2 ^ 40) (Q := 2 ^ 25) ht (hq.trans (by norm_num))
    (by exact_mod_cast hn)
    ((by exact_mod_cast hq : (q : ℝ) ≤ 2 ^ 50).trans_eq (by norm_num)) (by norm_num) (by norm_num)

end closed

end Quantum.Qrom.Xmss.Multi

end
