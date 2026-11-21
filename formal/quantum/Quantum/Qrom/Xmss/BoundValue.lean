module

public import Quantum.Qrom.Xmss.Security

@[expose] public section

/-!
# The size of the leanXMSS QROM bound

Security's `xmssQromBound q` in closed form for `q ≤ 2^64` (`xmssQromBound_le`):
`xmssQromBound q ≤ ((4.45 q + 0.523 · 2^17 √q + 0.709 · 2^33) / 2^64)²`, at most `2^-60` for
`q ≤ 2^30` and about `q² 2^-123.7` for large `q`. Each term is bounded by a real number:

* the adversary term `advTermQ q ≤ 2.45 q 2^-64` (`advTermQ_le`, `√6 < 2.45`), the verification
  `verTermQ = 384 · 2^-64` (`verTermQ_le`), its linear term `verLinQ ≤ 400 · 2^-128`
  (`verLinQ_le`, `|HashDomain| ≥ 2^136`) and the read error `readErrQ ≤ 2^-240`;
* the prefix's classical costs `clsBoundQ q ≤ ((0.523 · 2^17 √q + 0.708 · 2^33) / 2^64)²`
  (Costs' `twBoundQ_le`, `clsCapQ ≤ 2^65 + 2^41`);
* the hybrid `hybTermQ q ≤ 2q 2^-64 + 20 · 2^-64` (`hybTermQ_le`).

At `q ≤ 2^30` the bound is at most `2^-60`, at `q ≤ 2^40` at most `2^-43`, at `q ≤ 2^50` at most
`2^-23` (`xmssQromBound_two_pow_30_le`, `_40_le`, `_50_le`).
-/

open scoped ENNReal

namespace Quantum.Qrom.Xmss

open Quantum QuantumRuntime Quantum.Xmss.Hybrid
open LeanXmss HashSig
open Quantum.Xmss.Assembly (keepCost)

/-! ## Helpers -/

section helpers

/-- A square root below `a` from a bound below `a²`. -/
theorem rpow_inv_two_le_ofRealQ {x : ℝ≥0∞} {r a : ℝ} (ha : 0 ≤ a) (hx : x ≤ ENNReal.ofReal r)
    (h : r ≤ a ^ 2) : x ^ (2⁻¹ : ℝ) ≤ ENNReal.ofReal a :=
  calc x ^ (2⁻¹ : ℝ) ≤ (ENNReal.ofReal a ^ 2) ^ (2⁻¹ : ℝ) := by
        rw [← ENNReal.ofReal_pow ha]
        exact ENNReal.rpow_le_rpow (hx.trans (ENNReal.ofReal_le_ofReal h)) (by norm_num)
    _ = ENNReal.ofReal a := sq_rpow_inv_two_eq _

/-- `√(a² + b) ≤ a + √b`. -/
theorem sq_add_rpow_inv_two_leQ (a b : ℝ≥0∞) : (a ^ 2 + b) ^ (2⁻¹ : ℝ) ≤ a + b ^ (2⁻¹ : ℝ) :=
  (ENNReal.rpow_add_le_add_rpow _ _ (by norm_num) (by norm_num)).trans_eq
    (by rw [sq_rpow_inv_two_eq])

/-- `2^-k` as a real number. -/
theorem inv_two_pow_eq_ofRealQ (k : ℕ) : (2 ^ k : ℝ≥0∞)⁻¹ = ENNReal.ofReal (1 / 2 ^ k) := by
  rw [one_div, ENNReal.ofReal_inv_of_pos (by positivity), ENNReal.ofReal_pow (by norm_num),
    ENNReal.ofReal_ofNat]

theorem card_uInt8Q : Fintype.card UInt8 = 256 := by
  rw [← FinEnum.card_eq_fintypeCard]
  rfl

/-- **The random oracle's domain is large**: `2^136 ≤ |HashDomain|` (the bytes after the
length). -/
theorem two_pow_le_card_hashDomain : 2 ^ 136 ≤ Fintype.card HashDomain := by
  have hinj : Function.Injective fun f : Fin maxLen → UInt8 ↦ ((0 : Fin (maxLen + 1)), f) :=
    fun _ _ h ↦ (Prod.mk.inj h).2
  refine le_trans ?_ (Fintype.card_le_of_injective _ hinj)
  rw [Fintype.card_fun, Fintype.card_fin, card_uInt8Q]
  calc 2 ^ 136 = 256 ^ 17 := by norm_num
    _ ≤ 256 ^ maxLen := Nat.pow_le_pow_right (by norm_num) (by norm_num [maxLen])

end helpers

/-! ## The terms -/

section terms

set_option exponentiation.threshold 1100

/-- **The adversary term**: `advTermQ q ≤ 2.45 q 2^-64` (`√6 < 2.45`). -/
theorem advTermQ_le (q : ℕ) : advTermQ q ≤ ENNReal.ofReal (2.45 * q / 2 ^ 64) := by
  have h6 : (6 * (2 ^ 128 : ℝ≥0∞)⁻¹) ^ (2⁻¹ : ℝ) ≤ ENNReal.ofReal (2.45 / 2 ^ 64) := by
    refine rpow_inv_two_le_ofRealQ (r := 6 / 2 ^ 128) (by positivity) ?_ (by norm_num)
    simp (disch := positivity) only [← ENNReal.ofReal_ofNat, ← ENNReal.ofReal_pow,
      ← ENNReal.ofReal_inv_of_pos, ← ENNReal.ofReal_mul]
    exact ENNReal.ofReal_le_ofReal (by norm_num)
  unfold advTermQ
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  refine (mul_le_mul_of_nonneg_left h6 zero_le).trans ?_
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
  exact ENNReal.ofReal_le_ofReal (le_of_eq (by ring))

/-- **The verification term**: `verTermQ ≤ 384 · 2^-64`. -/
theorem verTermQ_le : verTermQ ≤ ENNReal.ofReal (384 / 2 ^ 64) := by
  have h : ((2 ^ 128 : ℝ≥0∞)⁻¹) ^ (2⁻¹ : ℝ) ≤ ENNReal.ofReal (1 / 2 ^ 64) :=
    rpow_inv_two_le_ofRealQ (r := 1 / 2 ^ 128) (by positivity)
      (inv_two_pow_eq_ofRealQ 128).le (by norm_num)
  unfold verTermQ
  rw [verifyCalls_eq]
  refine (mul_le_mul_of_nonneg_left h zero_le).trans ?_
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
  exact ENNReal.ofReal_le_ofReal (by norm_num)

/-- **The verification's linear term**: `verLinQ ≤ 400 · 2^-128`. -/
theorem verLinQ_le : verLinQ ≤ ENNReal.ofReal (400 / 2 ^ 128) := by
  have hY : (2 : ℝ≥0∞) / (Fintype.card HashOutput : ℝ≥0∞) ≤ (2 ^ 255)⁻¹ := by
    rw [card_hashOutput]
    exact Quantum.Xmss.Assembly.two_div_natCast_le (by norm_num)
  have hD : (2 : ℝ≥0∞) / (Fintype.card HashDomain : ℝ≥0∞) ≤ (2 ^ 135)⁻¹ :=
    Quantum.Xmss.Assembly.two_div_natCast_le
      ((by norm_num : 2 * 2 ^ 135 = 2 ^ 136).le.trans two_pow_le_card_hashDomain)
  unfold verLinQ keepCost
  rw [verifyCalls_eq]
  refine (mul_le_mul_of_nonneg_left (add_le_add (add_le_add le_rfl hY) hD) zero_le).trans ?_
  simp (disch := positivity) only [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_ofNat,
    ← ENNReal.ofReal_pow, ← ENNReal.ofReal_inv_of_pos, ← ENNReal.ofReal_mul,
    ← ENNReal.ofReal_add]
  exact ENNReal.ofReal_le_ofReal (by norm_num)

/-- **The read error**: `readErrQ ≤ 2^-240`. -/
theorem readErrQ_le : readErrQ ≤ ENNReal.ofReal (1 / 2 ^ 240) := by
  unfold readErrQ
  refine ENNReal.ofReal_le_ofReal ?_
  rw [Quantum.Sponge.readError, card_hashOutput, verifyCalls_eq, Nat.cast_zero, add_zero,
    zero_div, add_zero]
  norm_num

/-- **The prefix's classical costs** (Costs' `twBoundQ_le`): for `q ≤ 2^64`,
`clsBoundQ q ≤ ((0.523 · 2^17 √q + 0.708 · 2^33) / 2^64)²`. -/
theorem clsBoundQ_le {q : ℕ} (hq : q ≤ 2 ^ 64) :
    clsBoundQ q ≤ ENNReal.ofReal (((0.523 * 2 ^ 17 * √(q : ℝ) + 0.708 * 2 ^ 33) / 2 ^ 64) ^ 2) :=
  twBoundQ_le hq clsCapQ_le clsCapQ_le clsCapQ_le

/-- **The hybrid term**: `hybTermQ q ≤ 2q 2^-64 + 20 · 2^-64`. -/
theorem hybTermQ_le (q : ℕ) : hybTermQ q ≤ ENNReal.ofReal (2 * q / 2 ^ 64 + 20 / 2 ^ 64) := by
  have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  have hs : 4 * ((q : ℝ≥0∞) * ((q : ℝ≥0∞) * kappaQ)) ≤
      ENNReal.ofReal (4 * (q : ℝ) ^ 2 / 2 ^ 128) := by
    unfold kappaQ
    simp (disch := positivity) only [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_ofNat,
      ← ENNReal.ofReal_pow, ← ENNReal.ofReal_inv_of_pos, ← ENNReal.ofReal_mul]
    exact ENNReal.ofReal_le_ofReal (le_of_eq (by ring))
  have hv : (verifyCalls : ℝ≥0∞) * kappaQ ≤ ENNReal.ofReal (384 / 2 ^ 128) := by
    unfold kappaQ
    rw [verifyCalls_eq]
    simp (disch := positivity) only [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_ofNat,
      ← ENNReal.ofReal_pow, ← ENNReal.ofReal_inv_of_pos, ← ENNReal.ofReal_mul]
    exact ENNReal.ofReal_le_ofReal (by norm_num)
  unfold hybTermQ
  rw [ENNReal.ofReal_add (by positivity) (by positivity)]
  exact add_le_add (rpow_inv_two_le_ofRealQ (by positivity) hs (le_of_eq (by ring)))
    (rpow_inv_two_le_ofRealQ (by positivity) hv (by norm_num))

/-- **The square-rooted event term**: for `q ≤ 2^64`, `√eventTermQ q ≤ 2.45 q 2^-64 +
384 · 2^-64 + ((0.523 · 2^17 √q + 0.708 · 2^33) / 2^64 + 20 · 2^-64) + 2^-120`. -/
theorem eventTermQ_rpow_le {q : ℕ} (hq : q ≤ 2 ^ 64) :
    eventTermQ q ^ (2⁻¹ : ℝ) ≤ ENNReal.ofReal (2.45 * q / 2 ^ 64 + 384 / 2 ^ 64 +
      ((0.523 * 2 ^ 17 * √(q : ℝ) + 0.708 * 2 ^ 33) / 2 ^ 64 + 20 / 2 ^ 64) + 1 / 2 ^ 120) := by
  have hr := rpow_inv_two_le_ofRealQ (a := 1 / 2 ^ 120) (by positivity) readErrQ_le
    (by norm_num)
  have hc := rpow_inv_two_le_ofRealQ (by positivity) (clsBoundQ_le hq) le_rfl
  have hv := rpow_inv_two_le_ofRealQ (a := 20 / 2 ^ 64) (by positivity) verLinQ_le
    (by norm_num)
  have hcv : (clsBoundQ q + verLinQ) ^ (2⁻¹ : ℝ) ≤
      ENNReal.ofReal ((0.523 * 2 ^ 17 * √(q : ℝ) + 0.708 * 2 ^ 33) / 2 ^ 64 + 20 / 2 ^ 64) := by
    rw [ENNReal.ofReal_add (by positivity) (by positivity)]
    exact (ENNReal.rpow_add_le_add_rpow _ _ (by norm_num) (by norm_num)).trans
      (add_le_add hc hv)
  unfold eventTermQ
  refine (sq_add_rpow_inv_two_leQ _ _).trans ((add_le_add (add_le_add (add_le_add
    (advTermQ_le q) verTermQ_le) hcv) hr).trans_eq ?_)
  rw [← ENNReal.ofReal_add (by positivity) (by positivity),
    ← ENNReal.ofReal_add (by positivity) (by positivity),
    ← ENNReal.ofReal_add (by positivity) (by positivity)]

end terms

/-! ## The closed form -/

section closed

/-- The arithmetic of the closed form. -/
theorem root_le_closedQ (q : ℕ) :
    2.45 * q / 2 ^ 64 + 384 / 2 ^ 64 +
      ((0.523 * 2 ^ 17 * √(q : ℝ) + 0.708 * 2 ^ 33) / 2 ^ 64 + 20 / 2 ^ 64) + 1 / 2 ^ 120 +
        (2 * q / 2 ^ 64 + 20 / 2 ^ 64) ≤
      (4.45 * q + 0.523 * 2 ^ 17 * √(q : ℝ) + 0.709 * 2 ^ 33) / 2 ^ 64 := by
  have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  have hs0 := Real.sqrt_nonneg (q : ℝ)
  linarith

/-- **The leanXMSS QROM bound in closed form**: for `q ≤ 2^64`,
`xmssQromBound q ≤ ((4.45 q + 0.523 · 2^17 √q + 0.709 · 2^33) / 2^64)²`. -/
theorem xmssQromBound_le {q : ℕ} (hq : q ≤ 2 ^ 64) :
    xmssQromBound q ≤
      ENNReal.ofReal (((4.45 * q + 0.523 * 2 ^ 17 * √(q : ℝ) + 0.709 * 2 ^ 33) / 2 ^ 64) ^ 2) := by
  have h1 := eventTermQ_rpow_le hq
  have h2 := hybTermQ_le q
  rw [ENNReal.ofReal_pow (by positivity)]
  unfold xmssQromBound
  refine pow_le_pow_left₀ zero_le ((add_le_add h1 h2).trans ?_) 2
  rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
  exact ENNReal.ofReal_le_ofReal (root_le_closedQ q)

set_option exponentiation.threshold 1100 in
/-- **At most `2^30` hash calls**: `xmssQromBound q ≤ 2^-60`. -/
theorem xmssQromBound_two_pow_30_le {q : ℕ} (hq : q ≤ 2 ^ 30) :
    xmssQromBound q ≤ (2 ^ 60 : ℝ≥0∞)⁻¹ := by
  have hq' : (q : ℝ) ≤ 2 ^ 30 := by exact_mod_cast hq
  have hs : √(q : ℝ) ≤ 2 ^ 15 :=
    (Real.sqrt_le_sqrt hq').trans_eq (by rw [show (2 : ℝ) ^ 30 = (2 ^ 15) ^ 2 by norm_num,
      Real.sqrt_sq (by norm_num)])
  refine (xmssQromBound_le (hq.trans (by norm_num))).trans ?_
  rw [inv_two_pow_eq_ofRealQ]
  refine ENNReal.ofReal_le_ofReal ?_
  calc ((4.45 * q + 0.523 * 2 ^ 17 * √(q : ℝ) + 0.709 * 2 ^ 33) / 2 ^ 64) ^ 2
      ≤ ((4.45 * 2 ^ 30 + 0.523 * 2 ^ 17 * 2 ^ 15 + 0.709 * 2 ^ 33) / 2 ^ 64) ^ 2 := by gcongr
    _ ≤ 1 / 2 ^ 60 := by norm_num

set_option exponentiation.threshold 1100 in
/-- **At most `2^40` hash calls**: `xmssQromBound q ≤ 2^-43`. -/
theorem xmssQromBound_two_pow_40_le {q : ℕ} (hq : q ≤ 2 ^ 40) :
    xmssQromBound q ≤ (2 ^ 43 : ℝ≥0∞)⁻¹ := by
  have hq' : (q : ℝ) ≤ 2 ^ 40 := by exact_mod_cast hq
  have hs : √(q : ℝ) ≤ 2 ^ 20 :=
    (Real.sqrt_le_sqrt hq').trans_eq (by rw [show (2 : ℝ) ^ 40 = (2 ^ 20) ^ 2 by norm_num,
      Real.sqrt_sq (by norm_num)])
  refine (xmssQromBound_le (hq.trans (by norm_num))).trans ?_
  rw [inv_two_pow_eq_ofRealQ]
  refine ENNReal.ofReal_le_ofReal ?_
  calc ((4.45 * q + 0.523 * 2 ^ 17 * √(q : ℝ) + 0.709 * 2 ^ 33) / 2 ^ 64) ^ 2
      ≤ ((4.45 * 2 ^ 40 + 0.523 * 2 ^ 17 * 2 ^ 20 + 0.709 * 2 ^ 33) / 2 ^ 64) ^ 2 := by gcongr
    _ ≤ 1 / 2 ^ 43 := by norm_num

set_option exponentiation.threshold 1100 in
/-- **At most `2^50` hash calls**: `xmssQromBound q ≤ 2^-23`. -/
theorem xmssQromBound_two_pow_50_le {q : ℕ} (hq : q ≤ 2 ^ 50) :
    xmssQromBound q ≤ (2 ^ 23 : ℝ≥0∞)⁻¹ := by
  have hq' : (q : ℝ) ≤ 2 ^ 50 := by exact_mod_cast hq
  have hs : √(q : ℝ) ≤ 2 ^ 25 :=
    (Real.sqrt_le_sqrt hq').trans_eq (by rw [show (2 : ℝ) ^ 50 = (2 ^ 25) ^ 2 by norm_num,
      Real.sqrt_sq (by norm_num)])
  refine (xmssQromBound_le (hq.trans (by norm_num))).trans ?_
  rw [inv_two_pow_eq_ofRealQ]
  refine ENNReal.ofReal_le_ofReal ?_
  calc ((4.45 * q + 0.523 * 2 ^ 17 * √(q : ℝ) + 0.709 * 2 ^ 33) / 2 ^ 64) ^ 2
      ≤ ((4.45 * 2 ^ 50 + 0.523 * 2 ^ 17 * 2 ^ 25 + 0.709 * 2 ^ 33) / 2 ^ 64) ^ 2 := by gcongr
    _ ≤ 1 / 2 ^ 23 := by norm_num

end closed

end Quantum.Qrom.Xmss

end
