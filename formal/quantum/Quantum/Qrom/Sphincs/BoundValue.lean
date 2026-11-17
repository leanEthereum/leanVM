module

public import Quantum.Qrom.Sphincs.Security
public import Quantum.Qrom.Xmss.BoundValue

@[expose] public section

/-!
# The size of the leanSPHINCS QROM bound

Security's `sphincsQromBound q` in closed form for `q ≤ 2^64` (`sphincsQromBound_le`):
`sphincsQromBound q ≤ ((5.86 q + 257.3 √q + 1.818 · 2^32) / 2^64)²`, about `q² 2^-122.9` for large
`q`. Each term is bounded by a real number:

* the averaged adversary term `advBarQ q ≤ 3.852 q 2^-64` (`advBarQ_le`, `√(6 · 2.4726) < 3.852`,
  the mean fresh fraction `epsBarQ = 2.4726 · 2^-128` with the stream cover's mean price), the
  verification `verBarQ ≤ 1383 · 2^-64`, its linear term `verLinBarQ ≤ 2209 · 2^-128` and the read
  error `readErrQ ≤ 2^-240`;
* the prefix's classical costs `clsBoundQ q ≤ ((257.3 √q + 0.909 · 2^32) / 2^64)²` (Costs'
  `twBoundQ_clsCap_le`);
* the hybrid `hybTermQ q ≤ 2q 2^-64 + 0.9087 · 2^32 · 2^-64` (`hybTermQ_le`, the reads'
  `√(clsCapQ · 2^-128)`).

At `q ≤ 2^30` the bound is at most `2^-60`, at `q ≤ 2^40` at most `2^-42`, at `q ≤ 2^50` at most
`2^-22` (`sphincsQromBound_two_pow_30_le`, `_40_le`, `_50_le`).
-/

open scoped ENNReal
open HashSig (HashOutput)
open Sphincs (signatureLimit)

namespace Quantum.Qrom.Sphincs

open Quantum QuantumRuntime Quantum.Xmss.Hybrid
open Quantum.Xmss.Assembly (keepCost)
open Quantum.Qrom.Xmss (rpow_inv_two_le_ofRealQ sq_add_rpow_inv_two_leQ inv_two_pow_eq_ofRealQ
  two_pow_le_card_hashDomain card_hashOutput)

/-! ## The terms -/

section terms

set_option exponentiation.threshold 1100

theorem card_pairOut : Fintype.card (HashOutput × HashOutput) = 2 ^ 512 := by
  rw [Fintype.card_prod, card_hashOutput]
  norm_num

/-- **The mean fresh fraction**: `epsBarQ ≤ 2.4726 · 2^-128`. -/
theorem epsBarQ_le : epsBarQ ≤ ENNReal.ofReal (2.4726 / 2 ^ 128) := by
  unfold epsBarQ
  rw [inv_two_pow_eq_ofRealQ, ← ENNReal.ofReal_add (by positivity)
    (by unfold Quantum.Sphincs.rhoCov; positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  unfold Quantum.Sphincs.rhoCov
  norm_num

/-- **The averaged adversary term**: `advBarQ q ≤ 3.852 q 2^-64`. -/
theorem advBarQ_le (q : ℕ) : advBarQ q ≤ ENNReal.ofReal (3.852 * q / 2 ^ 64) := by
  have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  refine rpow_inv_two_le_ofRealQ (r := (q : ℝ) ^ 2 * (6 * (2.4726 / 2 ^ 128))) (by positivity)
    ?_ ?_
  · refine (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left epsBarQ_le zero_le)
      zero_le).trans_eq ?_
    rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_pow hq0, ← ENNReal.ofReal_ofNat,
      ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_mul (by positivity)]
  · have : (6 : ℝ) * (2.4726 / 2 ^ 128) ≤ (3.852 / 2 ^ 64) ^ 2 := by norm_num
    calc (q : ℝ) ^ 2 * (6 * (2.4726 / 2 ^ 128)) ≤ (q : ℝ) ^ 2 * (3.852 / 2 ^ 64) ^ 2 := by gcongr
      _ = (3.852 * (q : ℝ) / 2 ^ 64) ^ 2 := by ring

/-- **The averaged verification term**: `verBarQ ≤ 1383 · 2^-64`. -/
theorem verBarQ_le : verBarQ ≤ ENNReal.ofReal (1383 / 2 ^ 64) := by
  refine rpow_inv_two_le_ofRealQ (r := 879 ^ 2 * (2.4726 / 2 ^ 128)) (by positivity) ?_
    (by norm_num)
  rw [verifyCalls_eq]
  refine (mul_le_mul_of_nonneg_left epsBarQ_le zero_le).trans_eq ?_
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_pow (by norm_num),
    ← ENNReal.ofReal_mul (by positivity)]
  norm_num

/-- **The averaged verification's linear term**: `verLinBarQ ≤ 2209 · 2^-128`. -/
theorem verLinBarQ_le : verLinBarQ ≤ ENNReal.ofReal (2209 / 2 ^ 128) := by
  have hY : (2 : ℝ≥0∞) / (Fintype.card (HashOutput × HashOutput) : ℝ≥0∞) ≤ (2 ^ 511)⁻¹ := by
    rw [card_pairOut]
    exact Quantum.Xmss.Assembly.two_div_natCast_le (by norm_num)
  have hD : (2 : ℝ≥0∞) / (Fintype.card Qrom.HashDomain : ℝ≥0∞) ≤ (2 ^ 135)⁻¹ :=
    Quantum.Xmss.Assembly.two_div_natCast_le
      ((by norm_num : 2 * 2 ^ 135 = 2 ^ 136).le.trans two_pow_le_card_hashDomain)
  unfold verLinBarQ keepCost
  rw [verifyCalls_eq]
  refine (mul_le_mul_of_nonneg_left (add_le_add (add_le_add epsBarQ_le hY) hD)
    zero_le).trans ?_
  simp (disch := positivity) only [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_ofNat,
    ← ENNReal.ofReal_pow, ← ENNReal.ofReal_inv_of_pos, ← ENNReal.ofReal_mul,
    ← ENNReal.ofReal_add]
  exact ENNReal.ofReal_le_ofReal (by norm_num)

/-- **The read error**: `readErrQ ≤ 2^-240`. -/
theorem readErrQ_le : readErrQ ≤ ENNReal.ofReal (1 / 2 ^ 240) := by
  unfold readErrQ
  refine ENNReal.ofReal_le_ofReal ?_
  rw [Quantum.Sponge.readError, card_pairOut, verifyCalls_eq, Nat.cast_zero, add_zero,
    zero_div, add_zero]
  norm_num

/-- **The prefix's classical costs** (Costs' `twBoundQ_clsCap_le`): for `q ≤ 2^64`,
`clsBoundQ q ≤ ((257.3 √q + 0.909 · 2^32) / 2^64)²`. -/
theorem clsBoundQ_le {q : ℕ} (hq : q ≤ 2 ^ 64) :
    clsBoundQ q ≤ ENNReal.ofReal (((257.3 * √(q : ℝ) + 0.909 * 2 ^ 32) / 2 ^ 64) ^ 2) :=
  twBoundQ_clsCap_le hq

/-- **The hybrid term**: `hybTermQ q ≤ 2q 2^-64 + 0.9087 · 2^32 · 2^-64`. -/
theorem hybTermQ_le (q : ℕ) :
    hybTermQ q ≤ ENNReal.ofReal (2 * q / 2 ^ 64 + 0.9087 * 2 ^ 32 / 2 ^ 64) := by
  have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  have hs : 4 * ((q : ℝ≥0∞) * ((q : ℝ≥0∞) * kappaQ)) ≤
      ENNReal.ofReal (4 * (q : ℝ) ^ 2 / 2 ^ 128) := by
    unfold kappaQ
    simp (disch := positivity) only [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_ofNat,
      ← ENNReal.ofReal_pow, ← ENNReal.ofReal_inv_of_pos, ← ENNReal.ofReal_mul]
    exact ENNReal.ofReal_le_ofReal (le_of_eq (by ring))
  have hc : (clsCapQ : ℝ≥0∞) * kappaQ ≤ ENNReal.ofReal ((clsCapQ : ℝ) / 2 ^ 128) := by
    unfold kappaQ
    simp (disch := positivity) only [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_ofNat,
      ← ENNReal.ofReal_pow, ← ENNReal.ofReal_inv_of_pos, ← ENNReal.ofReal_mul]
    exact ENNReal.ofReal_le_ofReal (le_of_eq (by ring))
  have hcap : (clsCapQ : ℝ) / 2 ^ 128 ≤ (0.9087 * 2 ^ 32 / 2 ^ 64) ^ 2 := by
    rw [clsCapQ_eq]
    simp only [signatureLimit]
    norm_num
  unfold hybTermQ
  rw [ENNReal.ofReal_add (by positivity) (by positivity)]
  exact add_le_add (rpow_inv_two_le_ofRealQ (by positivity) hs (le_of_eq (by ring)))
    (rpow_inv_two_le_ofRealQ (by positivity) hc hcap)

/-- **The square-rooted event term**: for `q ≤ 2^64`, `√eventTermQ q ≤ 3.852 q 2^-64 +
1383 · 2^-64 + ((257.3 √q + 0.909 · 2^32) / 2^64 + 47 · 2^-64) + 2^-120`. -/
theorem eventTermQ_rpow_le {q : ℕ} (hq : q ≤ 2 ^ 64) :
    eventTermQ q ^ (2⁻¹ : ℝ) ≤ ENNReal.ofReal (3.852 * q / 2 ^ 64 + 1383 / 2 ^ 64 +
      ((257.3 * √(q : ℝ) + 0.909 * 2 ^ 32) / 2 ^ 64 + 47 / 2 ^ 64) + 1 / 2 ^ 120) := by
  have hr := rpow_inv_two_le_ofRealQ (a := 1 / 2 ^ 120) (by positivity) readErrQ_le
    (by norm_num)
  have hc := rpow_inv_two_le_ofRealQ (by positivity) (clsBoundQ_le hq) le_rfl
  have hv := rpow_inv_two_le_ofRealQ (a := 47 / 2 ^ 64) (by positivity) verLinBarQ_le
    (by norm_num)
  have hcv : (clsBoundQ q + verLinBarQ) ^ (2⁻¹ : ℝ) ≤
      ENNReal.ofReal ((257.3 * √(q : ℝ) + 0.909 * 2 ^ 32) / 2 ^ 64 + 47 / 2 ^ 64) := by
    rw [ENNReal.ofReal_add (by positivity) (by positivity)]
    exact (ENNReal.rpow_add_le_add_rpow _ _ (by norm_num) (by norm_num)).trans
      (add_le_add hc hv)
  unfold eventTermQ eventTermOf
  refine (sq_add_rpow_inv_two_leQ _ _).trans ((add_le_add (add_le_add (add_le_add
    (advBarQ_le q) verBarQ_le) hcv) hr).trans_eq ?_)
  rw [← ENNReal.ofReal_add (by positivity) (by positivity),
    ← ENNReal.ofReal_add (by positivity) (by positivity),
    ← ENNReal.ofReal_add (by positivity) (by positivity)]

end terms

/-! ## The closed form -/

section closed

/-- The arithmetic of the closed form. -/
theorem root_le_closedQ (q : ℕ) :
    3.852 * q / 2 ^ 64 + 1383 / 2 ^ 64 +
      ((257.3 * √(q : ℝ) + 0.909 * 2 ^ 32) / 2 ^ 64 + 47 / 2 ^ 64) + 1 / 2 ^ 120 +
        (2 * q / 2 ^ 64 + 0.9087 * 2 ^ 32 / 2 ^ 64) ≤
      (5.86 * q + 257.3 * √(q : ℝ) + 1.818 * 2 ^ 32) / 2 ^ 64 := by
  have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  have hs0 := Real.sqrt_nonneg (q : ℝ)
  have h : (1383 : ℝ) / 2 ^ 64 + 47 / 2 ^ 64 + 1 / 2 ^ 120 ≤ 0.0003 * 2 ^ 32 / 2 ^ 64 := by
    norm_num
  have e : (5.86 * q + 257.3 * √(q : ℝ) + 1.818 * 2 ^ 32) / 2 ^ 64 =
      5.86 * q / 2 ^ 64 + 257.3 * √(q : ℝ) / 2 ^ 64 + 1.818 * 2 ^ 32 / 2 ^ 64 := by ring
  rw [e]
  have h2 : (3.852 : ℝ) * q / 2 ^ 64 + 2 * q / 2 ^ 64 ≤ 5.86 * q / 2 ^ 64 := by
    rw [← add_div]
    gcongr
    linarith
  have h3 : (257.3 * √(q : ℝ) + 0.909 * 2 ^ 32) / 2 ^ 64 =
      257.3 * √(q : ℝ) / 2 ^ 64 + 0.909 * 2 ^ 32 / 2 ^ 64 := by ring
  have h4 : (0.909 : ℝ) * 2 ^ 32 / 2 ^ 64 + 0.9087 * 2 ^ 32 / 2 ^ 64 + 0.0003 * 2 ^ 32 / 2 ^ 64 ≤
      1.818 * 2 ^ 32 / 2 ^ 64 := by norm_num
  rw [h3]
  linarith

/-- **The leanSPHINCS QROM bound in closed form**: for `q ≤ 2^64`,
`sphincsQromBound q ≤ ((5.86 q + 257.3 √q + 1.818 · 2^32) / 2^64)²`. -/
theorem sphincsQromBound_le {q : ℕ} (hq : q ≤ 2 ^ 64) :
    sphincsQromBound q ≤
      ENNReal.ofReal (((5.86 * q + 257.3 * √(q : ℝ) + 1.818 * 2 ^ 32) / 2 ^ 64) ^ 2) := by
  have h1 := eventTermQ_rpow_le hq
  have h2 := hybTermQ_le q
  rw [ENNReal.ofReal_pow (by positivity)]
  unfold sphincsQromBound
  refine pow_le_pow_left₀ zero_le ((add_le_add h1 h2).trans ?_) 2
  rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
  exact ENNReal.ofReal_le_ofReal (root_le_closedQ q)

set_option exponentiation.threshold 1100 in
/-- **At most `2^30` hash calls**: `sphincsQromBound q ≤ 2^-60`. -/
theorem sphincsQromBound_two_pow_30_le {q : ℕ} (hq : q ≤ 2 ^ 30) :
    sphincsQromBound q ≤ (2 ^ 60 : ℝ≥0∞)⁻¹ := by
  have hq' : (q : ℝ) ≤ 2 ^ 30 := by exact_mod_cast hq
  have hs : √(q : ℝ) ≤ 2 ^ 15 :=
    (Real.sqrt_le_sqrt hq').trans_eq (by rw [show (2 : ℝ) ^ 30 = (2 ^ 15) ^ 2 by norm_num,
      Real.sqrt_sq (by norm_num)])
  refine (sphincsQromBound_le (hq.trans (by norm_num))).trans ?_
  rw [inv_two_pow_eq_ofRealQ]
  refine ENNReal.ofReal_le_ofReal ?_
  calc ((5.86 * q + 257.3 * √(q : ℝ) + 1.818 * 2 ^ 32) / 2 ^ 64) ^ 2
      ≤ ((5.86 * 2 ^ 30 + 257.3 * 2 ^ 15 + 1.818 * 2 ^ 32) / 2 ^ 64) ^ 2 := by gcongr
    _ ≤ 1 / 2 ^ 60 := by norm_num

set_option exponentiation.threshold 1100 in
/-- **At most `2^40` hash calls**: `sphincsQromBound q ≤ 2^-42`. -/
theorem sphincsQromBound_two_pow_40_le {q : ℕ} (hq : q ≤ 2 ^ 40) :
    sphincsQromBound q ≤ (2 ^ 42 : ℝ≥0∞)⁻¹ := by
  have hq' : (q : ℝ) ≤ 2 ^ 40 := by exact_mod_cast hq
  have hs : √(q : ℝ) ≤ 2 ^ 20 :=
    (Real.sqrt_le_sqrt hq').trans_eq (by rw [show (2 : ℝ) ^ 40 = (2 ^ 20) ^ 2 by norm_num,
      Real.sqrt_sq (by norm_num)])
  refine (sphincsQromBound_le (hq.trans (by norm_num))).trans ?_
  rw [inv_two_pow_eq_ofRealQ]
  refine ENNReal.ofReal_le_ofReal ?_
  calc ((5.86 * q + 257.3 * √(q : ℝ) + 1.818 * 2 ^ 32) / 2 ^ 64) ^ 2
      ≤ ((5.86 * 2 ^ 40 + 257.3 * 2 ^ 20 + 1.818 * 2 ^ 32) / 2 ^ 64) ^ 2 := by gcongr
    _ ≤ 1 / 2 ^ 42 := by norm_num

set_option exponentiation.threshold 1100 in
/-- **At most `2^50` hash calls**: `sphincsQromBound q ≤ 2^-22`. -/
theorem sphincsQromBound_two_pow_50_le {q : ℕ} (hq : q ≤ 2 ^ 50) :
    sphincsQromBound q ≤ (2 ^ 22 : ℝ≥0∞)⁻¹ := by
  have hq' : (q : ℝ) ≤ 2 ^ 50 := by exact_mod_cast hq
  have hs : √(q : ℝ) ≤ 2 ^ 25 :=
    (Real.sqrt_le_sqrt hq').trans_eq (by rw [show (2 : ℝ) ^ 50 = (2 ^ 25) ^ 2 by norm_num,
      Real.sqrt_sq (by norm_num)])
  refine (sphincsQromBound_le (hq.trans (by norm_num))).trans ?_
  rw [inv_two_pow_eq_ofRealQ]
  refine ENNReal.ofReal_le_ofReal ?_
  calc ((5.86 * q + 257.3 * √(q : ℝ) + 1.818 * 2 ^ 32) / 2 ^ 64) ^ 2
      ≤ ((5.86 * 2 ^ 50 + 257.3 * 2 ^ 25 + 1.818 * 2 ^ 32) / 2 ^ 64) ^ 2 := by gcongr
    _ ≤ 1 / 2 ^ 22 := by norm_num

end closed

end Quantum.Qrom.Sphincs

end
