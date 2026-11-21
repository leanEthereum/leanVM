module

public import Quantum.Qrom.Sphincs.Multi.Security
public import Quantum.Qrom.Sphincs.BoundValue

@[expose] public section

/-!
# The size of the multi-user leanSPHINCS QROM bound

Security's `sphincsQromMuBound n total q` in closed form for `n, total, q ≤ 2^64`, given a bound
`rhoMaxQ n ≤ ρ 2^-128` on the averaged worst user's coverage price (`sphincsQromMuBound_le`):
`0.51 n² / 2^128 + (((√6 √(1 + ρ) + 2) q + 257.3 √q + 909 √(1 + ρ) + 30) / 2^64)²`.
Each term is bounded by a real number:

* the collisions `collTermSN n ≤ 0.51 n² 2^-128` (`collTermSN_le`);
* the hybrid `hybTermSN n q ≤ (2q + q 2^-64 + 29.66) 2^-64` (`hybTermSN_le`, `n ≤ 2^64`);
* the averaged adversary term `advBarN n q ≤ √6 √(1 + ρ) q 2^-64`, the verification
  `verBarN n ≤ 879 √(1 + ρ) 2^-64` and its linear term `verLinBarN n ≤ 886.25 (1 + ρ) 2^-128`;
* the prefix's classical costs `clsBoundSN total q ≤ ((257.1 √q + 0.1) / 2^64)²` (Costs).

For one user (`sphincsQromMuBound_one_le`, `ρ = rhoCov`):
`((5.86 q + 257.3 √q + 1460) / 2^64)²`.
-/

open scoped ENNReal
open HashSig (HashOutput)
open Sphincs (signatureLimit)

namespace Quantum.Qrom.Sphincs.Multi

open Quantum QuantumRuntime Quantum.Xmss.Hybrid
open Quantum.Xmss.Assembly (keepCost)
open Quantum.Qrom.Xmss (rpow_inv_two_le_ofRealQ sq_add_rpow_inv_two_leQ inv_two_pow_eq_ofRealQ
  two_pow_le_card_hashDomain)

variable {n total q : ℕ} {ρ : ℝ}

/-! ## The terms -/

section terms

set_option exponentiation.threshold 1100

/-- **The collision term**: `collTermSN n ≤ 0.51 n² 2^-128`. -/
theorem collTermSN_le (n : ℕ) :
    collTermSN n ≤ ENNReal.ofReal (0.51 * (n : ℝ) ^ 2 / 2 ^ 128) := by
  have hc : ((n.choose 2 : ℕ) : ℝ) ≤ (n : ℝ) ^ 2 / 2 := by
    rw [Nat.cast_choose_two]
    nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have hc0 : (0 : ℝ) ≤ ((n.choose 2 : ℕ) : ℝ) := Nat.cast_nonneg _
  unfold collTermSN
  simp (disch := positivity) only [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_ofNat,
    ← ENNReal.ofReal_pow, ← ENNReal.ofReal_inv_of_pos, ← ENNReal.ofReal_mul,
    ← ENNReal.ofReal_add]
  refine ENNReal.ofReal_le_ofReal ?_
  have h1 : ((2 : ℝ) ^ 128)⁻¹ + (2 ^ 256)⁻¹ ≤ 1.02 * (2 ^ 128)⁻¹ := by norm_num
  calc ((n.choose 2 : ℕ) : ℝ) * ((2 ^ 128)⁻¹ + (2 ^ 256)⁻¹)
      ≤ (n : ℝ) ^ 2 / 2 * (1.02 * (2 ^ 128)⁻¹) := mul_le_mul hc h1 (by positivity) (by positivity)
    _ = 0.51 * (n : ℝ) ^ 2 / 2 ^ 128 := by ring

/-- `kappaQN n ≤ (1 + 2^-64) 2^-128` for `n ≤ 2^64`. -/
theorem kappaQN_le (hn : n ≤ 2 ^ 64) :
    kappaQN n ≤ ENNReal.ofReal ((1 + 1 / 2 ^ 64) / 2 ^ 128) := by
  have hnR : (n : ℝ) ≤ 2 ^ 64 := by exact_mod_cast hn
  unfold kappaQN
  simp (disch := positivity) only [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_ofNat,
    ← ENNReal.ofReal_pow, ← ENNReal.ofReal_inv_of_pos, ← ENNReal.ofReal_mul,
    ← ENNReal.ofReal_add]
  refine ENNReal.ofReal_le_ofReal ?_
  have : (n : ℝ) * (2 ^ 256)⁻¹ ≤ 2 ^ 64 * (2 ^ 256)⁻¹ :=
    mul_le_mul_of_nonneg_right hnR (by positivity)
  have e : (1 + 1 / 2 ^ 64 : ℝ) / 2 ^ 128 = (2 ^ 128)⁻¹ + 2 ^ 64 * (2 ^ 256)⁻¹ := by norm_num
  rw [e]
  linarith

/-- **The hybrid term**: for `n ≤ 2^64`, `hybTermSN n q ≤ (2q + q 2^-64 + 29.66) 2^-64`. -/
theorem hybTermSN_le (hn : n ≤ 2 ^ 64) (q : ℕ) :
    hybTermSN n q ≤ ENNReal.ofReal ((2 * q + q / 2 ^ 64 + 29.66) / 2 ^ 64) := by
  have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  have hk := kappaQN_le hn
  have hs : 4 * ((q : ℝ≥0∞) * ((q : ℝ≥0∞) * kappaQN n)) ≤
      ENNReal.ofReal (4 * (q : ℝ) ^ 2 * ((1 + 1 / 2 ^ 64) / 2 ^ 128)) := by
    refine (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hk zero_le) zero_le) zero_le).trans_eq ?_
    simp (disch := positivity) only [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_ofNat,
      ← ENNReal.ofReal_mul]
    congr 1
    ring
  have hc : (verifyCalls : ℝ≥0∞) * kappaQN n ≤
      ENNReal.ofReal (879 * ((1 + 1 / 2 ^ 64) / 2 ^ 128)) := by
    rw [verifyCalls_eq]
    refine (mul_le_mul_of_nonneg_left hk zero_le).trans_eq ?_
    rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat, Nat.cast_ofNat]
  have h1 : 4 * (q : ℝ) ^ 2 * ((1 + 1 / 2 ^ 64) / 2 ^ 128) ≤
      ((2 * q + q / 2 ^ 64) / 2 ^ 64) ^ 2 := by
    have e : ((2 * q + q / 2 ^ 64 : ℝ) / 2 ^ 64) ^ 2 =
        (q : ℝ) ^ 2 * (4 + 4 / 2 ^ 64 + 1 / 2 ^ 128) / 2 ^ 128 := by ring
    rw [e]
    have : (4 : ℝ) * (1 + 1 / 2 ^ 64) ≤ 4 + 4 / 2 ^ 64 + 1 / 2 ^ 128 := by norm_num
    have hq2 : (0 : ℝ) ≤ (q : ℝ) ^ 2 := by positivity
    calc 4 * (q : ℝ) ^ 2 * ((1 + 1 / 2 ^ 64) / 2 ^ 128)
        = (q : ℝ) ^ 2 * (4 * (1 + 1 / 2 ^ 64)) / 2 ^ 128 := by ring
      _ ≤ _ := by gcongr
  unfold hybTermSN
  have e : (2 * (q : ℝ) + q / 2 ^ 64 + 29.66) / 2 ^ 64 =
      (2 * q + q / 2 ^ 64) / 2 ^ 64 + 29.66 / 2 ^ 64 := by ring
  rw [e, ENNReal.ofReal_add (by positivity) (by positivity)]
  exact add_le_add (rpow_inv_two_le_ofRealQ (by positivity) hs h1)
    (rpow_inv_two_le_ofRealQ (by positivity) hc (by norm_num))

/-- **The mean fresh fraction**: `epsBarN n ≤ (1 + ρ) 2^-128` from `rhoMaxQ n ≤ ρ 2^-128`. -/
theorem epsBarN_le (hρ0 : 0 ≤ ρ) (hρ : rhoMaxQ n ≤ ENNReal.ofReal (ρ / 2 ^ 128)) :
    epsBarN n ≤ ENNReal.ofReal ((1 + ρ) / 2 ^ 128) := by
  unfold epsBarN
  refine (add_le_add le_rfl hρ).trans_eq ?_
  rw [inv_two_pow_eq_ofRealQ, ← ENNReal.ofReal_add (by positivity) (by positivity)]
  congr 1
  ring

/-- **The averaged adversary term**: `advBarN n q ≤ √6 √(1 + ρ) q 2^-64`. -/
theorem advBarN_le (hρ0 : 0 ≤ ρ) (hρ : rhoMaxQ n ≤ ENNReal.ofReal (ρ / 2 ^ 128)) (q : ℕ) :
    advBarN n q ≤ ENNReal.ofReal (√6 * √(1 + ρ) * q / 2 ^ 64) := by
  have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  refine rpow_inv_two_le_ofRealQ (r := (q : ℝ) ^ 2 * (6 * ((1 + ρ) / 2 ^ 128)))
    (by positivity) ?_ (le_of_eq ?_)
  · refine (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (epsBarN_le hρ0 hρ) zero_le)
      zero_le).trans_eq ?_
    rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_pow hq0, ← ENNReal.ofReal_ofNat,
      ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_mul (by positivity)]
  · rw [div_pow, mul_pow, mul_pow, Real.sq_sqrt (by norm_num), Real.sq_sqrt (by linarith)]
    ring

/-- **The averaged verification term**: `verBarN n ≤ 879 √(1 + ρ) 2^-64`. -/
theorem verBarN_le (hρ0 : 0 ≤ ρ) (hρ : rhoMaxQ n ≤ ENNReal.ofReal (ρ / 2 ^ 128)) :
    verBarN n ≤ ENNReal.ofReal (879 * √(1 + ρ) / 2 ^ 64) := by
  refine rpow_inv_two_le_ofRealQ (r := 879 ^ 2 * ((1 + ρ) / 2 ^ 128)) (by positivity) ?_
    (le_of_eq ?_)
  · rw [verifyCalls_eq]
    refine (mul_le_mul_of_nonneg_left (epsBarN_le hρ0 hρ) zero_le).trans_eq ?_
    rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_pow (by norm_num),
      ← ENNReal.ofReal_mul (by positivity)]
    norm_num
  · rw [div_pow, mul_pow, Real.sq_sqrt (by linarith)]
    ring

/-- **The averaged verification's linear term**: `verLinBarN n ≤ 886.25 (1 + ρ) 2^-128`. -/
theorem verLinBarN_le (hρ0 : 0 ≤ ρ) (hρ : rhoMaxQ n ≤ ENNReal.ofReal (ρ / 2 ^ 128)) :
    verLinBarN n ≤ ENNReal.ofReal (886.25 * (1 + ρ) / 2 ^ 128) := by
  have hY : (2 : ℝ≥0∞) / (Fintype.card (HashOutput × HashOutput) : ℝ≥0∞) ≤ (2 ^ 511)⁻¹ := by
    rw [card_pairOut]
    exact Quantum.Xmss.Assembly.two_div_natCast_le (by norm_num)
  have hD : (2 : ℝ≥0∞) / (Fintype.card Qrom.HashDomain : ℝ≥0∞) ≤ (2 ^ 135)⁻¹ :=
    Quantum.Xmss.Assembly.two_div_natCast_le
      ((by norm_num : 2 * 2 ^ 135 = 2 ^ 136).le.trans two_pow_le_card_hashDomain)
  unfold verLinBarN keepCost
  rw [verifyCalls_eq]
  refine (mul_le_mul_of_nonneg_left (add_le_add (add_le_add (epsBarN_le hρ0 hρ) hY) hD)
    zero_le).trans ?_
  simp (disch := positivity) only [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_ofNat,
    ← ENNReal.ofReal_pow, ← ENNReal.ofReal_inv_of_pos, ← ENNReal.ofReal_mul,
    ← ENNReal.ofReal_add]
  refine ENNReal.ofReal_le_ofReal ?_
  have h : (879 : ℝ) * ((2 ^ 511)⁻¹ + (2 ^ 135)⁻¹) ≤ 7.25 / 2 ^ 128 := by norm_num
  have e : (879 : ℝ) * ((1 + ρ) / 2 ^ 128 + (2 ^ 511)⁻¹ + (2 ^ 135)⁻¹) =
      879 * (1 + ρ) / 2 ^ 128 + 879 * ((2 ^ 511)⁻¹ + (2 ^ 135)⁻¹) := by ring
  have h2 : (7.25 : ℝ) / 2 ^ 128 ≤ 7.25 * (1 + ρ) / 2 ^ 128 := by
    gcongr
    linarith
  rw [Nat.cast_ofNat, e]
  have e2 : (886.25 : ℝ) * (1 + ρ) / 2 ^ 128 = 879 * (1 + ρ) / 2 ^ 128 + 7.25 * (1 + ρ) / 2 ^ 128 :=
    by ring
  rw [e2]
  linarith

/-- **The square-rooted event term**: for `total, q ≤ 2^64`. -/
theorem eventTermSN_rpow_le (ht : total ≤ 2 ^ 64) (hq : q ≤ 2 ^ 64) (hρ0 : 0 ≤ ρ)
    (hρ : rhoMaxQ n ≤ ENNReal.ofReal (ρ / 2 ^ 128)) :
    eventTermSN n total q ^ (2⁻¹ : ℝ) ≤ ENNReal.ofReal (√6 * √(1 + ρ) * q / 2 ^ 64 +
      879 * √(1 + ρ) / 2 ^ 64 + ((257.1 * √(q : ℝ) + 0.1) / 2 ^ 64 +
        29.77 * √(1 + ρ) / 2 ^ 64) + 1 / 2 ^ 120) := by
  have hr := rpow_inv_two_le_ofRealQ (a := 1 / 2 ^ 120) (by positivity) readErrQ_le
    (by norm_num)
  have hc := rpow_inv_two_le_ofRealQ (by positivity) (clsBoundSN_le ht hq) le_rfl
  have hv := rpow_inv_two_le_ofRealQ (a := 29.77 * √(1 + ρ) / 2 ^ 64) (by positivity)
    (verLinBarN_le hρ0 hρ) (by
      rw [div_pow, mul_pow, Real.sq_sqrt (by linarith)]
      have : (0 : ℝ) ≤ 1 + ρ := by linarith
      have e : ((2 : ℝ) ^ 64) ^ 2 = 2 ^ 128 := by norm_num
      rw [e]
      gcongr
      norm_num)
  have hcv : (clsBoundSN total q + verLinBarN n) ^ (2⁻¹ : ℝ) ≤
      ENNReal.ofReal ((257.1 * √(q : ℝ) + 0.1) / 2 ^ 64 + 29.77 * √(1 + ρ) / 2 ^ 64) := by
    rw [ENNReal.ofReal_add (by positivity) (by positivity)]
    exact (ENNReal.rpow_add_le_add_rpow _ _ (by norm_num) (by norm_num)).trans
      (add_le_add hc hv)
  unfold eventTermSN
  refine (sq_add_rpow_inv_two_leQ _ _).trans ((add_le_add (add_le_add (add_le_add
    (advBarN_le hρ0 hρ q) (verBarN_le hρ0 hρ)) hcv) hr).trans_eq ?_)
  rw [← ENNReal.ofReal_add (by positivity) (by positivity),
    ← ENNReal.ofReal_add (by positivity) (by positivity),
    ← ENNReal.ofReal_add (by positivity) (by positivity)]

end terms

/-! ## The closed form -/

section closed

/-- The arithmetic of the closed form. -/
theorem root_le_closedSN (hq : q ≤ 2 ^ 64) (hρ0 : 0 ≤ ρ) :
    √6 * √(1 + ρ) * q / 2 ^ 64 + 879 * √(1 + ρ) / 2 ^ 64 +
      ((257.1 * √(q : ℝ) + 0.1) / 2 ^ 64 + 29.77 * √(1 + ρ) / 2 ^ 64) + 1 / 2 ^ 120 +
        (2 * q + q / 2 ^ 64 + 29.66) / 2 ^ 64 ≤
      ((√6 * √(1 + ρ) + 2) * q + 257.3 * √(q : ℝ) + 909 * √(1 + ρ) + 30) / 2 ^ 64 := by
  have hqR : (q : ℝ) ≤ 2 ^ 64 := by exact_mod_cast hq
  have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  have hs0 := Real.sqrt_nonneg (q : ℝ)
  have hr0 : 0 ≤ √(1 + ρ) := Real.sqrt_nonneg _
  have hsq : (q : ℝ) = √(q : ℝ) * √(q : ℝ) := (Real.mul_self_sqrt hq0).symm
  have hsle : √(q : ℝ) ≤ 2 ^ 32 := by
    rw [Real.sqrt_le_left (by positivity)]
    calc (q : ℝ) ≤ 2 ^ 64 := hqR
      _ = (2 ^ 32) ^ 2 := by norm_num
  have h1 : (q : ℝ) ≤ √(q : ℝ) * 2 ^ 32 :=
    hsq.le.trans (mul_le_mul_of_nonneg_left hsle hs0)
  have hqq : (q : ℝ) / 2 ^ 64 ≤ 0.2 * √(q : ℝ) := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  rw [← sub_nonneg]
  have e : ((√6 * √(1 + ρ) + 2) * q + 257.3 * √(q : ℝ) + 909 * √(1 + ρ) + 30) / 2 ^ 64 -
      (√6 * √(1 + ρ) * q / 2 ^ 64 + 879 * √(1 + ρ) / 2 ^ 64 +
        ((257.1 * √(q : ℝ) + 0.1) / 2 ^ 64 + 29.77 * √(1 + ρ) / 2 ^ 64) + 1 / 2 ^ 120 +
          (2 * q + q / 2 ^ 64 + 29.66) / 2 ^ 64) =
      ((0.2 * √(q : ℝ) - q / 2 ^ 64) + 0.23 * √(1 + ρ) + (0.24 - 2 ^ 64 / 2 ^ 120)) / 2 ^ 64 := by
    ring
  rw [e]
  have : (0 : ℝ) ≤ 0.24 - 2 ^ 64 / 2 ^ 120 := by norm_num
  positivity

/-- The square-rooted part of the bound, without the collisions. -/
theorem rpow_add_hybTermSN_le (hn : n ≤ 2 ^ 64) (ht : total ≤ 2 ^ 64) (hq : q ≤ 2 ^ 64)
    (hρ0 : 0 ≤ ρ) (hρ : rhoMaxQ n ≤ ENNReal.ofReal (ρ / 2 ^ 128)) :
    (eventTermSN n total q ^ (2⁻¹ : ℝ) + hybTermSN n q) ^ 2 ≤ ENNReal.ofReal
      ((((√6 * √(1 + ρ) + 2) * q + 257.3 * √(q : ℝ) + 909 * √(1 + ρ) + 30) / 2 ^ 64) ^ 2) := by
  have hr0 : 0 ≤ √(1 + ρ) := Real.sqrt_nonneg _
  rw [ENNReal.ofReal_pow (by positivity)]
  refine pow_le_pow_left₀ zero_le ((add_le_add (eventTermSN_rpow_le ht hq hρ0 hρ)
    (hybTermSN_le hn q)).trans ?_) 2
  rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
  exact ENNReal.ofReal_le_ofReal (root_le_closedSN hq hρ0)

/-- **The multi-user leanSPHINCS QROM bound in closed form**: for `n, total, q ≤ 2^64` and
`rhoMaxQ n ≤ ρ 2^-128`,
`sphincsQromMuBound n total q ≤ 0.51 n² / 2^128 +
(((√6 √(1 + ρ) + 2) q + 257.3 √q + 909 √(1 + ρ) + 30) / 2^64)²`. -/
theorem sphincsQromMuBound_le (hn : n ≤ 2 ^ 64) (ht : total ≤ 2 ^ 64) (hq : q ≤ 2 ^ 64)
    (hρ0 : 0 ≤ ρ) (hρ : rhoMaxQ n ≤ ENNReal.ofReal (ρ / 2 ^ 128)) :
    sphincsQromMuBound n total q ≤ ENNReal.ofReal (0.51 * (n : ℝ) ^ 2 / 2 ^ 128 +
      (((√6 * √(1 + ρ) + 2) * q + 257.3 * √(q : ℝ) + 909 * √(1 + ρ) + 30) / 2 ^ 64) ^ 2) := by
  rw [ENNReal.ofReal_add (by positivity) (by positivity)]
  exact add_le_add (collTermSN_le n) (rpow_add_hybTermSN_le hn ht hq hρ0 hρ)

/-- **One user**: for `q ≤ 2^64`,
`sphincsQromMuBound 1 signatureLimit q ≤ ((5.86 q + 257.3 √q + 1460) / 2^64)²`, the bound of
`leanSphincs_qrom_security_one`. -/
theorem sphincsQromMuBound_one_le (hq : q ≤ 2 ^ 64) :
    sphincsQromMuBound 1 signatureLimit q ≤
      ENNReal.ofReal (((5.86 * q + 257.3 * √(q : ℝ) + 1460) / 2 ^ 64) ^ 2) := by
  have hρ0 : (0 : ℝ) ≤ Quantum.Sphincs.rhoCov := by unfold Quantum.Sphincs.rhoCov; norm_num
  have h0 : collTermSN 1 = 0 := by simp [collTermSN]
  have hs : √(1 + (Quantum.Sphincs.rhoCov : ℝ)) ≤ 1.5725 := by
    rw [Real.sqrt_le_left (by norm_num)]
    unfold Quantum.Sphincs.rhoCov
    norm_num
  have hs0 : 0 ≤ √(1 + (Quantum.Sphincs.rhoCov : ℝ)) := Real.sqrt_nonneg _
  have h6 : √(6 : ℝ) ≤ 2.4495 := by
    rw [Real.sqrt_le_left (by norm_num)]
    norm_num
  have h60 : 0 ≤ √(6 : ℝ) := Real.sqrt_nonneg _
  have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  unfold sphincsQromMuBound
  rw [h0, zero_add]
  refine (rpow_add_hybTermSN_le (by norm_num) (by norm_num [signatureLimit]) hq hρ0
    rhoMaxQ_one).trans (ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (by positivity) ?_ 2))
  refine div_le_div_of_nonneg_right ?_ (by positivity)
  have hp : √(6 : ℝ) * √(1 + (Quantum.Sphincs.rhoCov : ℝ)) ≤ 3.86 :=
    (mul_le_mul h6 hs hs0 (by norm_num)).trans (by norm_num)
  have h1 : (√(6 : ℝ) * √(1 + (Quantum.Sphincs.rhoCov : ℝ)) + 2) * q ≤ 5.86 * q :=
    mul_le_mul_of_nonneg_right (by linarith) hq0
  linarith

/-- **The averaged worst user's price at `n ≤ 2^e` users** from CovMax's certified grid. -/
theorem rhoMaxQ_le_of_le {N : ℕ} {r : ℝ} (hn : n ≤ N) (hr : rhoMaxR N ≤ r) :
    rhoMaxQ n ≤ ENNReal.ofReal (r / 2 ^ 128) :=
  (rhoMaxQ_le n).trans (ENNReal.ofReal_le_ofReal
    (div_le_div_of_nonneg_right ((rhoMaxR_mono hn).trans hr) (by positivity)))

/-- The closed form at bounded `n`, `q` and price. -/
theorem sphincsQromMuBound_le_of_le {N Q R : ℝ} {k : ℕ} (hn : n ≤ 2 ^ 64)
    (ht : total ≤ 2 ^ 64) (hq : q ≤ 2 ^ 64) (hρ0 : 0 ≤ ρ)
    (hρ : rhoMaxQ n ≤ ENNReal.ofReal (ρ / 2 ^ 128)) (hN : (n : ℝ) ≤ N) (hQ : (q : ℝ) ≤ Q ^ 2)
    (hQ0 : 0 ≤ Q) (hR : √(1 + ρ) ≤ R)
    (h : 0.51 * N ^ 2 / 2 ^ 128 + (((2.4495 * R + 2) * Q ^ 2 + 257.3 * Q + 909 * R + 30) /
      2 ^ 64) ^ 2 ≤ 1 / 2 ^ k) :
    sphincsQromMuBound n total q ≤ (2 ^ k : ℝ≥0∞)⁻¹ := by
  have hs : √(q : ℝ) ≤ Q := (Real.sqrt_le_sqrt hQ).trans_eq (Real.sqrt_sq hQ0)
  have h6 : √(6 : ℝ) ≤ 2.4495 := by
    rw [Real.sqrt_le_left (by norm_num)]
    norm_num
  have hr0 : 0 ≤ √(1 + ρ) := Real.sqrt_nonneg _
  have h60 : 0 ≤ √(6 : ℝ) := Real.sqrt_nonneg _
  have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  refine (sphincsQromMuBound_le hn ht hq hρ0 hρ).trans ?_
  rw [inv_two_pow_eq_ofRealQ]
  refine ENNReal.ofReal_le_ofReal (le_trans ?_ h)
  have hp : √(6 : ℝ) * √(1 + ρ) ≤ 2.4495 * R := mul_le_mul h6 hR hr0 (by norm_num)
  have hR0 : 0 ≤ R := hr0.trans hR
  have h1 : (√(6 : ℝ) * √(1 + ρ) + 2) * q ≤ (2.4495 * R + 2) * Q ^ 2 :=
    mul_le_mul (by linarith) hQ hq0 (by positivity)
  have hn2 : (n : ℝ) ^ 2 ≤ N ^ 2 := pow_le_pow_left₀ hn0 hN 2
  refine add_le_add (by gcongr) (pow_le_pow_left₀ (by positivity)
    (div_le_div_of_nonneg_right ?_ (by positivity)) 2)
  linarith

set_option exponentiation.threshold 1100 in
/-- **One user, at most `2^30` hash calls**: `sphincsQromMuBound 1 signatureLimit q ≤ 2^-62`. -/
theorem sphincsQromMuBound_one_two_pow_30_le (hq : q ≤ 2 ^ 30) :
    sphincsQromMuBound 1 signatureLimit q ≤ (2 ^ 62 : ℝ≥0∞)⁻¹ := by
  have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  have hqR : (q : ℝ) ≤ 2 ^ 30 := by exact_mod_cast hq
  have hs : √(q : ℝ) ≤ 2 ^ 15 := by
    rw [Real.sqrt_le_left (by positivity)]
    linarith
  refine (sphincsQromMuBound_one_le (hq.trans (by norm_num))).trans ?_
  rw [inv_two_pow_eq_ofRealQ]
  refine ENNReal.ofReal_le_ofReal (le_trans (pow_le_pow_left₀ (by positivity)
    (div_le_div_of_nonneg_right (add_le_add (add_le_add (mul_le_mul_of_nonneg_left hqR
      (by norm_num)) (mul_le_mul_of_nonneg_left hs (by norm_num))) le_rfl)
      (by positivity)) 2) ?_)
  norm_num

set_option exponentiation.threshold 1100 in
/-- **At most `2^20` users and `2^40` hash calls**: `sphincsQromMuBound n total q ≤ 2^-41`. -/
theorem sphincsQromMuBound_two_pow_40_le (hn : n ≤ 2 ^ 20) (ht : total ≤ 2 ^ 64)
    (hq : q ≤ 2 ^ 40) : sphincsQromMuBound n total q ≤ (2 ^ 41 : ℝ≥0∞)⁻¹ :=
  sphincsQromMuBound_le_of_le (N := 2 ^ 20) (Q := 2 ^ 20) (R := 3.4569) (ρ := 10.95)
    (hn.trans (by norm_num)) ht (hq.trans (by norm_num)) (by norm_num)
    (rhoMaxQ_le_of_le hn rhoMaxR_two_pow_20) (by exact_mod_cast hn)
    ((by exact_mod_cast hq : (q : ℝ) ≤ 2 ^ 40).trans_eq (by norm_num)) (by norm_num)
    (by rw [Real.sqrt_le_left (by norm_num)]; norm_num) (by norm_num)

set_option exponentiation.threshold 1100 in
/-- **At most `2^32` users and `2^30` hash calls**: `sphincsQromMuBound n total q ≤ 2^-58`. -/
theorem sphincsQromMuBound_two_pow_30_le (hn : n ≤ 2 ^ 32) (ht : total ≤ 2 ^ 64)
    (hq : q ≤ 2 ^ 30) : sphincsQromMuBound n total q ≤ (2 ^ 58 : ℝ≥0∞)⁻¹ :=
  sphincsQromMuBound_le_of_le (N := 2 ^ 32) (Q := 2 ^ 15) (R := 10.836) (ρ := 116.4)
    (hn.trans (by norm_num)) ht (hq.trans (by norm_num)) (by norm_num)
    (rhoMaxQ_le_of_le hn rhoMaxR_two_pow_32) (by exact_mod_cast hn)
    ((by exact_mod_cast hq : (q : ℝ) ≤ 2 ^ 30).trans_eq (by norm_num)) (by norm_num)
    (by rw [Real.sqrt_le_left (by norm_num)]; norm_num) (by norm_num)

set_option exponentiation.threshold 1100 in
/-- **At most `2^40` users and `2^50` hash calls**: `sphincsQromMuBound n total q ≤ 2^-16`. -/
theorem sphincsQromMuBound_two_pow_50_le (hn : n ≤ 2 ^ 40) (ht : total ≤ 2 ^ 64)
    (hq : q ≤ 2 ^ 50) : sphincsQromMuBound n total q ≤ (2 ^ 16 : ℝ≥0∞)⁻¹ :=
  sphincsQromMuBound_le_of_le (N := 2 ^ 40) (Q := 2 ^ 25) (R := 22.008) (ρ := 483.3)
    (hn.trans (by norm_num)) ht (hq.trans (by norm_num)) (by norm_num)
    (rhoMaxQ_le_of_le hn rhoMaxR_two_pow_40) (by exact_mod_cast hn)
    ((by exact_mod_cast hq : (q : ℝ) ≤ 2 ^ 50).trans_eq (by norm_num)) (by norm_num)
    (by rw [Real.sqrt_le_left (by norm_num)]; norm_num) (by norm_num)

end closed

end Quantum.Qrom.Sphincs.Multi

end
