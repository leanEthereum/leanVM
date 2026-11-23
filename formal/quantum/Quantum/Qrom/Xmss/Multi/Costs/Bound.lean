module

public import Quantum.Qrom.Xmss.Multi.Costs.Ports
public import Quantum.Qrom.Xmss.Multi.GameTCalls

@[expose] public section

/-!
# The classical costs of the `n`-user runtime 2: the event bound and the averaged costs

* **The event bound at the end of the challenge prefix** (`ewPrefixQN_le`): with at most `q`
  adversary calls and `K` classical calls, the weight of `BadRQN hon P` is at most
  `(advTermQ q + √twPQN)²` (fresh bound `2^-128`, the single-user `advTermQ`).
* **The averaged costs** (`uavg_twMaskN_le_of`): on the tables with distinct public parameters
  (`twMaskN`, `0` elsewhere), from the per-table split of Ports' `twPQN_le`, the Enc bound and the
  averaged recorded unselected mass `tauU`, the average is at most `twBoundQ q K 0 0` (no re-grind
  weights: the single-user `S = R = 0`).
* **The closed form** (`twBoundQ_le_mu`, `clsCapN_le`): for `q ≤ 2^64` and `K ≤ 2^98`,
  `twBoundQ q K 0 0 ≤ ((0.6 · 2^17 √q + 1) / 2^64)²`; the call count of `n ≤ 2^64` users with
  `total ≤ 2^64` requests is at most `2^98`.
-/

open Matrix IPFunctor
open scoped ENNReal Kronecker ComplexOrder

namespace Quantum.Qrom.Xmss.Multi

open Quantum QuantumRuntime Quantum.Sponge HashSig LeanXmss
open Quantum.Xmss.Assembly (recHwSpec recSpec runtimeR extWeight extCls
  eventWeight_runtimeR_le uavg_sq_rpow_add_le uavg_const_le)
open Quantum.Xmss.Hybrid (uavg uavg_mono uavg_add uavg_const_mul)

attribute [local irreducible] xmssRom

variable {n : ℕ}

/-! ## The event bound at the end of the prefix -/

/-- **The event bound at the end of the challenge prefix**: with at most `q` adversary calls and
`K` classical calls, `ew ≤ (advTermQ q + √twPQN)²`. -/
theorem ewPrefixQN_le (hon : Fin n → HonestCells) (P : Fin n → PublicParameter)
    (A : MuAdversary n) (θ : HPosN n → Digest) {q K : ℕ}
    (hq : IFreeM.IsChargeBound (prefixQN A θ) (portCharge fun i ↦
      if extCls HashOutput HashDomain (QMemN n) (recSpec (HPosN n) (SelMemN n)) i then 0 else 1)
      q)
    (hK : IFreeM.IsChargeBound (prefixQN A θ) (portCharge fun i ↦
      if extCls HashOutput HashDomain (QMemN n) (recSpec (HPosN n) (SelMemN n)) i then 1 else 0)
      K) :
    (runtimeR (m0N (n := n))).eventWeight .instruments (hwProjector (BadRQN hon P)) (prefixQN A θ)
      initQN ≤ (advTermQ q + twPQN hon P A θ ^ (2⁻¹ : ℝ)) ^ 2 :=
  eventWeight_runtimeR_le (q := q) (K := K) (BadRQN hon P) (labelFree_badRQN hon P)
    (fun W m ↦ upClosed_slice_badRQN W m) m0N (empty_not_mem_badRQN m0N)
    (fun _ ↦ (2 ^ 128 : ℝ≥0∞)⁻¹) (fun _ _ ↦ ENNReal.inv_ne_top.mpr (by positivity))
    (fun _ _ W m ↦ freshBound_slice_badRQN W m _)
    (fun c σ ↦ readCostT (BadRQN hon P) c σ)
    (fun c σ ↦ flipCost (BadRQN hon P) (hwProgKraus c) 0 σ)
    (fun c σ hσ ↦ potential_hwReadKraus_le_refinedT (BadRQN hon P) c σ hσ)
    (fun c σ hσ ↦ potential_hwProgKraus_le (BadRQN hon P) (fun _ ↦ 0)
      (fun _ ↦ conjTranspose_zero) (fun _ ↦ mul_zero 0) c σ hσ)
    .instruments (prefixQN A θ) hq hK (SubState.basis ())

/-! ## The averaged costs -/

open scoped Classical in
/-- **The classical costs on the tables with distinct public parameters**: `twPQN` at the hidden
values `θ` when the users' parameters are distinct, `0` otherwise. -/
noncomputable def twMaskN (A : MuAdversary n) (θ : HPosN n → Digest) : ℝ≥0∞ :=
  if PDistinct (tabOfN θ) then twPQN (honQN θ) (parQN θ) A θ else 0

theorem twMaskN_of_pDistinct (A : MuAdversary n) {θ : HPosN n → Digest}
    (h : PDistinct (tabOfN θ)) : twMaskN A θ = twPQN (honQN θ) (parQN θ) A θ := by
  classical
  unfold twMaskN
  exact ite_eq_left h

theorem twMaskN_of_not (A : MuAdversary n) {θ : HPosN n → Digest} (h : ¬PDistinct (tabOfN θ)) :
    twMaskN A θ = 0 := by
  classical
  unfold twMaskN
  exact ite_eq_right h

/-- **The averaged classical costs of the prefix**, from the slices' bounds: the prefix
invariant and the Enc bound on the tables with distinct parameters, the averaged recorded
unselected mass. -/
theorem uavg_twMaskN_le_of (A : MuAdversary n) {q K : ℕ}
    (hinv : ∀ θ, PDistinct (tabOfN θ) → PrefixInvQN (honQN θ) (parQN θ) A θ)
    (hK : ∀ θ, IFreeM.IsChargeBound (prefixQN A θ) (portCharge fun i ↦
      if extCls HashOutput HashDomain (QMemN n) (recSpec (HPosN n) (SelMemN n)) i then 1 else 0)
      K)
    (henc : ∀ θ, PDistinct (tabOfN θ) → encPreN (parQN θ) A θ ≤ 2 ^ 22 * ((q : ℝ≥0∞) +
      4 * ((q + K : ℕ) : ℝ≥0∞) * recUPreN A θ + ((q + K : ℕ) : ℝ≥0∞) * K * (2 ^ 250 : ℝ≥0∞)⁻¹))
    (hU : uavg (recUMaskN A) ≤ tauU q K) :
    uavg (twMaskN A) ≤ twBoundQ q K 0 0 := by
  set c₀ : ℝ≥0∞ := ENNReal.ofReal (2 / Fintype.card HashOutput) * K
  set a : (HPosN n → Digest) → ℝ≥0∞ := fun θ ↦
    (2 ^ 127 : ℝ≥0∞)⁻¹ * (encCap q K (recUMaskN A θ) + (2 ^ 128 : ℝ≥0∞)⁻¹ * ((0 : ℕ) : ℝ≥0∞)) +
      c₀
  set p : (HPosN n → Digest) → ℝ≥0∞ := fun θ ↦
    recUMaskN A θ + (2 ^ 128 : ℝ≥0∞)⁻¹ * ((0 : ℕ) : ℝ≥0∞)
  have hpt : ∀ θ, twMaskN A θ ≤ (a θ ^ (2⁻¹ : ℝ) + p θ ^ (2⁻¹ : ℝ)) ^ 2 := fun θ ↦ by
    by_cases hP : PDistinct (tabOfN θ)
    · rw [twMaskN_of_pDistinct A hP]
      have h1 : (2 ^ 127 : ℝ≥0∞)⁻¹ * encPreN (parQN θ) A θ + c₀ ≤ a θ := by
        refine add_le_add (mul_le_mul_of_nonneg_left ?_ zero_le) le_rfl
        rw [Nat.cast_zero, mul_zero, add_zero, recUMaskN_of_pDistinct A hP]
        exact henc θ hP
      have h2 : recUPreN A θ ≤ p θ := by
        rw [← recUMaskN_of_pDistinct A hP]
        exact le_add_of_nonneg_right zero_le
      exact (twPQN_le (honQN θ) (parQN θ) A θ (hinv θ hP) (hK θ)).trans
        (pow_le_pow_left₀ zero_le (add_le_add (ENNReal.rpow_le_rpow h1 (by norm_num))
          (ENNReal.rpow_le_rpow h2 (by norm_num))) 2)
    · rw [twMaskN_of_not A hP]
      exact zero_le
  refine (uavg_mono hpt).trans ((uavg_sq_rpow_add_le a p).trans ?_)
  have hua : uavg a ≤ aCap q K 0 := by
    have e : a = fun θ ↦ ((2 ^ 127 : ℝ≥0∞)⁻¹ * (2 ^ 22 * 4 * ((q + K : ℕ) : ℝ≥0∞))) *
        recUMaskN A θ + ((2 ^ 127 : ℝ≥0∞)⁻¹ * (2 ^ 22 * ((q : ℝ≥0∞) +
          ((q + K : ℕ) : ℝ≥0∞) * K * (2 ^ 250 : ℝ≥0∞)⁻¹) +
            (2 ^ 128 : ℝ≥0∞)⁻¹ * ((0 : ℕ) : ℝ≥0∞)) + c₀) := by
      funext θ
      simp only [a, encCap]
      ring
    rw [e, uavg_add, uavg_const_mul]
    refine (add_le_add (mul_le_mul_of_nonneg_left hU zero_le) (uavg_const_le _)).trans_eq ?_
    simp only [aCap, encCap]
    ring
  have hup : uavg p ≤ pCap q K 0 := by
    rw [uavg_add]
    exact add_le_add hU (uavg_const_le _)
  unfold twBoundQ
  gcongr

/-! ## The closed form -/

set_option exponentiation.threshold 2048 in
/-- **The linear charge, numerically**: for `q ≤ 2^64`, `K ≤ 2^98`,
`aR ≤ (2.92 · 2^-52)² q + (2^-78)²`. -/
theorem aR_le_mu {q K : ℕ} (hq : q ≤ 2 ^ 64) (hK : K ≤ 2 ^ 98) :
    aR q K 0 ≤ (2.92 * (2 ^ 52)⁻¹) ^ 2 * q + ((2 ^ 78)⁻¹) ^ 2 := by
  have hqR : (q : ℝ) ≤ 2 ^ 64 := by exact_mod_cast hq
  have hKR : (K : ℝ) ≤ 2 ^ 98 := by exact_mod_cast hK
  have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  have hK0 : (0 : ℝ) ≤ K := Nat.cast_nonneg K
  have hqK : ((q + K : ℕ) : ℝ) ≤ 2 ^ 64 + 2 ^ 98 := by push_cast; linarith
  have hqK0 : (0 : ℝ) ≤ ((q + K : ℕ) : ℝ) := Nat.cast_nonneg _
  have ht0 := tauR_nonneg q K
  have ht : tauR q K ≤ (2 ^ 96)⁻¹ * q + 2 ^ 98 * (2 ^ 1000)⁻¹ := by
    unfold tauR
    have : (K : ℝ) * (2 ^ 1000)⁻¹ ≤ 2 ^ 98 * (2 ^ 1000)⁻¹ :=
      mul_le_mul_of_nonneg_right hKR (by positivity)
    have e : (q : ℝ) * 2 ^ 32 * (2 ^ 128)⁻¹ = (2 ^ 96)⁻¹ * q := by ring
    linarith
  have h2 : ((q + K : ℕ) : ℝ) * tauR q K ≤
      (2 ^ 64 + 2 ^ 98) * ((2 ^ 96)⁻¹ * q + 2 ^ 98 * (2 ^ 1000)⁻¹) :=
    mul_le_mul hqK ht ht0 (by positivity)
  have h3 : ((q + K : ℕ) : ℝ) * K ≤ (2 ^ 64 + 2 ^ 98) * 2 ^ 98 :=
    mul_le_mul hqK hKR hK0 (by positivity)
  have hc : (2 : ℝ) / Fintype.card HashOutput = 2 * (2 ^ 256)⁻¹ := by
    rw [card_hashOutput, Nat.cast_pow, Nat.cast_ofNat, div_eq_mul_inv]
  unfold aR
  rw [hc]
  push_cast
  nlinarith

set_option exponentiation.threshold 2048 in
/-- **The recorded flip mass, numerically**: `pR ≤ (2^-48)² q + (2^-451)²` for `K ≤ 2^98`. -/
theorem pR_le_mu {q K : ℕ} (hK : K ≤ 2 ^ 98) :
    pR q K 0 ≤ ((2 ^ 48)⁻¹) ^ 2 * q + ((2 ^ 451)⁻¹) ^ 2 := by
  have hKR : (K : ℝ) ≤ 2 ^ 98 := by exact_mod_cast hK
  have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  unfold pR tauR
  push_cast
  nlinarith

set_option exponentiation.threshold 2048 in
/-- **The closed form**: for `q ≤ 2^64` and `K ≤ 2^98`,
`twBoundQ q K 0 0 ≤ ((0.6 · 2^17 √q + 1) / 2^64)²`. -/
theorem twBoundQ_le_mu {q K : ℕ} (hq : q ≤ 2 ^ 64) (hK : K ≤ 2 ^ 98) :
    twBoundQ q K 0 0 ≤ ENNReal.ofReal (((0.6 * 2 ^ 17 * √q + 1) / 2 ^ 64) ^ 2) := by
  have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  refine (twBoundQ_le_of (c₁ := 2.92 * (2 ^ 52)⁻¹) (c₂ := (2 ^ 48)⁻¹) (a₀ := (2 ^ 78)⁻¹)
    (p₀ := (2 ^ 451)⁻¹) (by positivity) (by positivity) (by positivity) (by positivity)
    (aR_le_mu hq hK) (pR_le_mu hK)).trans ?_
  refine ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (by positivity) ?_ 2)
  rw [le_div_iff₀ (by positivity)]
  nlinarith [Real.sqrt_nonneg (q : ℝ)]

/-- **The classical calls of `n` users with `total ≤ 2^64` requests**: at most `2^98`. -/
theorem clsCapN_le {total : ℕ} (ht : total ≤ 2 ^ 64) :
    clsCapN n total ≤ 2 ^ 98 := by
  have hm : min total (n * 2 ^ 16) ≤ 2 ^ 64 := (min_le_left _ _).trans ht
  have hc : randomizerAttemptLimit = 2 ^ 32 := by unfold randomizerAttemptLimit; norm_num
  have hl : layerProgCap ≤ 2 ^ 10 := by
    rw [layerProgCap]
    norm_num [chainCount, chainLength, layerHeight, winternitzBits, lifetime, layerCount]
  calc clsCapN n total = 1 + (2 ^ 32 + 5 + 2 * layerProgCap) * total +
        2 ^ 32 * min total (n * 2 ^ 16) + 384 := by rw [clsCapN, verifyCalls_eq, hc]
    _ ≤ 1 + (2 ^ 32 + 5 + 2 * 2 ^ 10) * 2 ^ 64 + 2 ^ 32 * 2 ^ 64 + 384 := by gcongr
    _ ≤ 2 ^ 98 := by norm_num

end Quantum.Qrom.Xmss.Multi

end
