module

public import Quantum.Qrom.Xmss.Costs.RecUFirst
public import Quantum.Qrom.Xmss.Costs.RecUFail

@[expose] public section

/-!
# The recorded unselected weights of the challenge prefix, averaged

* **`uavg_recUPre_le'`**: averaged over the hidden values, the recorded unselected weights of the
  trial reads (`recUPre`) are at most `2^32 q / 2^128 + K / 2^1000`: the weights move onto the
  reveals of the randomizer bases (`recUPre_le_split`), the first reveals cost `2^32 / 2^128` per
  sponge call summed over the bases (`sum_totalWeight_firstQW_le`), the repeated reveals with the
  key unselected `2^-1000` per classical call (`totalWeight_reRevQW_le`).
* **`uavg_recUPre_le`**: the stated form, with the constant `4`.
-/

open Matrix IPFunctor
open scoped ENNReal

namespace Quantum.Qrom.Xmss

open Quantum QuantumRuntime Quantum.Sponge HashSig LeanXmss
open Quantum.Xmss.Hybrid (uavg)
open Quantum.Xmss.Assembly (runtimeR recSpec extCls)

attribute [local irreducible] xmssRom

/-- **The averaged recorded unselected weights**, with the constant `1`. -/
theorem uavg_recUPre_le' (A : Adversary) {q K : ℕ}
    (hq : ∀ θ, IFreeM.IsChargeBound (prefixQ A θ) (portCharge fun i ↦
      if extCls HashOutput HashDomain QMem (recSpec HPos SelMem) i then 0 else 1) q)
    (hK : ∀ θ, IFreeM.IsChargeBound (prefixQ A θ) (portCharge fun i ↦
      if extCls HashOutput HashDomain QMem (recSpec HPos SelMem) i then 1 else 0) K) :
    uavg (fun θ : HPos → Digest ↦ recUPre A θ) ≤
      q * 2 ^ 32 * (2 ^ 128 : ℝ≥0∞)⁻¹ + K * (2 ^ 1000 : ℝ≥0∞)⁻¹ := by
  set N : ℝ≥0∞ := (Fintype.card (HPos → Digest) : ℝ≥0∞)
  have hN0 : N ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hNt : N ≠ ⊤ := ENNReal.natCast_ne_top _
  have hsum : ∑ θ : HPos → Digest, recUPre A θ ≤
      (randomizerAttemptLimit : ℝ≥0∞) * (2 ^ 128 : ℝ≥0∞)⁻¹ * q * N +
        N * (K * (2 ^ 1000 : ℝ≥0∞)⁻¹) := by
    refine (Finset.sum_le_sum fun θ _ ↦ recUPre_le_split A θ).trans ?_
    rw [Finset.sum_add_distrib]
    refine add_le_add (sum_totalWeight_firstQW_le A hq) ?_
    refine (Finset.sum_le_sum fun θ _ ↦ totalWeight_reRevQW_le A θ (hK θ)).trans ?_
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  unfold uavg
  refine (mul_le_mul_of_nonneg_left hsum zero_le).trans (le_of_eq ?_)
  rw [mul_add, ← mul_assoc N⁻¹ N, ENNReal.inv_mul_cancel hN0 hNt, one_mul,
    mul_comm _ N, ← mul_assoc, ← mul_assoc, ENNReal.inv_mul_cancel hN0 hNt, one_mul]
  have h32 : (randomizerAttemptLimit : ℝ≥0∞) = 2 ^ 32 := by
    unfold randomizerAttemptLimit
    norm_num
  rw [h32]
  ring

/-- **The averaged recorded unselected weights** (the stated form). -/
theorem uavg_recUPre_le (A : Adversary) {q K : ℕ}
    (hq : ∀ θ, IFreeM.IsChargeBound (prefixQ A θ) (portCharge fun i ↦
      if extCls HashOutput HashDomain QMem (recSpec HPos SelMem) i then 0 else 1) q)
    (hK : ∀ θ, IFreeM.IsChargeBound (prefixQ A θ) (portCharge fun i ↦
      if extCls HashOutput HashDomain QMem (recSpec HPos SelMem) i then 1 else 0) K) :
    uavg (fun θ : HPos → Digest ↦ recUPre A θ) ≤
      4 * q * 2 ^ 32 * (2 ^ 128 : ℝ≥0∞)⁻¹ + K * (2 ^ 1000 : ℝ≥0∞)⁻¹ := by
  refine (uavg_recUPre_le' A hq hK).trans (add_le_add ?_ le_rfl)
  refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ?_ zero_le) zero_le
  exact le_mul_of_one_le_left zero_le (by norm_num)

end Quantum.Qrom.Xmss

end
