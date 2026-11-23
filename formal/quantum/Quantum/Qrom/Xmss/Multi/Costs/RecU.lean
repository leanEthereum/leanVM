module

public import Quantum.Qrom.Xmss.Multi.Costs.RecUFirst
public import Quantum.Qrom.Xmss.Multi.Costs.RecUFail

@[expose] public section

/-!
# The recorded unselected weights of the `n`-user challenge prefix, averaged

The `n`-user analog of `Quantum.Qrom.Xmss.Costs.RecU`, on distinct parameters (`recUMaskN`).

* **`uavg_recUPreN_le`**: averaged over the hidden values, the recorded unselected weights of the
  trial reads on distinct parameters are at most `2^32 q / 2^128 + K / 2^1000`: the weights move
  onto the reveals of the randomizer bases (`recUPreN_le_split`), the first reveals cost
  `2^32 / 2^128` per sponge call summed over the bases (`sum_totalWeight_firstQWN_le`), the
  repeated reveals with the key unselected `2^-1000` per classical call
  (`totalWeight_reRevQWN_le`).
-/

open Matrix IPFunctor
open scoped ENNReal

namespace Quantum.Qrom.Xmss.Multi

open Quantum QuantumRuntime Quantum.Sponge HashSig LeanXmss
open Quantum.Xmss.Hybrid (uavg)
open Quantum.Xmss.Assembly (runtimeR recSpec extCls)

attribute [local irreducible] xmssRom

variable {n : ℕ}

/-- **The averaged recorded unselected weights** on distinct parameters. -/
theorem uavg_recUPreN_le (A : MuAdversary n) (hn : n ≤ 2 ^ 128) {q K : ℕ}
    (hq : ∀ θ, IFreeM.IsChargeBound (prefixQN A θ) (portCharge fun i ↦
      if extCls HashOutput HashDomain (QMemN n) (recSpec (HPosN n) (SelMemN n)) i then 0 else 1)
      q)
    (hK : ∀ θ, IFreeM.IsChargeBound (prefixQN A θ) (portCharge fun i ↦
      if extCls HashOutput HashDomain (QMemN n) (recSpec (HPosN n) (SelMemN n)) i then 1 else 0)
      K) :
    uavg (recUMaskN A) ≤ q * 2 ^ 32 * (2 ^ 128 : ℝ≥0∞)⁻¹ + K * (2 ^ 1000 : ℝ≥0∞)⁻¹ := by
  set N : ℝ≥0∞ := (Fintype.card (HPosN n → Digest) : ℝ≥0∞)
  have hN0 : N ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hNt : N ≠ ⊤ := ENNReal.natCast_ne_top _
  have hsum : ∑ θ : HPosN n → Digest, recUMaskN A θ ≤
      (randomizerAttemptLimit : ℝ≥0∞) * (2 ^ 128 : ℝ≥0∞)⁻¹ * q * N +
        N * (K * (2 ^ 1000 : ℝ≥0∞)⁻¹) := by
    refine (Finset.sum_le_sum fun θ _ ↦ (?_ : recUMaskN A θ ≤ firstMaskN A θ +
      (runtimeR (m0N (n := n))).totalWeight .instruments reRevQWN (prefixQN A θ)
        initQN)).trans ?_
    · classical
      unfold recUMaskN firstMaskN
      split_ifs
      · exact recUPreN_le_split A θ
      · exact zero_le
    rw [Finset.sum_add_distrib]
    refine add_le_add (sum_totalWeight_firstQWN_le A hq) ?_
    refine (Finset.sum_le_sum fun θ _ ↦ totalWeight_reRevQWN_le A θ hn (hK θ)).trans ?_
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

end Quantum.Qrom.Xmss.Multi

end
