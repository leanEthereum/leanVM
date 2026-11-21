module

public import Quantum.Qrom.Sphincs.Multi.Costs.RecUFirst
public import Quantum.Qrom.Sphincs.Multi.Costs.RecUFail
public import Quantum.Qrom.Sphincs.Multi.Costs.Numeric

@[expose] public section

/-!
# The recorded unselected weights of the `n`-user challenge prefix, averaged

The `n`-user analog of `Quantum.Qrom.Sphincs.Costs.RecU`, on distinct `PK.seed`s (`recUMaskSN`).

* **`uavg_recUPreSN_le`**: averaged over the hidden values, the recorded unselected weights of the
  trial reads on distinct `PK.seed`s are at most `tauUN q K = q / 2^128 + K / 2^1000`: the weights
  move onto the reveals of the users' keys' coordinates (`recUPreSN_le_split`), the first reveals
  cost `2^-128` per sponge call (`sum_totalWeight_firstQWSN_le`), the repeated reveals with the key
  unselected `2^-1000` per classical call (`totalWeight_reRevQWSN_le`).
-/

open Matrix IPFunctor
open scoped ENNReal
open HashSig hiding PublicKey
open Sphincs hiding HashDomain

namespace Quantum.Qrom.Sphincs.Multi

open Quantum QuantumRuntime Quantum.Sponge
open Quantum.Xmss.Hybrid (uavg)
open Quantum.Xmss.Assembly (runtimeR recSpec extCls)

attribute [local irreducible] sphincsRom Fin.fintype

variable {n : ℕ}

/-- **The averaged recorded unselected weights** on distinct `PK.seed`s: `2^-128` per sponge
call, `2^-1000` per classical call. -/
theorem uavg_recUPreSN_le (A : MuAdversaryS n) (hn : n ≤ 2 ^ 128) {q K : ℕ}
    (hq : ∀ θ, IFreeM.IsChargeBound (prefixQSN (strPolN n) A θ) (portCharge fun i ↦
      if extCls PairOut HashDomain (QMemSN n) (recSpec (TPosN n) (SelMemN n)) i then 0 else 1)
      q)
    (hK : ∀ θ, IFreeM.IsChargeBound (prefixQSN (strPolN n) A θ) (portCharge fun i ↦
      if extCls PairOut HashDomain (QMemSN n) (recSpec (TPosN n) (SelMemN n)) i then 1 else 0)
      K) :
    uavg (recUMaskSN A) ≤ tauUN q K := by
  set N : ℝ≥0∞ := (Fintype.card (TValsN n) : ℝ≥0∞)
  have hN0 : N ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hNt : N ≠ ⊤ := ENNReal.natCast_ne_top _
  have hsum : ∑ θ : TValsN n, recUMaskSN A θ ≤
      (2 ^ 128 : ℝ≥0∞)⁻¹ * q * N + N * (K * (2 ^ 1000 : ℝ≥0∞)⁻¹) := by
    refine (Finset.sum_le_sum fun θ _ ↦ (?_ : recUMaskSN A θ ≤ firstMaskSN A θ +
      (runtimeR (m0SN (n := n))).totalWeight .instruments reRevQWSN
        (prefixQSN (strPolN n) A θ) initQSN)).trans ?_
    · classical
      unfold recUMaskSN firstMaskSN
      split_ifs
      · exact recUPreSN_le_split A θ
      · exact zero_le
    rw [Finset.sum_add_distrib]
    refine add_le_add (sum_totalWeight_firstQWSN_le A hq) ?_
    refine (Finset.sum_le_sum fun θ _ ↦ totalWeight_reRevQWSN_le A θ hn (hK θ)).trans ?_
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  unfold uavg tauUN
  refine (mul_le_mul_of_nonneg_left hsum zero_le).trans (le_of_eq ?_)
  rw [mul_add, ← mul_assoc N⁻¹ N, ENNReal.inv_mul_cancel hN0 hNt, one_mul,
    mul_comm _ N, ← mul_assoc, ← mul_assoc, ENNReal.inv_mul_cancel hN0 hNt, one_mul]
  ring

end Quantum.Qrom.Sphincs.Multi

end
