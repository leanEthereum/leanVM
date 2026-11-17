module

public import Quantum.Qrom.Sphincs.Costs.RecUFirst
public import Quantum.Qrom.Sphincs.Costs.RecUFail

@[expose] public section

/-!
# The recorded unselected weights of leanSPHINCS's challenge prefix, averaged

* **`uavg_recUPre_le`**: averaged over the hidden values, the recorded unselected weights of the
  trial reads (`recUPre`) are at most `tauU q K = q / 2^128 + K / 2^200`: the weights move onto
  the reveals of the keys' coordinates (`recUPre_le_split`), the first reveals cost `2^-128` per
  sponge call (`sum_totalWeight_firstQW_le`: a cell at a key's encoding slot is one trial of one
  value, and each digest has `2^384` of the `2^512` pairs), the repeated reveals with the key
  unselected `2^-200` per classical call (`totalWeight_reRevQW_le`: failed searches).
* **`tauU_le`**: the form `cU · q / 2^128 + K / 2^200`, with `cU = 1`.
-/

open Matrix IPFunctor
open scoped ENNReal
open HashSig hiding PublicKey
open Sphincs hiding HashDomain

namespace Quantum.Qrom.Sphincs

open Quantum QuantumRuntime Quantum.Sponge
open Quantum.Xmss.Hybrid (uavg)
open Quantum.Xmss.Assembly (runtimeR recSpec extCls)

attribute [local irreducible] sphincsRom Fin.fintype

/-- **The bound on the averaged recorded unselected weights**: `2^-128` per sponge call, `2^-200`
per classical call. -/
noncomputable def tauU (q K : ℕ) : ℝ≥0∞ :=
  q * (2 ^ 128 : ℝ≥0∞)⁻¹ + K * (2 ^ 200 : ℝ≥0∞)⁻¹

/-- **The averaged recorded unselected weights.** -/
theorem uavg_recUPre_le (pol : DigestPolicy) (A : SAdversary) {q K : ℕ} (hpol : pol.NoVal)
    (hq : ∀ θ, IFreeM.IsChargeBound (prefixQ pol A θ) (portCharge fun i ↦
      if extCls PairOut Qrom.HashDomain QMem (recSpec TPos SelMem) i then 0 else 1) q)
    (hK : ∀ θ, IFreeM.IsChargeBound (prefixQ pol A θ) (portCharge fun i ↦
      if extCls PairOut Qrom.HashDomain QMem (recSpec TPos SelMem) i then 1 else 0) K) :
    Quantum.Xmss.Hybrid.uavg (fun θ : TVals ↦ recUPre pol A θ) ≤ tauU q K := by
  set N : ℝ≥0∞ := (Fintype.card TVals : ℝ≥0∞)
  have hN0 : N ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hNt : N ≠ ⊤ := ENNReal.natCast_ne_top _
  have hsum : ∑ θ : TVals, recUPre pol A θ ≤
      (2 ^ 128 : ℝ≥0∞)⁻¹ * q * N + N * (K * (2 ^ 200 : ℝ≥0∞)⁻¹) := by
    refine (Finset.sum_le_sum fun θ _ ↦ recUPre_le_split hpol A θ).trans ?_
    rw [Finset.sum_add_distrib]
    refine add_le_add (sum_totalWeight_firstQW_le hpol A hq) ?_
    refine (Finset.sum_le_sum fun θ _ ↦ totalWeight_reRevQW_le hpol A θ (hK θ)).trans ?_
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  unfold uavg tauU
  refine (mul_le_mul_of_nonneg_left hsum zero_le).trans (le_of_eq ?_)
  rw [mul_add, ← mul_assoc N⁻¹ N, ENNReal.inv_mul_cancel hN0 hNt, one_mul,
    mul_comm _ N, ← mul_assoc, ← mul_assoc, ENNReal.inv_mul_cancel hN0 hNt, one_mul]
  ring

/-- **`tauU` in the closed form** `cU · q / 2^128 + K / 2^200`, with `cU = 1`. -/
theorem tauU_le (q K : ℕ) :
    tauU q K ≤ ((1 : ℕ) : ℝ≥0∞) * q * (2 ^ 128 : ℝ≥0∞)⁻¹ + K * (2 ^ 200 : ℝ≥0∞)⁻¹ := by
  rw [Nat.cast_one, one_mul]
  exact le_rfl

end Quantum.Qrom.Sphincs

end
