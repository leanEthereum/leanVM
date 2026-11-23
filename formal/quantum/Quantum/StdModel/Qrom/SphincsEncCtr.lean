module

public import Quantum.StdModel.Qrom.SphincsEncCtrJu
public import Quantum.StdModel.Qrom.SphincsEncCtrSetup
public import Quantum.StdModel.Qrom.SphincsEncCtrLive
public import Quantum.StdModel.Qrom.CpreValue

@[expose] public section

/-!
# EncTCR+C at leanSPHINCS B4 in the QROM

* `SphEnc.probAvg_encTcrCtrIn_encRed_le`: the committed bound `EncTcr.encTcrCtrIn_probAvg_le` at
  B4, with the live invariant `EncJu`, established by the setup (`encJu_pre`) and kept by the
  handler (`encJu_sign`, the signer's re-grinds re-reading the challenger's trials) and the
  output's six reads at the classes (`encJu_post`):
  `probAvg ≤ (q √(6 · 2^128 / 2^256) + 7 √(gradeEta 2^128))²`.
* `SphInst.probAvg_encTcrCtrIn_encRed_le_closed`: `probAvg ≤ ((2.45 q + 21.01) / 2^64)²`.
-/

open OracleComp OracleSpec
open scoped ENNReal
open HashSig hiding PublicKey
open Sphincs hiding HashDomain

namespace Quantum.StdModel.Qrom.SphEnc

open Quantum.StdModel Props Quantum.StdModel.Sphincs

attribute [local irreducible] LiveRedRun LiveRun encRedPost encRedSign encRedPre

/-- **EncTCR+C at leanSPHINCS B4 in the QROM**: for an adversary of `q` hash calls and any number
of signing requests, `probAvg ≤ (q √(6 · 2^128 / 2^256) + 7 √(gradeEta 2^128))²`. -/
theorem probAvg_encTcrCtrIn_encRed_le (A : SAdv romWorld) {q : ℕ}
    (hq : ∀ pk, IPFunctor.IFreeM.IsChargeBound (A pk) (cmdCharge hashCharge) q) :
    romWorld.probAvg ((encTcrCtrIn romWorld encCtr slotColl EncTwIn).game
        (encRed romWorld A)) ≤
      (q * (6 * (((2 ^ 128 : ℕ) : ℝ≥0∞) / Fintype.card HashOutput)) ^ (2⁻¹ : ℝ) +
        (nB : ℝ≥0∞) * ENNReal.ofReal (gradeEta HashOutput (2 ^ 128)) ^ (2⁻¹ : ℝ)) ^ 2 :=
  probAvg_encTcrCtrIn_encRed_le_ju A hq (fun P a μ h ↦ encJu_pre P a μ h)
    (fun P a st log μ M hI hJ r μ' h ↦ encJu_sign P a st log μ M hI hJ r μ' h)

end Quantum.StdModel.Qrom.SphEnc

namespace Quantum.StdModel.Qrom.SphInst

open Quantum.StdModel Props Quantum.StdModel.Sphincs
open Quantum.StdModel.Qrom.CpreQ (ofReal_rpow_inv_two sqrt_gradeEta_le)

/-- **The EncTCR+C price in closed form**:
`(q √(6 · 2^128 / 2^256) + 7 √(gradeEta 2^128))² ≤ ((2.45 q + 21.01) / 2^64)²`. -/
theorem encCtr_closed_le (q : ℕ) :
    ((q : ℝ≥0∞) * (6 * (((2 ^ 128 : ℕ) : ℝ≥0∞) / Fintype.card HashOutput)) ^ (2⁻¹ : ℝ) +
        ((7 : ℕ) : ℝ≥0∞) * ENNReal.ofReal (gradeEta HashOutput (2 ^ 128)) ^ (2⁻¹ : ℝ)) ^ 2 ≤
      ENNReal.ofReal (((2.45 * q + 21.01) / 2 ^ 64) ^ 2) := by
  have h6 : (6 * (((2 ^ 128 : ℕ) : ℝ≥0∞) / Fintype.card HashOutput)) =
      ENNReal.ofReal (6 * (((2 ^ 128 : ℕ) : ℝ) / ((2 ^ 256 : ℕ) : ℝ))) := by
    rw [card_hashOutput', ENNReal.ofReal_mul (by norm_num),
      ENNReal.ofReal_div_of_pos (by positivity), ENNReal.ofReal_natCast, ENNReal.ofReal_natCast,
      ENNReal.ofReal_ofNat]
  have hs6 : √(6 * (((2 ^ 128 : ℕ) : ℝ) / ((2 ^ 256 : ℕ) : ℝ))) ≤ 2.45 / 2 ^ 64 :=
    Real.sqrt_le_iff.mpr ⟨by positivity, by push_cast; norm_num⟩
  have hsg : √(gradeEta HashOutput (2 ^ 128)) ≤ 3.001 / 2 ^ 64 :=
    sqrt_gradeEta_le.trans (by norm_num)
  rw [h6, ofReal_rpow_inv_two _ (by positivity), ofReal_rpow_inv_two _ (gradeEta_nonneg _ _),
    ← ENNReal.ofReal_natCast q, ← ENNReal.ofReal_natCast 7,
    ← ENNReal.ofReal_mul (Nat.cast_nonneg _), ← ENNReal.ofReal_mul (Nat.cast_nonneg _),
    ← ENNReal.ofReal_add (by positivity) (by positivity),
    ← ENNReal.ofReal_pow (by positivity)]
  refine ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (by positivity) ?_ 2)
  have hq : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  calc (q : ℝ) * √(6 * (((2 ^ 128 : ℕ) : ℝ) / ((2 ^ 256 : ℕ) : ℝ))) +
        ((7 : ℕ) : ℝ) * √(gradeEta HashOutput (2 ^ 128))
      ≤ q * (2.45 / 2 ^ 64) + 7 * (3.001 / 2 ^ 64) := by
        rw [show ((7 : ℕ) : ℝ) = 7 by norm_num]
        gcongr
    _ ≤ (2.45 * q + 21.01) / 2 ^ 64 := by
        rw [div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv]
        nlinarith [show (0 : ℝ) < (2 ^ 64)⁻¹ by positivity]

/-- **EncTCR+C at leanSPHINCS B4 in the QROM, in closed form**: for an adversary of `q` hash calls
and any number of signing requests, `probAvg ≤ ((2.45 q + 21.01) / 2^64)²`. -/
theorem probAvg_encTcrCtrIn_encRed_le_closed (A : SAdv romWorld) {q : ℕ}
    (hq : ∀ pk, IPFunctor.IFreeM.IsChargeBound (A pk) (cmdCharge hashCharge) q) :
    romWorld.probAvg ((encTcrCtrIn romWorld encCtr slotColl EncTwIn).game
        (encRed romWorld A)) ≤
      ENNReal.ofReal (((2.45 * q + 21.01) / 2 ^ 64) ^ 2) :=
  (SphEnc.probAvg_encTcrCtrIn_encRed_le A hq).trans (encCtr_closed_le q)

end Quantum.StdModel.Qrom.SphInst

end
