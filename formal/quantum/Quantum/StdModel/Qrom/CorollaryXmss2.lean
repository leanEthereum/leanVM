module

public import Quantum.StdModel.Qrom.CorollaryXmss
public import Quantum.StdModel.Qrom.CpreValue
public import Quantum.StdModel.Qrom.XmssTcr2
public import Quantum.StdModel.Qrom.SphincsTcr

@[expose] public section

/-!
# leanXMSS in the QROM through its properties, in closed form

* `natCast_sq_mul_gradeEta_le`: `n² · gradeEta 2^128 ≤ (3.001 n / 2^64)²`, from
  `√(gradeEta 2^128) ≤ (3 + 2^-64) / 2^64` (`CpreQ.sqrt_gradeEta_le`). So the SM-TCR-C successes
  are at most `((3.001 (q + 294)) / 2^64)²` at leanXMSS B4 (`probAvg_smTcrIn_tcrRed_le_closed`)
  and `((3.001 (q + 11813)) / 2^64)²` at leanSPHINCS B6
  (`Sphincs.probAvg_smTcrIn_tcrRed_le_closed`), for `q` adversary hash calls.
* `leanXmss_qrom_security_props_of_enc`: Theorem 1 restricted to in-kind targets, averaged over
  the tables, through no leaf reuse (`winProb_xmssRom_le_of_refuse`), with KIM-PRF in closed form
  (`prfTerm_le`), CPRE at B3 (`probAvg_cpreRed_le_closed`) and SM-TCR-C at B4, given a bound `E`
  on the QROM EncTCR$ success of B2: for `q` hash calls and `m ≤ 2^32` signing requests,
  `winProb ≤ (6 q + 2^68) / 2^128 + E + ((5.001 q + 2650) / 2^64)² + ((3.001 (q + 294)) / 2^64)²`.
* `leanXmss_qrom_security_props_of_enc_closed`: the same sum as one fraction,
  `E + ((5.001 q + 2650)² + (3.001 q + 883)² + 6 q + 2^68) / 2^128`.
-/

open IPFunctor OracleComp OracleSpec HashSig LeanXmss
open scoped ENNReal

namespace Quantum.StdModel.Xmss

open Quantum.StdModel Props
open Quantum.StdModel.Qrom (gradeEta gradeEta_nonneg)

/-! ## The graded price in closed form -/

/-- **`n² · gradeEta 2^128 ≤ (3.001 n / 2^64)²`.** -/
theorem natCast_sq_mul_gradeEta_le (n : ℕ) :
    (n : ℝ≥0∞) ^ 2 * ENNReal.ofReal (gradeEta HashOutput (2 ^ 128)) ≤
      ENNReal.ofReal ((3.001 * n / 2 ^ 64) ^ 2) := by
  have hs : √(gradeEta HashOutput (2 ^ 128)) ≤ 3.001 / 2 ^ 64 :=
    Qrom.CpreQ.sqrt_gradeEta_le.trans (by norm_num)
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_pow (Nat.cast_nonneg _),
    ← ENNReal.ofReal_mul (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [← Real.sq_sqrt (gradeEta_nonneg HashOutput (2 ^ 128)), ← mul_pow]
  refine pow_le_pow_left₀ (by positivity) ?_ 2
  calc (n : ℝ) * √(gradeEta HashOutput (2 ^ 128)) ≤ n * (3.001 / 2 ^ 64) :=
        mul_le_mul_of_nonneg_left hs (Nat.cast_nonneg _)
    _ = 3.001 * n / 2 ^ 64 := by ring

/-- **leanXMSS's SM-TCR-C game played by B4, in closed form**: for an adversary of `q` hash calls,
`probAvg ≤ ((3.001 (q + 294)) / 2^64)²`. -/
theorem probAvg_smTcrIn_tcrRed_le_closed
    (A : SufAdversary romWorld PublicKey SigningRequest (Option Signature) Forgery) {q : ℕ}
    (hq : ∀ pk, IFreeM.IsChargeBound (A pk) (cmdCharge hashCharge) q) :
    romWorld.probAvg ((smTcrIn romWorld xmssTcrC xmssTcrD TcrInKind).game (tcrRed romWorld A)) ≤
      ENNReal.ofReal ((3.001 * (q + 294) / 2 ^ 64) ^ 2) := by
  refine (probAvg_smTcrIn_tcrRed_le A hq).trans ((natCast_sq_mul_gradeEta_le _).trans_eq ?_)
  push_cast
  rfl

/-! ## The leanXMSS corollary given B2 -/

/-- **leanXMSS in the QROM through its properties, given B2.** For an adversary of `q` hash calls
and `m ≤ 2^32` signing requests, if the QROM EncTCR$ success of B2 run on `refuse A` is at most
`E`, then `A` wins with probability at most
`(6 q + 2^68) / 2^128 + E + ((5.001 q + 2650) / 2^64)² + ((3.001 (q + 294)) / 2^64)²`: KIM-PRF
(B1), EncTCR$ (B2), CPRE (B3) and SM-TCR-C (B4). -/
theorem leanXmss_qrom_security_props_of_enc (A : Qrom.Xmss.Adversary) {q m : ℕ}
    (hq : ∀ pk, IFreeM.IsChargeBound (A pk) (Qrom.SufCma.cmdCharge Qrom.SufCma.hashCharge) q)
    (hm : ∀ pk, IFreeM.IsChargeBound (A pk) (Qrom.SufCma.cmdCharge Qrom.SufCma.signCharge) m)
    (hm32 : m ≤ 2 ^ 32) {E : ℝ≥0∞}
    (hEnc : romWorld.probAvg ((encTcrSalt romWorld xmssEnc).game
      (encRed romWorld (ofQrom (Qrom.Xmss.refuse A)))) ≤ E) :
    Qrom.SufCma.winProb Qrom.Xmss.xmssRom A ≤
      ENNReal.ofReal ((6 * q + 2 ^ 68) / 2 ^ 128) + E +
        ENNReal.ofReal (((5.001 * q + 2650) / 2 ^ 64) ^ 2) +
        ENNReal.ofReal ((3.001 * (q + 294) / 2 ^ 64) ^ 2) := by
  have hq' : ∀ pk, IFreeM.IsChargeBound (ofQrom (Qrom.Xmss.refuse A) pk) (cmdCharge hashCharge) q :=
    isChargeBound_ofQrom_hash fun pk ↦ Qrom.Xmss.isChargeBound_refuse (hq pk)
  have hm' : ∀ pk, IFreeM.IsChargeBound (ofQrom (Qrom.Xmss.refuse A) pk) (cmdCharge callCharge)
      m :=
    isChargeBound_ofQrom_call fun pk ↦ Qrom.Xmss.isChargeBound_refuse (hm pk)
  refine (winProb_xmssRom_le_of_refuse A hq hm hEnc (probAvg_cpreRed_le_closed _ hq' hm')
    (probAvg_smTcrIn_tcrRed_le_closed _ hq')).trans ?_
  gcongr
  exact prfTerm_le q hm32

/-- **The sum in closed form**:
`E + ((5.001 q + 2650)² + (3.001 q + 883)² + 6 q + 2^68) / 2^128`. -/
theorem propsSum_le (q : ℕ) (E : ℝ≥0∞) :
    ENNReal.ofReal ((6 * q + 2 ^ 68) / 2 ^ 128) + E +
        ENNReal.ofReal (((5.001 * q + 2650) / 2 ^ 64) ^ 2) +
        ENNReal.ofReal ((3.001 * (q + 294) / 2 ^ 64) ^ 2) ≤
      E + ENNReal.ofReal (((5.001 * q + 2650) ^ 2 + (3.001 * q + 883) ^ 2 + 6 * q + 2 ^ 68) /
        2 ^ 128) := by
  have hq : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  have h3 : (3.001 * ((q : ℝ) + 294) / 2 ^ 64) ^ 2 ≤ (3.001 * q + 883) ^ 2 / 2 ^ 128 := by
    rw [div_pow, show ((2 : ℝ) ^ 64) ^ 2 = 2 ^ 128 by norm_num]
    gcongr
    linarith
  have h5 : ((5.001 * (q : ℝ) + 2650) / 2 ^ 64) ^ 2 = (5.001 * q + 2650) ^ 2 / 2 ^ 128 := by
    rw [div_pow]
    norm_num
  calc ENNReal.ofReal ((6 * q + 2 ^ 68) / 2 ^ 128) + E +
          ENNReal.ofReal (((5.001 * q + 2650) / 2 ^ 64) ^ 2) +
          ENNReal.ofReal ((3.001 * (q + 294) / 2 ^ 64) ^ 2)
      = E + (ENNReal.ofReal ((6 * q + 2 ^ 68) / 2 ^ 128) +
          ENNReal.ofReal (((5.001 * q + 2650) / 2 ^ 64) ^ 2) +
          ENNReal.ofReal ((3.001 * (q + 294) / 2 ^ 64) ^ 2)) := by ring
    _ ≤ E + ENNReal.ofReal (((5.001 * q + 2650) ^ 2 + (3.001 * q + 883) ^ 2 + 6 * q + 2 ^ 68) /
          2 ^ 128) := by
        gcongr
        rw [← ENNReal.ofReal_add (by positivity) (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
        refine ENNReal.ofReal_le_ofReal ?_
        rw [h5]
        calc (6 * (q : ℝ) + 2 ^ 68) / 2 ^ 128 + (5.001 * q + 2650) ^ 2 / 2 ^ 128 +
              (3.001 * (q + 294) / 2 ^ 64) ^ 2
            ≤ (6 * (q : ℝ) + 2 ^ 68) / 2 ^ 128 + (5.001 * q + 2650) ^ 2 / 2 ^ 128 +
              (3.001 * q + 883) ^ 2 / 2 ^ 128 := by gcongr
          _ = _ := by ring

/-- **leanXMSS in the QROM through its properties, given B2, as one fraction**: for `q` hash
calls and `m ≤ 2^32` signing requests,
`winProb ≤ E + ((5.001 q + 2650)² + (3.001 q + 883)² + 6 q + 2^68) / 2^128`. -/
theorem leanXmss_qrom_security_props_of_enc_closed (A : Qrom.Xmss.Adversary) {q m : ℕ}
    (hq : ∀ pk, IFreeM.IsChargeBound (A pk) (Qrom.SufCma.cmdCharge Qrom.SufCma.hashCharge) q)
    (hm : ∀ pk, IFreeM.IsChargeBound (A pk) (Qrom.SufCma.cmdCharge Qrom.SufCma.signCharge) m)
    (hm32 : m ≤ 2 ^ 32) {E : ℝ≥0∞}
    (hEnc : romWorld.probAvg ((encTcrSalt romWorld xmssEnc).game
      (encRed romWorld (ofQrom (Qrom.Xmss.refuse A)))) ≤ E) :
    Qrom.SufCma.winProb Qrom.Xmss.xmssRom A ≤
      E + ENNReal.ofReal (((5.001 * q + 2650) ^ 2 + (3.001 * q + 883) ^ 2 + 6 * q + 2 ^ 68) /
        2 ^ 128) :=
  (leanXmss_qrom_security_props_of_enc A hq hm hm32 hEnc).trans (propsSum_le q E)

end Quantum.StdModel.Xmss

namespace Quantum.StdModel.Sphincs

open Quantum.StdModel Props

/-- **leanSPHINCS's SM-TCR-C game played by B6, in closed form**: for an adversary of `q` hash
calls and any number of signing requests, `probAvg ≤ ((3.001 (q + 11813)) / 2^64)²`. -/
theorem probAvg_smTcrIn_tcrRed_le_closed (A : SAdv romWorld) {q : ℕ}
    (hq : ∀ pk, IFreeM.IsChargeBound (A pk) (cmdCharge hashCharge) q) :
    romWorld.probAvg ((smTcrIn romWorld tcrColl slotColl TcrTwIn).game (tcrRed romWorld A)) ≤
      ENNReal.ofReal ((3.001 * (q + 11813) / 2 ^ 64) ^ 2) := by
  refine (probAvg_smTcrIn_tcrRed_le A hq).trans
    ((Quantum.StdModel.Xmss.natCast_sq_mul_gradeEta_le _).trans_eq ?_)
  push_cast
  rfl

end Quantum.StdModel.Sphincs

end
