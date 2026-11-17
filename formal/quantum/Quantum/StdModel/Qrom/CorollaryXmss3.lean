module

public import Quantum.StdModel.Qrom.CorollaryXmss2
public import Quantum.StdModel.Qrom.XmssEncSaltTW
public import Quantum.StdModel.Qrom.XmssEncSaltBudget
public import Quantum.StdModel.Qrom.EncSaltCode

@[expose] public section

/-!
# leanXMSS in the QROM through its properties, unconditionally

* **B2's EncTCR$ term** (`probAvg_encTcrSalt_encRed_le_closed`): the graded bound with live
  budget `q + 4` (`probAvg_encTcrSalt_encRed_le_budget`) and the trial-read weight
  `TW ≤ λ (q + 2) + c₀ (2 m)` (`totalWeight_encRed_le`, per answer `ansCode`), with
  `λ ≤ (2^34 + 1)/2^128` (`lamS_xmssEnc_le`) and `c₀ ≤ (2^33 + 1)/2^128` (`c0C_xmssEnc_le`):
  `(2 (3.001 (q + 4))² + (2^35 + 2)(q + 2) + 2^67 + 2^34) / 2^128`
  (`encSalt_closed_le`, `tw_closed_le`, `encSalt_term_closed_le`).
* **leanXMSS** (`leanXmss_qrom_security_props`, `leanXmss_qrom_security_props_closed`): with
  the committed KIM-PRF, CPRE and SM-TCR-C terms
  (`leanXmss_qrom_security_props_of_enc_closed`), for `q` hash calls and `m ≤ 2^32` requests,
  `winProb ≤ ((5.001 q + 2650)² + (3.001 q + 883)² + 2 (3.001 (q + 4))² + (2^35 + 2)(q + 2) +
  6 q + 3 · 2^67 + 2^34) / 2^128`.
-/

open IPFunctor OracleComp OracleSpec HashSig LeanXmss
open scoped ENNReal

namespace Quantum.StdModel.Xmss

open Quantum.StdModel Props
open Quantum.StdModel.Qrom (gradeEta gradeEta_nonneg)
open Quantum.StdModel.Qrom.CpreQ (ofReal_rpow_inv_two sqrt_gradeEta_le)

/-- The randomizers: `2^128`. -/
theorem card_randomizer_eq : Fintype.card Randomizer = 2 ^ 128 := by
  rw [← FinEnum.card_eq_fintypeCard, FinEnum.card_bitVec]
  rfl

/-- **The slope of an answer's cost at leanXMSS**: `λ ≤ (2^34 + 1) / 2^128`. -/
theorem lamS_xmssEnc_le : Qrom.EncSalt.lamS xmssEnc (2 ^ 128) ≤ (2 ^ 34 + 1) / 2 ^ 128 := by
  unfold Qrom.EncSalt.lamS
  have hN : (Fintype.card HashOutput : ℝ) = 2 ^ 256 := by
    exact_mod_cast Qrom.CpreQ.card_hashOutput_eq
  have hS : (Fintype.card Randomizer : ℝ) = 2 ^ 128 := by exact_mod_cast card_randomizer_eq
  have hl : (xmssEnc.limit : ℝ) = 2 ^ 32 := by
    norm_num [xmssEnc, randomizerAttemptLimit]
  rw [hN, hS, hl]
  norm_num

/-- **The constant of an answer's cost at leanXMSS, with every trial cell a partner**:
`c₀ ≤ (2^65 + 2^33 + 1) / 2^128`. -/
theorem c0S_xmssEnc_le : Qrom.EncSalt.c0S xmssEnc (2 ^ 128) ≤ (2 ^ 65 + 2 ^ 33 + 1) / 2 ^ 128 := by
  unfold Qrom.EncSalt.c0S
  have hN : (Fintype.card HashOutput : ℝ) = 2 ^ 256 := by
    exact_mod_cast Qrom.CpreQ.card_hashOutput_eq
  have hl : (xmssEnc.limit : ℝ) = 2 ^ 32 := by
    norm_num [xmssEnc, randomizerAttemptLimit]
  rw [hN, hl]
  norm_num

/-- **The constant of an answer's cost at leanXMSS, codeword partners only**:
`c₀ ≤ (2^33 + 1) / 2^128`. -/
theorem c0C_xmssEnc_le :
    Qrom.EncSalt.Code.c0C xmssEnc (2 ^ 128) ≤ (2 ^ 33 + 1) / 2 ^ 128 := by
  unfold Qrom.EncSalt.Code.c0C
  have hN : (Fintype.card HashOutput : ℝ) = 2 ^ 256 := by
    exact_mod_cast Qrom.CpreQ.card_hashOutput_eq
  have hl : (xmssEnc.limit : ℝ) = 2 ^ 32 := by
    norm_num [xmssEnc, randomizerAttemptLimit]
  rw [hN, hl]
  norm_num

/-- **The trial-read weight in closed form**: with `λ ≤ (2^34 + 1)/2^128`, `c₀ ≤ C/2^128` and
`m ≤ 2^32` requests, `λ (q + 2) + c₀ (2 m) ≤ ((2^34 + 1)(q + 2) + 2^33 C)/2^128`. -/
theorem tw_closed_le (q m : ℕ) (hm : m ≤ 2 ^ 32) {lam c₀ C : ℝ}
    (hlam : lam ≤ (2 ^ 34 + 1) / 2 ^ 128) (hlam₀ : 0 ≤ lam) (hc : c₀ ≤ C / 2 ^ 128)
    (hc₀ : 0 ≤ c₀) :
    ENNReal.ofReal lam * ((q + 2 : ℕ) : ℝ≥0∞) + ENNReal.ofReal c₀ * ((2 * m : ℕ) : ℝ≥0∞) ≤
      ENNReal.ofReal (((2 ^ 34 + 1) * (q + 2) + 2 ^ 33 * C) / 2 ^ 128) := by
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_natCast,
    ← ENNReal.ofReal_mul' (Nat.cast_nonneg _), ← ENNReal.ofReal_mul' (Nat.cast_nonneg _),
    ← ENNReal.ofReal_add (by positivity) (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  have hm' : ((2 * m : ℕ) : ℝ) ≤ 2 ^ 33 := by
    push_cast
    have : (m : ℝ) ≤ 2 ^ 32 := by exact_mod_cast hm
    linarith
  have hq : (0 : ℝ) ≤ ((q + 2 : ℕ) : ℝ) := Nat.cast_nonneg _
  have hC : 0 ≤ C / 2 ^ 128 := hc₀.trans hc
  calc lam * ((q + 2 : ℕ) : ℝ) + c₀ * ((2 * m : ℕ) : ℝ)
      ≤ (2 ^ 34 + 1) / 2 ^ 128 * ((q + 2 : ℕ) : ℝ) + C / 2 ^ 128 * 2 ^ 33 := by
        gcongr
    _ = ((2 ^ 34 + 1) * (q + 2) + 2 ^ 33 * C) / 2 ^ 128 := by
        push_cast
        ring

/-- **The graded EncTCR$ bound in closed form.** -/
theorem encSalt_closed_le (q : ℕ) {X : ℝ} (hX : 0 ≤ X) {TW : ℝ≥0∞}
    (hT : TW ≤ ENNReal.ofReal (X / 2 ^ 128)) :
    (((q : ℝ≥0∞) + 4) * ENNReal.ofReal (gradeEta HashOutput (2 ^ 128)) ^ (2⁻¹ : ℝ) +
        TW ^ (2⁻¹ : ℝ)) ^ 2 ≤
      ENNReal.ofReal ((2 * (3.001 * (q + 4)) ^ 2 + 2 * X) / 2 ^ 128) := by
  have hq : ((q : ℝ≥0∞) + 4) = ENNReal.ofReal ((q : ℝ) + 4) := by
    rw [ENNReal.ofReal_add (Nat.cast_nonneg _) (by norm_num), ENNReal.ofReal_natCast,
      ENNReal.ofReal_ofNat]
  have hT' : TW ^ (2⁻¹ : ℝ) ≤ ENNReal.ofReal √(X / 2 ^ 128) := by
    rw [← ofReal_rpow_inv_two _ (by positivity)]
    exact ENNReal.rpow_le_rpow hT (by norm_num)
  refine (pow_le_pow_left₀ zero_le (add_le_add le_rfl hT') 2).trans ?_
  rw [hq, ofReal_rpow_inv_two _ (gradeEta_nonneg _ _), ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_add (by positivity) (by positivity), ← ENNReal.ofReal_pow (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  set a := ((q : ℝ) + 4) * √(gradeEta HashOutput (2 ^ 128))
  set b := √(X / 2 ^ 128)
  have ha : a ≤ 3.001 * (q + 4) / 2 ^ 64 := by
    calc a ≤ ((q : ℝ) + 4) * (3.001 / 2 ^ 64) :=
          mul_le_mul_of_nonneg_left (sqrt_gradeEta_le.trans (by norm_num)) (by positivity)
      _ = 3.001 * (q + 4) / 2 ^ 64 := by ring
  have ha0 : 0 ≤ a := by positivity
  have hb : b ^ 2 = X / 2 ^ 128 := Real.sq_sqrt (by positivity)
  have ha2 : a ^ 2 ≤ (3.001 * (q + 4)) ^ 2 / 2 ^ 128 := by
    calc a ^ 2 ≤ (3.001 * (q + 4) / 2 ^ 64) ^ 2 := pow_le_pow_left₀ ha0 ha 2
      _ = (3.001 * (q + 4)) ^ 2 / 2 ^ 128 := by ring
  calc (a + b) ^ 2 ≤ 2 * a ^ 2 + 2 * b ^ 2 := by nlinarith [sq_nonneg (a - b)]
    _ ≤ 2 * ((3.001 * (q + 4)) ^ 2 / 2 ^ 128) + 2 * (X / 2 ^ 128) := by
        rw [hb]
        linarith
    _ = (2 * (3.001 * (q + 4)) ^ 2 + 2 * X) / 2 ^ 128 := by ring

/-- **The EncTCR$ term in closed form**, from the graded bound and the trial-read weight. -/
theorem encSalt_term_closed_le (q m : ℕ) (hm : m ≤ 2 ^ 32) {E TW : ℝ≥0∞} {lam c₀ C : ℝ}
    (hbud : E ≤ (((q : ℝ≥0∞) + 4) * ENNReal.ofReal (gradeEta HashOutput (2 ^ 128)) ^ (2⁻¹ : ℝ) +
      TW ^ (2⁻¹ : ℝ)) ^ 2)
    (hTW : TW ≤ ENNReal.ofReal lam * ((q + 2 : ℕ) : ℝ≥0∞) +
      ENNReal.ofReal c₀ * ((2 * m : ℕ) : ℝ≥0∞))
    (hlam : lam ≤ (2 ^ 34 + 1) / 2 ^ 128) (hlam₀ : 0 ≤ lam) (hc : c₀ ≤ C / 2 ^ 128)
    (hc₀ : 0 ≤ c₀) :
    E ≤ ENNReal.ofReal ((2 * (3.001 * (q + 4)) ^ 2 +
      2 * ((2 ^ 34 + 1) * (q + 2) + 2 ^ 33 * C)) / 2 ^ 128) := by
  have hC : 0 ≤ C := by
    have h := hc₀.trans hc
    rw [div_nonneg_iff, or_iff_left (by norm_num)] at h
    exact h.1
  exact hbud.trans (encSalt_closed_le q (by positivity)
    (hTW.trans (tw_closed_le q m hm hlam hlam₀ hc hc₀)))

/-- **EncTCR$ at leanXMSS B2 in the QROM, in closed form**: for an adversary of `q` hash calls
and `m ≤ 2^32` signing requests, B2 run on `refuse A` wins EncTCR$ with average probability at
most `(2 (3.001 (q + 4))² + (2^35 + 2)(q + 2) + 2^67 + 2^34) / 2^128`. -/
theorem probAvg_encTcrSalt_encRed_le_closed (A : Qrom.Xmss.Adversary) {q m : ℕ}
    (hq : ∀ pk, IFreeM.IsChargeBound (A pk) (Qrom.SufCma.cmdCharge Qrom.SufCma.hashCharge) q)
    (hm : ∀ pk, IFreeM.IsChargeBound (A pk) (Qrom.SufCma.cmdCharge Qrom.SufCma.signCharge) m)
    (hm32 : m ≤ 2 ^ 32) :
    romWorld.probAvg ((encTcrSalt romWorld xmssEnc).game
      (encRed romWorld (ofQrom (Qrom.Xmss.refuse A)))) ≤
      ENNReal.ofReal ((2 * (3.001 * (q + 4)) ^ 2 + (2 ^ 35 + 2) * (q + 2) + 2 ^ 67 + 2 ^ 34) /
        2 ^ 128) := by
  have h := encSalt_term_closed_le q m hm32 (probAvg_encTcrSalt_encRed_le_budget A hq)
    (totalWeight_encRed_le A hq hm (Qrom.EncSalt.Code.ansCode xmssEnc (2 ^ 128))
      (Qrom.EncSalt.Code.ansBound_ansCode xmssEnc_gSep xmssEnc_layout_injective
        xmssEnc_lengthLe (fun o ↦ by convert card_truncateHash_fiber_le_enc o using 3)
        xmssEnc_shift_injective
        xmssEnc_shift_distinct)
      (Qrom.EncSalt.lamS xmssEnc (2 ^ 128)) (Qrom.EncSalt.Code.c0C xmssEnc (2 ^ 128))
      (Qrom.EncSalt.lamS_nonneg xmssEnc _) (Qrom.EncSalt.Code.c0C_nonneg (e := xmssEnc) _)
      fun P qq s ↦ Qrom.EncSalt.Code.ansCode_le_cntY xmssEnc_layout_injective xmssEnc_lengthLe
        (2 ^ 128) P qq s)
    lamS_xmssEnc_le (Qrom.EncSalt.lamS_nonneg xmssEnc _) c0C_xmssEnc_le
    (Qrom.EncSalt.Code.c0C_nonneg (e := xmssEnc) _)
  refine h.trans (ENNReal.ofReal_le_ofReal (le_of_eq ?_))
  ring

/-- **leanXMSS in the QROM through its properties.** For an adversary of `q` hash calls and
`m ≤ 2^32` signing requests, `A` wins with probability at most the sum of the KIM-PRF (B1),
EncTCR$ (B2), CPRE (B3) and SM-TCR-C (B4) terms. -/
theorem leanXmss_qrom_security_props (A : Qrom.Xmss.Adversary) {q m : ℕ}
    (hq : ∀ pk, IFreeM.IsChargeBound (A pk) (Qrom.SufCma.cmdCharge Qrom.SufCma.hashCharge) q)
    (hm : ∀ pk, IFreeM.IsChargeBound (A pk) (Qrom.SufCma.cmdCharge Qrom.SufCma.signCharge) m)
    (hm32 : m ≤ 2 ^ 32) :
    Qrom.SufCma.winProb Qrom.Xmss.xmssRom A ≤
      ENNReal.ofReal ((2 * (3.001 * (q + 4)) ^ 2 + (2 ^ 35 + 2) * (q + 2) + 2 ^ 67 + 2 ^ 34) /
          2 ^ 128) +
        ENNReal.ofReal (((5.001 * q + 2650) ^ 2 + (3.001 * q + 883) ^ 2 + 6 * q + 2 ^ 68) /
          2 ^ 128) :=
  leanXmss_qrom_security_props_of_enc_closed A hq hm hm32
    (probAvg_encTcrSalt_encRed_le_closed A hq hm hm32)

/-- **leanXMSS in the QROM through its properties, as one fraction**: for `q` hash calls and
`m ≤ 2^32` signing requests, `winProb ≤ ((5.001 q + 2650)² + (3.001 q + 883)² +
2 (3.001 (q + 4))² + (2^35 + 2)(q + 2) + 6 q + 3 · 2^67 + 2^34) / 2^128`. -/
theorem leanXmss_qrom_security_props_closed (A : Qrom.Xmss.Adversary) {q m : ℕ}
    (hq : ∀ pk, IFreeM.IsChargeBound (A pk) (Qrom.SufCma.cmdCharge Qrom.SufCma.hashCharge) q)
    (hm : ∀ pk, IFreeM.IsChargeBound (A pk) (Qrom.SufCma.cmdCharge Qrom.SufCma.signCharge) m)
    (hm32 : m ≤ 2 ^ 32) :
    Qrom.SufCma.winProb Qrom.Xmss.xmssRom A ≤
      ENNReal.ofReal (((5.001 * q + 2650) ^ 2 + (3.001 * q + 883) ^ 2 +
        2 * (3.001 * (q + 4)) ^ 2 + (2 ^ 35 + 2) * (q + 2) + 6 * q + 3 * 2 ^ 67 + 2 ^ 34) /
          2 ^ 128) := by
  refine (leanXmss_qrom_security_props A hq hm hm32).trans (le_of_eq ?_)
  rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
  congr 1
  ring

end Quantum.StdModel.Xmss

end
