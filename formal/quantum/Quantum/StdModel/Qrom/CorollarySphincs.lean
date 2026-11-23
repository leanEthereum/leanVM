module

public import Quantum.StdModel.Qrom.SphincsEncCtr
public import Quantum.StdModel.Qrom.CorollaryXmss2

@[expose] public section

/-!
# leanSPHINCS in the QROM through its properties

Theorem 2 with SM-TCR-C and EncTCR+C restricted to the target tweaks
(`sphincs_suf_le_propsIn`) holds at every table of `romWorld`; the QROM winning probability is the
average over the tables (`SphInst.winProb_sphincsRom_le_avg`), so it is at most the averaged
property terms (`winProb_sphincsRom_le_of`). With the QROM bounds of the reductions:

* B1, KIM-PRF (`SphInst.leanSphincs_kimPrf_B1_qrom`), at most `(6 q + 2^68) / 2^128` for
  `m ≤ 2^31` signing requests (`kimTerm_le`);
* B2, PRF_msg (`SphInst.leanSphincs_prfMsg_B2_qrom`), at most `(4 q + 2^67) / 2^128`
  (`prfMsgTerm_le`);
* B3, ITSR, a hypothesis `I` here (`leanSphincs_qrom_security_props_of_itsr`);
* B4, EncTCR+C (`SphInst.probAvg_encTcrCtrIn_encRed_le_closed`), `((2.45 q + 21.01) / 2^64)²`;
* B5, CPRE (`SphInst.probAvg_cpreRed_le_closed`), `((5.001 q + 3645) / 2^64)²`;
* B6, SM-TCR-C (`Sphincs.probAvg_smTcrIn_tcrRed_le_closed`), `((3.001 (q + 11813)) / 2^64)²`;

as one fraction (`leanSphincs_qrom_security_props_of_itsr_closed`):
`winProb ≤ I + ((2.45 q + 21.01)² + (5.001 q + 3645)² + (3.001 q + 35451)² + 10 q + 2^68 + 2^67) /
2^128`.
-/

open IPFunctor OracleComp OracleSpec
open scoped ENNReal
open HashSig hiding PublicKey
open Sphincs hiding HashDomain

namespace Quantum.StdModel.Sphincs

open Quantum.StdModel Props
open Quantum.StdModel.Qrom.SphInst (romAvg)

/-- **The average over the tables of a success, as a real**, is the real of the probability over
a uniform table. -/
theorem romAvg_toReal_succAt {Q : Type} {R : OracleSpec.{0, 0} Q} {Pub Out : Type}
    (E : Experiment romWorld R Pub Out) (B : Adversary romWorld R Pub Out) :
    romAvg (fun H ↦ (E.succAt H B).toReal) = (romWorld.probAvg (E.game B)).toReal := by
  rw [Quantum.StdModel.Xmss.toReal_probAvg]
  simp only [romAvg, Experiment.succAt, ENNReal.toReal_inv, ENNReal.toReal_natCast]

/-- The relabelled adversary's hash calls. -/
theorem isChargeBound_ofQrom_hash_sph
    {A : Quantum.Qrom.SufCma.Adversary PublicKey Message (Option Signature) Forgery} {q : ℕ}
    (hq : ∀ pk, IFreeM.IsChargeBound (A pk)
      (Quantum.Qrom.SufCma.cmdCharge Quantum.Qrom.SufCma.hashCharge) q)
    (pk : PublicKey) : IFreeM.IsChargeBound (ofQrom A pk) (cmdCharge hashCharge) q :=
  isChargeBound_ofQrom A hashCharge pk (by rw [hashCharge_comp_qromPort]; exact hq pk)

/-- The relabelled adversary's signing requests. -/
theorem isChargeBound_ofQrom_call_sph
    {A : Quantum.Qrom.SufCma.Adversary PublicKey Message (Option Signature) Forgery} {m : ℕ}
    (hm : ∀ pk, IFreeM.IsChargeBound (A pk)
      (Quantum.Qrom.SufCma.cmdCharge Quantum.Qrom.SufCma.signCharge) m)
    (pk : PublicKey) : IFreeM.IsChargeBound (ofQrom A pk) (cmdCharge callCharge) m :=
  isChargeBound_ofQrom A callCharge pk (by rw [callCharge_comp_qromPort]; exact hm pk)

/-! ## The combination -/

/-- **The QROM win from the property bounds**: if the QROM successes of B3, B4, B5 and B6 against
`A` are at most `i`, `e`, `c` and `t`, then `A` wins with probability at most the KIM-PRF and
PRF_msg terms of B1 and B2 plus `i + e + c + t`. -/
theorem winProb_sphincsRom_le_of
    (A : Quantum.Qrom.SufCma.Adversary PublicKey Message (Option Signature) Forgery) {q m : ℕ}
    (hq : ∀ pk, IFreeM.IsChargeBound (A pk)
      (Quantum.Qrom.SufCma.cmdCharge Quantum.Qrom.SufCma.hashCharge) q)
    (hm : ∀ pk, IFreeM.IsChargeBound (A pk)
      (Quantum.Qrom.SufCma.cmdCharge Quantum.Qrom.SufCma.signCharge) m)
    {i e c t : ℝ≥0∞}
    (hi : romWorld.probAvg ((itsr romWorld itsrMap).game (itsrRed romWorld (ofQrom A))) ≤ i)
    (he : romWorld.probAvg ((encTcrCtrIn romWorld encCtr slotColl EncTwIn).game
      (encRed romWorld (ofQrom A))) ≤ e)
    (hc : romWorld.probAvg ((cpre romWorld cpreChains slotColl).game
      (cpreRed romWorld (ofQrom A))) ≤ c)
    (ht : romWorld.probAvg ((smTcrIn romWorld tcrColl slotColl TcrTwIn).game
      (tcrRed romWorld (ofQrom A))) ≤ t) :
    Quantum.Qrom.SufCma.winProb Quantum.Qrom.Sphincs.sphincsRom A ≤
      ENNReal.ofReal (4 * ((273410 + ((q + 12886291206 * m) + 879) : ℕ) : ℝ) *
          Real.sqrt (2 / 2 ^ 256)) +
        ENNReal.ofReal (4 * ((273410 + ((q + 12886291206 * m) + 879) : ℕ) : ℝ) *
          Real.sqrt (1 / 2 ^ 256)) + i + e + c + t := by
  have hq' := isChargeBound_ofQrom_hash_sph hq
  have hm' := isChargeBound_ofQrom_call_sph hm
  have h1 := (le_abs_self _).trans (Qrom.SphInst.leanSphincs_kimPrf_B1_qrom (ofQrom A) hq' hm')
  have h2 := (le_abs_self _).trans (Qrom.SphInst.leanSphincs_prfMsg_B2_qrom (ofQrom A) hq' hm')
  have hr := Qrom.SphInst.winProb_sphincsRom_le_avg A
  have he' : romAvg (fun H ↦
      (encTcrCtrSucc romWorld encCtr slotColl H (encRed romWorld (ofQrom A))).toReal) =
      (romWorld.probAvg ((encTcrCtrIn romWorld encCtr slotColl EncTwIn).game
        (encRed romWorld (ofQrom A)))).toReal := by
    rw [← romAvg_toReal_succAt]
    exact congrArg romAvg (funext fun H ↦ congrArg ENNReal.toReal
      (encTcrCtrSucc_encRed_eq romWorld H (ofQrom A) romWorld_coinsFair))
  have ht' : romAvg (fun H ↦
      (smTcrSucc romWorld tcrColl slotColl H (tcrRed romWorld (ofQrom A))).toReal) =
      (romWorld.probAvg ((smTcrIn romWorld tcrColl slotColl TcrTwIn).game
        (tcrRed romWorld (ofQrom A)))).toReal := by
    rw [← romAvg_toReal_succAt]
    exact congrArg romAvg (funext fun H ↦ congrArg ENNReal.toReal
      (smTcrSucc_tcrRed_eq romWorld H (ofQrom A) romWorld_coinsFair))
  rw [he', ht', romAvg_toReal_succAt, romAvg_toReal_succAt] at hr
  have hw : Quantum.Qrom.SufCma.winProb Quantum.Qrom.Sphincs.sphincsRom A ≠ ⊤ := by
    rw [winProb_qrom_eq_avg]
    exact ENNReal.sum_ne_top.mpr fun H _ ↦ ENNReal.mul_ne_top
      (Quantum.StdModel.Xmss.inv_card_tab_ne_top romWorld)
      (ne_top_of_le_ne_top ENNReal.one_ne_top (Qrom.SphInst.winProbAt_le_one _ _ H _))
  have hr' := hr.trans (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add h1 h2)
    le_rfl) le_rfl) le_rfl) le_rfl)
  rw [← ENNReal.ofReal_toReal hw]
  refine (ENNReal.ofReal_le_ofReal hr').trans ?_
  rw [ENNReal.ofReal_add (by positivity) ENNReal.toReal_nonneg,
    ENNReal.ofReal_add (by positivity) ENNReal.toReal_nonneg,
    ENNReal.ofReal_add (by positivity) ENNReal.toReal_nonneg,
    ENNReal.ofReal_add (by positivity) ENNReal.toReal_nonneg,
    ENNReal.ofReal_add (by positivity) (by positivity),
    ENNReal.ofReal_toReal (Quantum.StdModel.Xmss.probAvg_ne_top _ _),
    ENNReal.ofReal_toReal (Quantum.StdModel.Xmss.probAvg_ne_top _ _),
    ENNReal.ofReal_toReal (Quantum.StdModel.Xmss.probAvg_ne_top _ _),
    ENNReal.ofReal_toReal (Quantum.StdModel.Xmss.probAvg_ne_top _ _)]
  gcongr

/-! ## The KIM-PRF and PRF_msg terms in closed form -/

/-- **B1's term at most `2^31` requests**: `4 (q + 12886291206 m + 274289) √(2 / 2^256) ≤
(6 q + 2^68) / 2^128`. -/
theorem kimTerm_le (q : ℕ) {m : ℕ} (hm : m ≤ 2 ^ 31) :
    4 * ((273410 + ((q + 12886291206 * m) + 879) : ℕ) : ℝ) * Real.sqrt (2 / 2 ^ 256) ≤
      (6 * q + 2 ^ 68) / 2 ^ 128 := by
  have hs : Real.sqrt (2 / 2 ^ 256) ≤ 1.5 / 2 ^ 128 :=
    Real.sqrt_le_iff.2 ⟨by positivity, by norm_num⟩
  have hm' : (m : ℝ) ≤ 2 ^ 31 := by exact_mod_cast hm
  have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  push_cast
  calc 4 * (273410 + ((q : ℝ) + 12886291206 * m + 879)) * Real.sqrt (2 / 2 ^ 256)
      ≤ 4 * (273410 + ((q : ℝ) + 12886291206 * 2 ^ 31 + 879)) * (1.5 / 2 ^ 128) := by gcongr
    _ ≤ (6 * q + 2 ^ 68) / 2 ^ 128 := by
      rw [mul_div_assoc', div_le_div_iff_of_pos_right (by positivity)]
      norm_num
      linarith

/-- **B2's term at most `2^31` requests**: `4 (q + 12886291206 m + 274289) √(1 / 2^256) ≤
(4 q + 2^67) / 2^128`. -/
theorem prfMsgTerm_le (q : ℕ) {m : ℕ} (hm : m ≤ 2 ^ 31) :
    4 * ((273410 + ((q + 12886291206 * m) + 879) : ℕ) : ℝ) * Real.sqrt (1 / 2 ^ 256) ≤
      (4 * q + 2 ^ 67) / 2 ^ 128 := by
  have hs : Real.sqrt (1 / 2 ^ 256) ≤ 1 / 2 ^ 128 :=
    Real.sqrt_le_iff.2 ⟨by positivity, by norm_num⟩
  have hm' : (m : ℝ) ≤ 2 ^ 31 := by exact_mod_cast hm
  have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  push_cast
  calc 4 * (273410 + ((q : ℝ) + 12886291206 * m + 879)) * Real.sqrt (1 / 2 ^ 256)
      ≤ 4 * (273410 + ((q : ℝ) + 12886291206 * 2 ^ 31 + 879)) * (1 / 2 ^ 128) := by gcongr
    _ ≤ (4 * q + 2 ^ 67) / 2 ^ 128 := by
      rw [mul_div_assoc', div_le_div_iff_of_pos_right (by positivity)]
      norm_num
      linarith

/-! ## The leanSPHINCS corollary given B3 -/

/-- **leanSPHINCS in the QROM through its properties, given B3.** For an adversary of `q` hash
calls and `m ≤ 2^31` signing requests, if the QROM ITSR success of B3 is at most `I`, then `A`
wins with probability at most `(6 q + 2^68) / 2^128 + (4 q + 2^67) / 2^128 + I +
((2.45 q + 21.01) / 2^64)² + ((5.001 q + 3645) / 2^64)² + ((3.001 (q + 11813)) / 2^64)²`:
KIM-PRF (B1), PRF_msg (B2), ITSR (B3), EncTCR+C (B4), CPRE (B5) and SM-TCR-C (B6). -/
theorem leanSphincs_qrom_security_props_of_itsr
    (A : Quantum.Qrom.SufCma.Adversary PublicKey Message (Option Signature) Forgery) {q m : ℕ}
    (hq : ∀ pk, IFreeM.IsChargeBound (A pk)
      (Quantum.Qrom.SufCma.cmdCharge Quantum.Qrom.SufCma.hashCharge) q)
    (hm : ∀ pk, IFreeM.IsChargeBound (A pk)
      (Quantum.Qrom.SufCma.cmdCharge Quantum.Qrom.SufCma.signCharge) m)
    (hm31 : m ≤ 2 ^ 31) {I : ℝ≥0∞}
    (hItsr : romWorld.probAvg ((itsr romWorld itsrMap).game (itsrRed romWorld (ofQrom A))) ≤ I) :
    Quantum.Qrom.SufCma.winProb Quantum.Qrom.Sphincs.sphincsRom A ≤
      ENNReal.ofReal ((6 * q + 2 ^ 68) / 2 ^ 128) + ENNReal.ofReal ((4 * q + 2 ^ 67) / 2 ^ 128) +
        I + ENNReal.ofReal (((2.45 * q + 21.01) / 2 ^ 64) ^ 2) +
        ENNReal.ofReal (((5.001 * q + 3645) / 2 ^ 64) ^ 2) +
        ENNReal.ofReal ((3.001 * (q + 11813) / 2 ^ 64) ^ 2) := by
  have hq' := isChargeBound_ofQrom_hash_sph hq
  have hm' := isChargeBound_ofQrom_call_sph hm
  refine (winProb_sphincsRom_le_of A hq hm hItsr
    (Qrom.SphInst.probAvg_encTcrCtrIn_encRed_le_closed _ hq')
    (Qrom.SphInst.probAvg_cpreRed_le_closed _ hq' hm')
    (probAvg_smTcrIn_tcrRed_le_closed _ hq')).trans ?_
  gcongr
  · exact kimTerm_le q hm31
  · exact prfMsgTerm_le q hm31

/-- **The sum in closed form**: `I + ((2.45 q + 21.01)² + (5.001 q + 3645)² +
(3.001 q + 35451)² + 10 q + 2^68 + 2^67) / 2^128`. -/
theorem propsSumSph_le (q : ℕ) (I : ℝ≥0∞) :
    ENNReal.ofReal ((6 * q + 2 ^ 68) / 2 ^ 128) + ENNReal.ofReal ((4 * q + 2 ^ 67) / 2 ^ 128) +
        I + ENNReal.ofReal (((2.45 * q + 21.01) / 2 ^ 64) ^ 2) +
        ENNReal.ofReal (((5.001 * q + 3645) / 2 ^ 64) ^ 2) +
        ENNReal.ofReal ((3.001 * (q + 11813) / 2 ^ 64) ^ 2) ≤
      I + ENNReal.ofReal (((2.45 * q + 21.01) ^ 2 + (5.001 * q + 3645) ^ 2 +
        (3.001 * q + 35451) ^ 2 + 10 * q + 2 ^ 68 + 2 ^ 67) / 2 ^ 128) := by
  have hq : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  have h3 : (3.001 * ((q : ℝ) + 11813) / 2 ^ 64) ^ 2 ≤ (3.001 * q + 35451) ^ 2 / 2 ^ 128 := by
    rw [div_pow, show ((2 : ℝ) ^ 64) ^ 2 = 2 ^ 128 by norm_num]
    gcongr
    linarith
  have h4 : ((2.45 * (q : ℝ) + 21.01) / 2 ^ 64) ^ 2 = (2.45 * q + 21.01) ^ 2 / 2 ^ 128 := by
    rw [div_pow]
    norm_num
  have h5 : ((5.001 * (q : ℝ) + 3645) / 2 ^ 64) ^ 2 = (5.001 * q + 3645) ^ 2 / 2 ^ 128 := by
    rw [div_pow]
    norm_num
  calc ENNReal.ofReal ((6 * q + 2 ^ 68) / 2 ^ 128) + ENNReal.ofReal ((4 * q + 2 ^ 67) / 2 ^ 128) +
          I + ENNReal.ofReal (((2.45 * q + 21.01) / 2 ^ 64) ^ 2) +
          ENNReal.ofReal (((5.001 * q + 3645) / 2 ^ 64) ^ 2) +
          ENNReal.ofReal ((3.001 * (q + 11813) / 2 ^ 64) ^ 2)
      = I + (ENNReal.ofReal ((6 * q + 2 ^ 68) / 2 ^ 128) +
          ENNReal.ofReal ((4 * q + 2 ^ 67) / 2 ^ 128) +
          ENNReal.ofReal (((2.45 * q + 21.01) / 2 ^ 64) ^ 2) +
          ENNReal.ofReal (((5.001 * q + 3645) / 2 ^ 64) ^ 2) +
          ENNReal.ofReal ((3.001 * (q + 11813) / 2 ^ 64) ^ 2)) := by ring
    _ ≤ I + ENNReal.ofReal (((2.45 * q + 21.01) ^ 2 + (5.001 * q + 3645) ^ 2 +
          (3.001 * q + 35451) ^ 2 + 10 * q + 2 ^ 68 + 2 ^ 67) / 2 ^ 128) := by
        gcongr
        rw [← ENNReal.ofReal_add (by positivity) (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
        refine ENNReal.ofReal_le_ofReal ?_
        rw [h4, h5]
        calc (6 * (q : ℝ) + 2 ^ 68) / 2 ^ 128 + (4 * q + 2 ^ 67) / 2 ^ 128 +
              (2.45 * q + 21.01) ^ 2 / 2 ^ 128 + (5.001 * q + 3645) ^ 2 / 2 ^ 128 +
              (3.001 * (q + 11813) / 2 ^ 64) ^ 2
            ≤ (6 * (q : ℝ) + 2 ^ 68) / 2 ^ 128 + (4 * q + 2 ^ 67) / 2 ^ 128 +
              (2.45 * q + 21.01) ^ 2 / 2 ^ 128 + (5.001 * q + 3645) ^ 2 / 2 ^ 128 +
              (3.001 * q + 35451) ^ 2 / 2 ^ 128 := by gcongr
          _ = _ := by ring

/-- **leanSPHINCS in the QROM through its properties, given B3, as one fraction**: for `q` hash
calls and `m ≤ 2^31` signing requests, `winProb ≤ I + ((2.45 q + 21.01)² + (5.001 q + 3645)² +
(3.001 q + 35451)² + 10 q + 2^68 + 2^67) / 2^128`. -/
theorem leanSphincs_qrom_security_props_of_itsr_closed
    (A : Quantum.Qrom.SufCma.Adversary PublicKey Message (Option Signature) Forgery) {q m : ℕ}
    (hq : ∀ pk, IFreeM.IsChargeBound (A pk)
      (Quantum.Qrom.SufCma.cmdCharge Quantum.Qrom.SufCma.hashCharge) q)
    (hm : ∀ pk, IFreeM.IsChargeBound (A pk)
      (Quantum.Qrom.SufCma.cmdCharge Quantum.Qrom.SufCma.signCharge) m)
    (hm31 : m ≤ 2 ^ 31) {I : ℝ≥0∞}
    (hItsr : romWorld.probAvg ((itsr romWorld itsrMap).game (itsrRed romWorld (ofQrom A))) ≤ I) :
    Quantum.Qrom.SufCma.winProb Quantum.Qrom.Sphincs.sphincsRom A ≤
      I + ENNReal.ofReal (((2.45 * q + 21.01) ^ 2 + (5.001 * q + 3645) ^ 2 +
        (3.001 * q + 35451) ^ 2 + 10 * q + 2 ^ 68 + 2 ^ 67) / 2 ^ 128) :=
  (leanSphincs_qrom_security_props_of_itsr A hq hm hm31 hItsr).trans (propsSumSph_le q I)

/-- **The ITSR term in the same fraction**: `((a q + b) / 2^64)² = (a q + b)² / 2^128`. -/
theorem ofReal_sq_div_two_pow_64 (x : ℝ) :
    ENNReal.ofReal ((x / 2 ^ 64) ^ 2) = ENNReal.ofReal (x ^ 2 / 2 ^ 128) := by
  rw [div_pow]
  norm_num

/-- **leanSPHINCS in the QROM through its properties, given B3 in closed form**: if the QROM ITSR
success of B3 is at most `((a q + b) / 2^64)²`, then for `q` hash calls and `m ≤ 2^31` signing
requests, `winProb ≤ ((a q + b)² + (2.45 q + 21.01)² + (5.001 q + 3645)² + (3.001 q + 35451)² +
10 q + 2^68 + 2^67) / 2^128`. -/
theorem leanSphincs_qrom_security_props_of_itsr_value
    (A : Quantum.Qrom.SufCma.Adversary PublicKey Message (Option Signature) Forgery) {q m : ℕ}
    (hq : ∀ pk, IFreeM.IsChargeBound (A pk)
      (Quantum.Qrom.SufCma.cmdCharge Quantum.Qrom.SufCma.hashCharge) q)
    (hm : ∀ pk, IFreeM.IsChargeBound (A pk)
      (Quantum.Qrom.SufCma.cmdCharge Quantum.Qrom.SufCma.signCharge) m)
    (hm31 : m ≤ 2 ^ 31) {a b : ℝ}
    (hItsr : romWorld.probAvg ((itsr romWorld itsrMap).game (itsrRed romWorld (ofQrom A))) ≤
      ENNReal.ofReal (((a * q + b) / 2 ^ 64) ^ 2)) :
    Quantum.Qrom.SufCma.winProb Quantum.Qrom.Sphincs.sphincsRom A ≤
      ENNReal.ofReal (((a * q + b) ^ 2 + (2.45 * q + 21.01) ^ 2 + (5.001 * q + 3645) ^ 2 +
        (3.001 * q + 35451) ^ 2 + 10 * q + 2 ^ 68 + 2 ^ 67) / 2 ^ 128) := by
  refine (leanSphincs_qrom_security_props_of_itsr_closed A hq hm hm31 hItsr).trans
    (le_of_eq ?_)
  have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  rw [ofReal_sq_div_two_pow_64, ← ENNReal.ofReal_add (by positivity) (by positivity)]
  congr 1
  ring

end Quantum.StdModel.Sphincs

end
