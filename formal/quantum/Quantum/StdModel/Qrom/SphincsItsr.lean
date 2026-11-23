module

public import Quantum.Qrom.Sphincs.BoundValue
public import Quantum.Cost.Qrom
public import Quantum.StdModel.Sphincs.ItsrHop
public import Quantum.StdModel.Qrom.SphincsItsrRt1
public import Quantum.StdModel.Qrom.SphincsItsrHyb
public import Quantum.StdModel.Qrom.SphincsItsrEndWin
public import Quantum.StdModel.Qrom.SphincsItsrEndEw

@[expose] public section

/-!
# ITSR of `H_msg` at leanSPHINCS's B3 in the QROM

B3's ITSR success (`itsrRed romWorld (ofQrom A)` against `Props.itsr romWorld itsrMap`), averaged
over the random oracle, bounded through the direct leanSPHINCS pipeline with the ITSR decision in
place of the verification (no SUF-CMA statement is used):

1. **Runtime 1** (`SphincsItsrRt1`, `probAvg_itsrRed_le_uavg`): the ideal game read through the
   ITSR decision is at most runtime 1, the non-secret cells of the table hardwired, running the
   ITSR template game `gameIQ msgPol` (`SphincsItsrGame`).
2. **The hybrid** (`SphincsItsrHyb`, `uavg_runtime1R_gameIQ_le`): runtime 1 against runtime 2 at
   the event side's policy, at the hidden masses `hybTermQ q`.
3. **The end** (`SphincsItsrEndWin`, `SphincsItsrEndEw`): an ITSR win of runtime 2 is a Cov hit of
   the forgery's digest cell against the stream cover `S★`, so its probability is at most the
   event weight at the end of the game plus the read error; the event weight is graded as for the
   SUF game, the two reads of the forgery's digest in place of the verification, with the
   prefix's averaged classical costs `clsBoundQ q` (`uavg_p2I_le`).

`itsrQromBound q = (√eventTermI q + hybTermQ q)²` (`probAvg_itsrRed_le`), in closed form
`((5.86 q + 2^33) / 2^64)²` for every `q` (`probAvg_itsrRed_le_closed`; the term `257.3 √q` of the
prefix's costs is at most `0.001 q + 2^24`).
-/

open IPFunctor
open scoped ENNReal
open HashSig hiding PublicKey
open Sphincs hiding HashDomain

namespace Quantum.StdModel.Sphincs.SphItsr

open Quantum QuantumRuntime Quantum.Xmss.Hybrid
open Quantum.Qrom.Sphincs
open Quantum.Xmss.Assembly (keepCost uavg_const)
open Quantum.Qrom.Xmss (rpow_inv_two_le_ofRealQ sq_add_rpow_inv_two_leQ inv_two_pow_eq_ofRealQ
  two_pow_le_card_hashDomain)

local notation "hashChargeQ" => Quantum.Qrom.SufCma.cmdCharge Quantum.Qrom.SufCma.hashCharge
local notation "signChargeQ" => Quantum.Qrom.SufCma.cmdCharge Quantum.Qrom.SufCma.signCharge

/-! ## The bound -/

/-- **The event term**: runtime 2's averaged ITSR win at the prefix's averaged costs. -/
noncomputable def eventTermI (q : ℕ) : ℝ≥0∞ :=
  (advBarQ q + verBarI + (clsBoundQ q + verLinBarI) ^ (2⁻¹ : ℝ)) ^ 2 + readErrI

/-- **The ITSR bound at B3**: `(√eventTermI q + hybTermQ q)²`. -/
noncomputable def itsrQromBound (q : ℕ) : ℝ≥0∞ :=
  (eventTermI q ^ (2⁻¹ : ℝ) + hybTermQ q) ^ 2

variable (A : SAdversary) {q : ℕ} (hhash : ∀ pk, IFreeM.IsChargeBound (A pk) hashChargeQ q)
  (hsign : ∀ pk, IFreeM.IsChargeBound (A pk) signChargeQ signatureLimit)
include hhash hsign

/-- **Runtime 2's averaged ITSR win.** -/
theorem uavg_p2I_le : uavg (p2I strPol A) ≤ eventTermI q := by
  refine (uavg_mono fun θ ↦ p2I_le_eventWeight A hsign θ).trans ?_
  rw [uavg_add, uavg_const]
  exact add_le_add (uavg_ewGameIQ_le A hhash hsign
    (uavg_twPQ_le starQ strPol noVal_strPol A hhash hsign)) le_rfl

/-- **ITSR of `H_msg` at B3 in the QROM**: at most `itsrQromBound q`. -/
theorem probAvg_itsrRed_le :
    romWorld.probAvg ((Props.itsr romWorld itsrMap).game (itsrRed romWorld (ofQrom A))) ≤
      itsrQromBound q :=
  (probAvg_itsrRed_le_uavg A).trans ((uavg_runtime1R_gameIQ_le A hhash hsign hwI covers_hwI).trans
    (pow_le_pow_left₀ zero_le (add_le_add (ENNReal.rpow_le_rpow (uavg_p2I_le A hhash hsign)
      (by norm_num)) le_rfl) 2))

omit hhash hsign

/-! ## The closed form -/

section closed

set_option exponentiation.threshold 1100

/-- **The averaged tail term**: `verBarI ≤ 3.15 · 2^-64`. -/
theorem verBarI_le : verBarI ≤ ENNReal.ofReal (3.15 / 2 ^ 64) := by
  refine rpow_inv_two_le_ofRealQ (r := 2 ^ 2 * (2.4726 / 2 ^ 128)) (by positivity) ?_
    (by norm_num)
  refine (mul_le_mul_of_nonneg_left epsBarQ_le zero_le).trans_eq ?_
  rw [← ENNReal.ofReal_ofNat, ← ENNReal.ofReal_pow (by norm_num),
    ← ENNReal.ofReal_mul (by positivity)]

/-- **The tail's averaged linear term**: `verLinBarI ≤ 6 · 2^-128`. -/
theorem verLinBarI_le : verLinBarI ≤ ENNReal.ofReal (6 / 2 ^ 128) := by
  have hY : (2 : ℝ≥0∞) / (Fintype.card (HashOutput × HashOutput) : ℝ≥0∞) ≤ (2 ^ 511)⁻¹ := by
    rw [card_pairOut]
    exact Quantum.Xmss.Assembly.two_div_natCast_le (by norm_num)
  have hD : (2 : ℝ≥0∞) / (Fintype.card Qrom.HashDomain : ℝ≥0∞) ≤ (2 ^ 135)⁻¹ :=
    Quantum.Xmss.Assembly.two_div_natCast_le
      ((by norm_num : 2 * 2 ^ 135 = 2 ^ 136).le.trans two_pow_le_card_hashDomain)
  unfold verLinBarI keepCost
  refine (mul_le_mul_of_nonneg_left (add_le_add (add_le_add epsBarQ_le hY) hD)
    zero_le).trans ?_
  simp (disch := positivity) only [← ENNReal.ofReal_ofNat,
    ← ENNReal.ofReal_pow, ← ENNReal.ofReal_inv_of_pos, ← ENNReal.ofReal_mul,
    ← ENNReal.ofReal_add]
  exact ENNReal.ofReal_le_ofReal (by norm_num)

/-- **The tail's read error**: `readErrI ≤ 2^-240`. -/
theorem readErrI_le : readErrI ≤ ENNReal.ofReal (1 / 2 ^ 240) := by
  unfold readErrI
  refine ENNReal.ofReal_le_ofReal ?_
  rw [Quantum.Sponge.readError, card_pairOut, Nat.cast_zero, add_zero, zero_div, add_zero]
  norm_num

/-- **The square-rooted event term**: for `q ≤ 2^64`, `√eventTermI q ≤ 3.852 q 2^-64 +
3.15 · 2^-64 + ((257.3 √q + 0.909 · 2^32) / 2^64 + 3 · 2^-64) + 2^-120`. -/
theorem eventTermI_rpow_le (hq : q ≤ 2 ^ 64) :
    eventTermI q ^ (2⁻¹ : ℝ) ≤ ENNReal.ofReal (3.852 * q / 2 ^ 64 + 3.15 / 2 ^ 64 +
      ((257.3 * √(q : ℝ) + 0.909 * 2 ^ 32) / 2 ^ 64 + 3 / 2 ^ 64) + 1 / 2 ^ 120) := by
  have hr := rpow_inv_two_le_ofRealQ (a := 1 / 2 ^ 120) (by positivity) readErrI_le
    (by norm_num)
  have hc := rpow_inv_two_le_ofRealQ (by positivity) (clsBoundQ_le hq) le_rfl
  have hv := rpow_inv_two_le_ofRealQ (a := 3 / 2 ^ 64) (by positivity) verLinBarI_le
    (by norm_num)
  have hcv : (clsBoundQ q + verLinBarI) ^ (2⁻¹ : ℝ) ≤
      ENNReal.ofReal ((257.3 * √(q : ℝ) + 0.909 * 2 ^ 32) / 2 ^ 64 + 3 / 2 ^ 64) := by
    rw [ENNReal.ofReal_add (by positivity) (by positivity)]
    exact (ENNReal.rpow_add_le_add_rpow _ _ (by norm_num) (by norm_num)).trans
      (add_le_add hc hv)
  unfold eventTermI
  refine (sq_add_rpow_inv_two_leQ _ _).trans ((add_le_add (add_le_add (add_le_add
    (advBarQ_le q) verBarI_le) hcv) hr).trans_eq ?_)
  rw [← ENNReal.ofReal_add (by positivity) (by positivity),
    ← ENNReal.ofReal_add (by positivity) (by positivity),
    ← ENNReal.ofReal_add (by positivity) (by positivity)]

/-- The arithmetic of the closed form: `257.3 √q ≤ 0.001 q + 2^24`. -/
theorem root_le_closedI (q : ℕ) :
    3.852 * q / 2 ^ 64 + 3.15 / 2 ^ 64 +
      ((257.3 * √(q : ℝ) + 0.909 * 2 ^ 32) / 2 ^ 64 + 3 / 2 ^ 64) + 1 / 2 ^ 120 +
        (2 * q / 2 ^ 64 + 0.9087 * 2 ^ 32 / 2 ^ 64) ≤
      (5.86 * q + 2 ^ 33) / 2 ^ 64 := by
  have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  have hs0 := Real.sqrt_nonneg (q : ℝ)
  have hsq : √(q : ℝ) ^ 2 = q := Real.sq_sqrt hq0
  have hamgm : 257.3 * √(q : ℝ) ≤ 0.001 * q + 2 ^ 24 := by
    nlinarith [sq_nonneg (√(q : ℝ) - 128650), hsq, hs0]
  have h : (2 : ℝ) ^ 64 / 2 ^ 120 ≤ 1 := by norm_num
  calc _ = (3.852 * q + 3.15 + (257.3 * √(q : ℝ) + 0.909 * 2 ^ 32 + 3) + 2 ^ 64 / 2 ^ 120 +
        (2 * q + 0.9087 * 2 ^ 32)) / 2 ^ 64 := by ring
    _ ≤ (5.86 * q + 2 ^ 33) / 2 ^ 64 := by
        refine div_le_div_of_nonneg_right ?_ (by positivity)
        norm_num at h hamgm ⊢
        linarith

/-- **The ITSR bound in closed form**: for `q ≤ 2^64`,
`itsrQromBound q ≤ ((5.86 q + 2^33) / 2^64)²`. -/
theorem itsrQromBound_le (hq : q ≤ 2 ^ 64) :
    itsrQromBound q ≤ ENNReal.ofReal (((5.86 * q + 2 ^ 33) / 2 ^ 64) ^ 2) := by
  have h1 := eventTermI_rpow_le hq
  have h2 := hybTermQ_le q
  rw [ENNReal.ofReal_pow (by positivity)]
  unfold itsrQromBound
  refine pow_le_pow_left₀ zero_le ((add_le_add h1 h2).trans ?_) 2
  rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
  exact ENNReal.ofReal_le_ofReal (root_le_closedI q)

end closed

/-- **ITSR of `H_msg` at leanSPHINCS's B3 in the QROM, in closed form**: for an adversary with at
most `q` hash calls and `signatureLimit` signing requests, B3 run on it wins ITSR with average
probability at most `((5.86 q + 2^33) / 2^64)²`. -/
theorem probAvg_itsrRed_le_closed (A : SAdversary) {q : ℕ}
    (hhash : ∀ pk, IFreeM.IsChargeBound (A pk) hashChargeQ q)
    (hsign : ∀ pk, IFreeM.IsChargeBound (A pk) signChargeQ signatureLimit) :
    romWorld.probAvg ((Props.itsr romWorld itsrMap).game (itsrRed romWorld (ofQrom A))) ≤
      ENNReal.ofReal (((5.86 * q + 2 ^ 33) / 2 ^ 64) ^ 2) := by
  by_cases hq : q ≤ 2 ^ 64
  · exact (probAvg_itsrRed_le A hhash hsign).trans (itsrQromBound_le hq)
  · refine (Quantum.Cost.sampledEvalDistMap_le_one _ _ _ _ _ _).trans ?_
    rw [← ENNReal.ofReal_one]
    refine ENNReal.ofReal_le_ofReal ?_
    have hq' : (2 : ℝ) ^ 64 ≤ q := by exact_mod_cast (Nat.lt_of_not_le hq).le
    have h1 : (1 : ℝ) ≤ (5.86 * q + 2 ^ 33) / 2 ^ 64 := by
      rw [le_div_iff₀ (by positivity)]
      linarith
    nlinarith

end Quantum.StdModel.Sphincs.SphItsr

end
