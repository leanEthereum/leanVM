module

public import Quantum.Sphincs.Assembly.GoodTables
public import Quantum.Sphincs.Assembly.ChgRevBound

@[expose] public section

/-!
# The mismatch terms of leanSPHINCS's hybrid

The masses (MassSources' `chgRevAvg`) and the win (Masked's `winChgAvg`) pay the mismatch between
the game at a padded table and the game at the reparametrized data with the first-meeting record
mass of the charged coordinates `chgBK (fullE t)`, averaged over the good set. On data satisfying
ChgRevStatic's `ChgStatic` (a conjunct of GoodTables' `SphStatic`), ChgRevBound bounds its sum over
the coordinates; `fullE` is injective on the good set and the coordinates are as many as the
padded tables.

* `avg_revFirst_fullG_le`: the average over `FullG S` is at most `R (εK + cD)` times the trace,
  `R = 3 signatureLimit`, `εK = (3 |Message| + 2 |SkIdx|) / |Z|`, `cD = 254 / |Randomizer|²`.
* `chgRevAvg_le`, `uavg_winChg_le`: the two mismatch terms.
* `epsK_add_cD_le`: `εK + cD ≤ 2^-247`; `chgRevC_le`: `R (εK + cD) ≤ 2^-215`.
* `chgRevAvg_le_cap` (`≤ 2^-200`), `winChgAvg_le_cap` (`≤ 2^-90`) at `SphStatic`: Security's
  `hChg`, `hWin`.
-/

open Matrix IPFunctor
open scoped ENNReal ComplexOrder Kronecker

open Quantum.SufCma

open Quantum QuantumRuntime Quantum.Sponge Sphincs
open HashSig (Digest Message Randomizer)
open Quantum.Xmss (X Z)
open Quantum.Xmss.Hybrid (uavg diagMass revW)
open Quantum.Xmss.Assembly (recHwSpec runtimeR)

namespace Quantum.Sphincs.Assembly

/-! ## The averages -/

section avg

variable {A : SAdversary}
  (hsign : ∀ pk, IFreeM.IsChargeBound (A pk) (cmdCharge signCharge) signatureLimit)
include hsign

open scoped Classical in
/-- **The first-meeting record mass of the charged coordinates, averaged over the good set**
`FullG S` of a static condition implying `ChgStatic`: at most `R (εK + cD)` times the trace. -/
theorem avg_revFirst_fullG_le (S : PP → ((s : HPos) → XD s) → Prop)
    (hS : ∀ p v, S p v → ChgStatic (pubP p) (rootV v))
    (ρ : Matrix (QReg.of Unit × QReg.of (HwReg X Z (Finset HPos × Selections)))
      (QReg.of Unit × QReg.of (HwReg X Z (Finset HPos × Selections))) ℂ) (hρ : ρ.PosSemidef) :
    (Fintype.card FT : ℝ≥0∞)⁻¹ * ∑ t, (if FullG S t then
        revFirst m0R LocalSig.Interp.instruments (chgBK (fullE t))
          (gameR msgPol A (pubP (fullE t).1) (fullE t).2.1) ρ else 0) ≤
      (3 * signatureLimit : ℕ) * (epsK + cD) * ENNReal.ofReal ρ.trace.re :=
  @avg_le_of_injOn_coords FT PP ((s : HPos) → XD s) KK instFintypeFT instFintypePP
    instFintypeHidVals instFintypeKK fullE (FullG S) _ (fullE_spec S A).1 card_coords_le
    (fun t ↦ revFirst m0R LocalSig.Interp.instruments (chgBK (fullE t))
      (gameR msgPol A (pubP (fullE t).1) (fullE t).2.1) ρ)
    (fun p v k ↦ revW m0R LocalSig.Interp.instruments (kPartK (p, (v, k)))
        (gameR msgPol A (pubP p) v) ρ +
      (runtimeR m0R).totalWeight LocalSig.Interp.instruments
        (fun i ↦ diagMass (dCSet p v i)) (gameR msgPol A (pubP p) v) ρ)
    (fun t ht ↦ revFirst_chgBK_le (fullE t) (hS _ _ ht.2.2) _ hρ) _
    (fun p ↦ sum_sum_revFirst_parts_le hsign ρ hρ p)

/-- **The masses' mismatch term**: `chgRevAvg A ρ S ≤ R (εK + cD)` times the trace, for a static
condition `S` implying `ChgStatic`. -/
theorem chgRevAvg_le (S : PP → ((s : HPos) → XD s) → Prop)
    (hS : ∀ p v, S p v → ChgStatic (pubP p) (rootV v))
    (ρ : Matrix (QReg.of Unit × QReg.of (HwReg X Z (Mem HPos)))
      (QReg.of Unit × QReg.of (HwReg X Z (Mem HPos))) ℂ) (hρ : ρ.PosSemidef) :
    chgRevAvg A ρ S ≤ (3 * signatureLimit : ℕ) * (epsK + cD) * ENNReal.ofReal ρ.trace.re :=
  avg_revFirst_fullG_le hsign (SrcS S) (fun p v h ↦ hS p v h.2) ρ hρ

/-- **The win's mismatch term**: `winChgAvg A S ≤ R (εK + cD)` times the initial trace, for a static
condition `S` implying `ChgStatic`. -/
theorem uavg_winChg_le (S : PP → ((s : HPos) → XD s) → Prop)
    (hS : ∀ p v, S p v → ChgStatic (pubP p) (rootV v)) :
    winChgAvg A S ≤ (3 * signatureLimit : ℕ) * (epsK + cD) * ENNReal.ofReal initR.trace.re :=
  avg_revFirst_fullG_le hsign S hS initR initR_posSemidef

end avg

/-! ## The constants -/

section consts

set_option exponentiation.threshold 1024 in
/-- The never-revealed part's rate at given counts (over abstract counts: the kernel never
evaluates a concrete cardinality). -/
theorem epsK_form_le (m s z : ℕ) (hm : m = 2 ^ 256) (hs : s ≤ 2 ^ 44) (hz : z = 2 ^ 512) :
    (3 * (m : ℝ≥0∞) + 2 * s) * (z : ℝ≥0∞)⁻¹ ≤ ENNReal.ofReal (1 / 2 ^ 254) := by
  subst hm hz
  calc (3 * ((2 ^ 256 : ℕ) : ℝ≥0∞) + 2 * s) * ((2 ^ 512 : ℕ) : ℝ≥0∞)⁻¹
      = ((3 * 2 ^ 256 + 2 * s : ℕ) : ℝ≥0∞) / ((2 ^ 512 : ℕ) : ℝ≥0∞) := by
        rw [ENNReal.div_eq_inv_mul, mul_comm, Nat.cast_add, Nat.cast_mul, Nat.cast_mul,
          Nat.cast_ofNat, Nat.cast_ofNat]
    _ ≤ ENNReal.ofReal (1 / 2 ^ 254) :=
        natCast_div_le_ofReal (by positivity) (Nat.add_le_add_left (Nat.mul_le_mul_left 2 hs) _)
          (by norm_num)

set_option exponentiation.threshold 1024 in
/-- The hidden randomizers' rate at a given count (over an abstract count). -/
theorem cD_form_le (r : ℕ) (hr : r = 2 ^ 128) :
    ((2 * 127 : ℕ) : ℝ≥0∞) * ((r : ℝ≥0∞) * r)⁻¹ ≤ ENNReal.ofReal (1 / 2 ^ 248) := by
  subst hr
  rw [← Nat.cast_mul, ← div_eq_mul_inv]
  exact natCast_div_le_ofReal (by positivity) le_rfl (by norm_num)

/-- **The charge rates** at Keccak's sizes: `εK + cD ≤ 2^-254 + 2^-248 ≤ 2^-247`. -/
theorem epsK_add_cD_le : epsK + cD ≤ ENNReal.ofReal (1 / 2 ^ 247) := by
  refine (add_le_add (epsK_form_le _ _ _ Hybrid.card_message Hybrid.card_skIdx_le
    Quantum.Xmss.Hybrid.R0.card_cap) (cD_form_le _ card_digest_eq)).trans ?_
  rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
  exact ENNReal.ofReal_le_ofReal (by norm_num)

/-- **The mismatch constant** `R (εK + cD) ≤ 2^-215`. -/
theorem chgRevC_le :
    ((3 * signatureLimit : ℕ) : ℝ≥0∞) * (epsK + cD) ≤ ENNReal.ofReal (1 / 2 ^ 215) := by
  refine (mul_le_mul' le_rfl epsK_add_cD_le).trans ?_
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
  exact ENNReal.ofReal_le_ofReal (by norm_num [signatureLimit])

/-- The mismatch constant times the initial trace. -/
theorem chgRevC_mul_initR_le :
    ((3 * signatureLimit : ℕ) : ℝ≥0∞) * (epsK + cD) * ENNReal.ofReal initR.trace.re ≤
      ENNReal.ofReal (1 / 2 ^ 215) :=
  (mul_le_mul' chgRevC_le ofReal_trace_initR_le_one).trans_eq (mul_one _)

end consts

/-! ## The caps -/

/-- **Security's `hChg`**: the masses' mismatch term at `SphStatic` is at most `2^-200`. -/
theorem chgRevAvg_le_cap (A : SAdversary)
    (hsign : ∀ pk, IFreeM.IsChargeBound (A pk) (cmdCharge signCharge) signatureLimit) :
    chgRevAvg A initR SphStatic ≤ ENNReal.ofReal (1 / 2 ^ 200) :=
  ((chgRevAvg_le hsign SphStatic (fun _ _ h ↦ h.2.2) initR initR_posSemidef).trans
    chgRevC_mul_initR_le).trans (ENNReal.ofReal_le_ofReal (by norm_num))

/-- **Security's `hWin`**: the win's mismatch term at `SrcS SphStatic` is at most `2^-90`. -/
theorem winChgAvg_le_cap (A : SAdversary)
    (hsign : ∀ pk, IFreeM.IsChargeBound (A pk) (cmdCharge signCharge) signatureLimit) :
    winChgAvg A (SrcS SphStatic) ≤ ENNReal.ofReal (1 / 2 ^ 90) :=
  ((uavg_winChg_le hsign (SrcS SphStatic) (fun _ _ h ↦ h.2.2.2)).trans
    chgRevC_mul_initR_le).trans (ENNReal.ofReal_le_ofReal (by norm_num))

end Quantum.Sphincs.Assembly

end
