module

public import Quantum.Sphincs.Assembly.Depth.EventSide
public import Quantum.Sphincs.Assembly.Depth.Hybrid

@[expose] public section

/-!
# leanSPHINCS's chain with a parallel hybrid and a general event bound

Security's `winProb_le_sphincsQrpmBound` (through Masked's `winProb_le_masked`) with the masked
hybrid on a parallel program family (Depth/Hybrid's `uavg_p1R_leD_of_par`, the masses by
`totalWeight` equalities with the sequential game's, then Masses' `hcov_sph`, HmsgCoversMass'
`hS_sph'`, `hRd_sph'`) and the event side for a general event bound (Depth/EventSide's
`uavg_p2R_msgPol_full_leG`): for an adversary `A` with at most `q` permutation calls and
`signatureLimit` signing requests,
`winProb A ≤ (√(eventTermG a b C L + 2 goodESCap + 2^-777 + winChgCap + stageCap) +
hybTermSD q d kappaSph readCapS)² + stageCap` (`winProb_le_depth_of`).
-/

open IPFunctor
open scoped ENNReal

open Quantum.SufCma

open Quantum QuantumRuntime Quantum.Sponge Quantum.Par Sphincs Common Common.SufCma
open HashSig (PublicParameter)
open Quantum.Xmss (X Z keccakStateEquiv)
open Quantum.Xmss.Hybrid (uavg uavg_mono parSpongeMassR readMass spongeMass)
open Quantum.Xmss.Assembly (runtimeR runtime1R recHwSpec recSpec extCls portR keepCost)

namespace Quantum.Sphincs.Assembly

/-- The verification's fresh rate without the coverage part, at `q` calls: `2^-128 + 2 capRate`
below `progCap + 6q + clsCap + 3 verifyBlocks + 1` entries. -/
noncomputable def freshKD (q : ℕ) : ℝ≥0∞ :=
  (2 ^ 128)⁻¹ + 2 * capRate (progCap + (6 * q + clsCap + 3 * verifyBlocks + 1)) 18

/-- **The factor of `√covRate` at depth `d`**: `√(24 min d q · q) + 3 verifyBlocks`. -/
noncomputable def advBD (q d : ℕ) : ℝ≥0∞ :=
  (6 * ((2 * min d q : ℕ) : ℝ≥0∞) * ((2 * q : ℕ) : ℝ≥0∞)) ^ (2⁻¹ : ℝ) +
    ((3 * verifyBlocks : ℕ) : ℝ≥0∞)

/-- The price-free part of `verLin` at `q` calls. -/
noncomputable def verLinSD (q : ℕ) : ℝ≥0∞ :=
  ((3 * verifyBlocks : ℕ) : ℝ≥0∞) * keepCost X Z (freshKD q)

/-- **The depth-aware chain's event term**: the event side's `eventTermG a b C L`, the bad data
`2 goodESCap + 2^-777`, the win's mismatch term and the bad fraction. -/
noncomputable def eventTermSphG (a b C L : ℝ≥0∞) : ℝ≥0∞ :=
  eventTermG a b C L + 2 * goodESCap + ENNReal.ofReal (1 / 2 ^ 777) + winChgCap + stageCap

section chain

attribute [local instance] badDecES

variable {q : ℕ} {A : SAdversary}
  (hperm : ∀ pk, IFreeM.IsChargeBound (A pk) (cmdCharge permCharge) q)
  (hsign : ∀ pk, IFreeM.IsChargeBound (A pk) (cmdCharge signCharge) signatureLimit)
include hperm hsign

open scoped Classical in
set_option synthInstance.maxSize 2000 in
/-- **leanSPHINCS's win probability with a parallel hybrid and a general event bound.** If
runtime 1 with the full table and runtime 2 run the canonical game at `msgPol` as the parallel
programs `xP t`, with at most `10 min d q` single sponge calls and rounds of positive width, and
the masses of `xP t` are the sequential game's, and if on the good event-side data the end event
weight is at most `(a + √(b² covRate v) + √(twPR + L + 3 verifyBlocks covRate v))²` and the
averaged classical cost at most `C`, then
`winProb A ≤ (√(eventTermSphG a b C L) + hybTermSD q d kappaSph readCapS)² + stageCap`. -/
theorem winProb_le_depth_of {d : ℕ}
    (xP : FT → QComp (parSpec (recHwSpec X Z HPos Selections) (portR X Z HPos Selections))
      (QReg.of Unit) (QReg.of Unit) Bool)
    (h1 : ∀ t, p1R A fullHw (tabOf t) = ((runtime1R X Z (fullHw (tabOf t)) m0R).par
      (portR X Z HPos Selections)).evalDistMap .instruments (xP t) (SubState.basis ()) winObs
        {true})
    (h2 : ∀ t, p2R msgPol A (pubOf (tabOf t)) (valueAt (tabOf t)) = ((runtimeR m0R).par
      (portR X Z HPos Selections)).evalDistMap .instruments (xP t) (SubState.basis ()) winObs
        {true})
    (hd : ∀ t, IFreeM.IsChargeBound (xP t) (portCharge (spongeRounds (portR X Z HPos Selections)
      (extCls X Z (Mem HPos) (recSpec HPos Selections)))) (10 * min d q))
    (hm : ∀ t, ((runtimeR m0R).par (portR X Z HPos Selections)).totalWeight .instruments
      (parSpongeMassR (fullCovH (tabOf t)) (fullCovK (tabOf t)) (fullCovK' (tabOf t))) (xP t)
        initR = (runtimeR m0R).totalWeight .instruments
      (spongeMass (fullCovH (tabOf t)) (fullCovK (tabOf t)) (fullCovK' (tabOf t)))
        (gameR msgPol A (pubOf (tabOf t)) (valueAt (tabOf t))) initR)
    (hr : ∀ t, ((runtimeR m0R).par (portR X Z HPos Selections)).totalWeight .instruments
      (parWeight (portR X Z HPos Selections)
        (readMass (fullCovH (tabOf t)) (fullCovK (tabOf t)) (fullCovK' (tabOf t)))) (xP t)
        initR = (runtimeR m0R).totalWeight .instruments
      (readMass (fullCovH (tabOf t)) (fullCovK (tabOf t)) (fullCovK' (tabOf t)))
        (gameR msgPol A (pubOf (tabOf t)) (valueAt (tabOf t))) initR)
    {a b C L : ℝ≥0∞}
    (hev : ∀ (par : PublicParameter) (perm : Equiv.Perm (X × Z)) (hk : Z → X),
      PermGood perm 18 → ∀ θ : ((X → Z) × (X → Z)) × ((s : HPos) → XD s),
      GoodES par perm hk θ →
      ewR (pubES par perm hk θ.1) θ.2 (gameR strPol A (pubES par perm hk θ.1) θ.2) ≤
        (a + (b ^ 2 * covRate θ.2) ^ (2⁻¹ : ℝ) + (twPR strPol A (pubES par perm hk θ.1) θ.2 +
          (L + ((3 * verifyBlocks : ℕ) : ℝ≥0∞) * covRate θ.2)) ^ (2⁻¹ : ℝ)) ^ 2)
    (hcls : ∀ (par : PublicParameter) (perm : Equiv.Perm (X × Z)) (hk : Z → X),
      PermGood perm 18 → uavg (fun θ : ((X → Z) × (X → Z)) × ((s : HPos) → XD s) ↦
        if GoodES par perm hk θ then twPR strPol A (pubES par perm hk θ.1) θ.2 else 0) ≤ C) :
    winProb RandomPermutationModel.sufCmaScheme keccakStateEquiv A ≤
      (eventTermSphG a b C L ^ (2⁻¹ : ℝ) + hybTermSD q d kappaSph readCapS) ^ 2 + stageCap := by
  have hS := hS_sph' A hperm hsign SphStatic fun _ _ h ↦ h.1
  have hRd := hRd_sph' A hperm hsign SphStatic (fun _ _ h ↦ h.1) fun _ _ h ↦ h.2.1
  have hc : chgRevAvg A initR SphStatic ≤ chgRevCap := chgRevAvg_le_cap A hsign
  have hμ : uavg (fun t : FT ↦ if FullG (SrcS SphStatic) t then ((runtimeR m0R).par
      (portR X Z HPos Selections)).totalWeight .instruments
        (parSpongeMassR (fullCovH (tabOf t)) (fullCovK (tabOf t)) (fullCovK' (tabOf t))) (xP t)
          initR else 0) ≤ ((6 * q : ℕ) : ℝ≥0∞) * kappaSph := by
    simp only [hm]
    refine hS.trans (mul_le_mul_of_nonneg_left ?_ zero_le)
    unfold kappaSph
    exact add_le_add le_rfl hc
  have hν : uavg (fun t : FT ↦ if FullG (SrcS SphStatic) t then ((runtimeR m0R).par
      (portR X Z HPos Selections)).totalWeight .instruments
        (parWeight (portR X Z HPos Selections)
          (readMass (fullCovH (tabOf t)) (fullCovK (tabOf t)) (fullCovK' (tabOf t)))) (xP t)
          initR else 0) ≤ readCapS := by
    simp only [hr]
    refine hRd.trans ?_
    unfold readCapS
    exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hc zero_le)
  have hhyb := uavg_p1R_leD_of_par (A := A) (SrcS SphStatic) xP h1 h2 hd
    (fun t ↦ fullCovH (tabOf t)) (fun t ↦ fullCovK (tabOf t)) (fun t ↦ fullCovK' (tabOf t))
    hcov_sph kappaSph readCapS hμ hν
  have hst := stageFrac_le_stageCap
  have hwc : winChgAvg A (SrcS SphStatic) ≤ winChgCap := winChgAvg_le_cap A hsign
  have hside : uavg (fun L ↦ p2R msgPol A (pubOf L) (valueAt L)) ≤ eventTermSphG a b C L := by
    refine (uavg_p2R_tab_le A (SrcS SphStatic)).trans ?_
    rw [uavg_pubP_eq_full]
    unfold eventTermSphG
    exact add_le_add (add_le_add (uavg_p2R_msgPol_full_leG hperm hsign hev hcls) hwc) hst
  rw [winProb_eq_uavg_p1R]
  exact hhyb.trans (add_le_add (pow_le_pow_left₀ zero_le (add_le_add
    (ENNReal.rpow_le_rpow hside (by norm_num)) le_rfl) 2) hst)

end chain

end Quantum.Sphincs.Assembly

end
