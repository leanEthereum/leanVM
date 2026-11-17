module

public import Quantum.Sphincs.Assembly.Depth.Chain
public import Quantum.Sphincs.Assembly.Depth.EventGame
public import Quantum.Sphincs.Assembly.Depth.MassGame

@[expose] public section

/-!
# leanSPHINCS against a parallel adversary, given the classical cap

A parallel adversary `Ap` (`Quantum.SufCma.AdversaryPar`) of total width `q`, at most `d` rounds
and `signatureLimit` signing requests is run as its serialization `serialize Ap`, on which every
sequential lemma of the leanSPHINCS chain holds with `q` permutation calls. Only the event bound
and the hybrid use the rounds, through the parallel canonical game `gameRPar Ap pol p v` (Sim:
lockstep rounds of `h`, `k`, `k'`, the same runs, weights and masses as the serialized game):

* **the event** (EventGame's `ewR_le_depth_of_par`, Sim's `eventWeight_prefixRPar_eq`,
  `twPR_eq_par` and the round charges): `√ewR ≤ advTermSD v q d + verTerm v q +
  √(twPR + verLin v q)`, the `h` rounds charged by depth at the rate `epsHS v = 2^-128 +
  2^16 price S★(v)` (Struct/Enc and the coverage Half event), the `k`, `k'` calls sequentially at
  the capacity rate; linearized in the coverage rate `covRate v` (`ewR_le_lin_par`);
* **the hybrid** (Depth/Hybrid's `uavg_p1R_leD_of_par` at `gameRPar Ap msgPol`, the masses by
  MassGame's `totalWeight_parSpongeMassR_gameRPar_eq` and Sim's `readMass_gameRPar_eq`):
  `√(4 · 10 min d q · 6q kappaSph) + √readCapS`.

Given the averaged classical cost `C` of the serialized adversary's prefix on the good event-side
data, `winProbPar Ap ≤ (√(eventTermSphG (advAD q d) (advBD q d) C (verLinSD q)) + hybTermSD q d
kappaSph readCapS)² + stageCap` (`winProbPar_le_of_cls`).
-/

open IPFunctor
open scoped ENNReal

open Quantum QuantumRuntime Quantum.Sponge Quantum.Par Sphincs Common Common.SufCma
open Quantum.SufCma (serialize isChargeBound_toSeq_perm isChargeBound_toSeq_sign winProbPar
  cmdChargePar signChargePar)
open HashSig (PublicParameter)
open Quantum.Xmss (X Z keccakStateEquiv)
open Quantum.Xmss.Hybrid (uavg)
open Quantum.Xmss.Assembly (runtimeR keepCost portR pow_two_rpow_inv_two)

namespace Quantum.Sphincs.Assembly

/-- **The price-free adversary amplitude at depth `d`**: the `h` rounds at `2^-128`, the capacity
residual and the verification's reads. -/
noncomputable def advAD (q d : ℕ) : ℝ≥0∞ :=
  (6 * (2 ^ 128 : ℝ≥0∞)⁻¹ * ((2 * min d q : ℕ) : ℝ≥0∞) * ((2 * q : ℕ) : ℝ≥0∞)) ^ (2⁻¹ : ℝ) +
    capTermSD q + ((3 * verifyBlocks : ℕ) : ℝ≥0∞) * freshKD q ^ (2⁻¹ : ℝ)

/-! ## The event bound linearized in the coverage rate -/

section linear

/-- **The `h` rate of the event's cells** is `2^-128` plus the coverage rate. -/
theorem epsHS_eq (v : (s : HPos) → XD s) : epsHS v = (2 ^ 128)⁻¹ + covRate v :=
  freshRate_h_eq (coverOf v)

/-- **The verification's fresh rate** is `freshKD q` plus the coverage rate. -/
theorem verEps_le_D (v : (s : HPos) → XD s) (q : ℕ) : verEps v q ≤ freshKD q + covRate v :=
  verEps_le v q

/-- **`advTermSD + verTerm` linearized in the coverage rate**:
`advTermSD v q d + verTerm v q ≤ advAD q d + √(advBD q d² covRate v)`. -/
theorem advTermSD_add_verTerm_le (v : (s : HPos) → XD s) (q d : ℕ) :
    advTermSD v q d + verTerm v q ≤ advAD q d + (advBD q d ^ 2 * covRate v) ^ (2⁻¹ : ℝ) := by
  have hh : (0 : ℝ) ≤ 2⁻¹ := by norm_num
  have hh1 : (2⁻¹ : ℝ) ≤ 1 := by norm_num
  set D : ℝ≥0∞ := ((2 * min d q : ℕ) : ℝ≥0∞)
  set Q : ℝ≥0∞ := ((2 * q : ℕ) : ℝ≥0∞)
  set V : ℝ≥0∞ := ((3 * verifyBlocks : ℕ) : ℝ≥0∞)
  set c := covRate v
  have h1 : (6 * epsHS v * D * Q) ^ (2⁻¹ : ℝ) ≤
      (6 * (2 ^ 128 : ℝ≥0∞)⁻¹ * D * Q) ^ (2⁻¹ : ℝ) +
        (6 * D * Q) ^ (2⁻¹ : ℝ) * c ^ (2⁻¹ : ℝ) := by
    rw [epsHS_eq, ← ENNReal.mul_rpow_of_nonneg _ _ hh]
    refine (ENNReal.rpow_le_rpow (le_of_eq (by ring)) hh).trans
      (ENNReal.rpow_add_le_add_rpow _ _ hh hh1)
  have h2 : verTerm v q ≤ V * (freshKD q ^ (2⁻¹ : ℝ) + c ^ (2⁻¹ : ℝ)) := by
    unfold verTerm
    exact mul_le_mul_of_nonneg_left ((ENNReal.rpow_le_rpow (verEps_le_D v q) hh).trans
      (ENNReal.rpow_add_le_add_rpow _ _ hh hh1)) zero_le
  have e : (advBD q d ^ 2 * c) ^ (2⁻¹ : ℝ) =
      ((6 * D * Q) ^ (2⁻¹ : ℝ) + V) * c ^ (2⁻¹ : ℝ) := by
    rw [ENNReal.mul_rpow_of_nonneg _ _ hh, pow_two_rpow_inv_two]
    rfl
  rw [e]
  unfold advTermSD advAD
  calc (6 * epsHS v * D * Q) ^ (2⁻¹ : ℝ) + capTermSD q + verTerm v q
      ≤ ((6 * (2 ^ 128 : ℝ≥0∞)⁻¹ * D * Q) ^ (2⁻¹ : ℝ) +
          (6 * D * Q) ^ (2⁻¹ : ℝ) * c ^ (2⁻¹ : ℝ)) + capTermSD q +
          V * (freshKD q ^ (2⁻¹ : ℝ) + c ^ (2⁻¹ : ℝ)) := add_le_add (add_le_add h1 le_rfl) h2
    _ = _ := by ring

/-- **`verLin` linearized in the coverage rate**: `verLin v q ≤ verLinSD q + 3 verifyBlocks ·
covRate v`. -/
theorem verLin_le_D (v : (s : HPos) → XD s) (q : ℕ) :
    verLin v q ≤ verLinSD q + ((3 * verifyBlocks : ℕ) : ℝ≥0∞) * covRate v := by
  unfold verLin verLinSD
  rw [← mul_add, ← keepCost_add]
  exact mul_le_mul_of_nonneg_left (keepCost_mono (verEps_le_D v q)) zero_le

end linear

/-! ## The event bound of the serialized adversary -/

section event

attribute [local instance] badDecES

variable (Ap : SAdversaryPar) {q d : ℕ}
  (hq : ∀ pk, IFreeM.IsChargeBound (Ap pk) (cmdChargePar Quantum.SufCma.widthCharge) q)
  (hd : ∀ pk, IFreeM.IsChargeBound (Ap pk) (cmdChargePar Quantum.SufCma.roundCharge) d)
  (hs : ∀ pk, IFreeM.IsChargeBound (Ap pk) (cmdChargePar signChargePar) signatureLimit)
include hq hd hs

set_option synthInstance.maxSize 2000 in
/-- **The depth-aware event bound of the serialized adversary, linearized in the coverage rate**
(EventGame's `ewR_le_depth_of_par` at Sim's `prefixRPar Ap pol p v`, then
`advTermSD_add_verTerm_le`, `verLin_le_D`): at `PermGood π 18`,
`ewR ≤ (advAD q d + √(advBD q d² covRate v) + √(twPR + verLinSD q + 3 verifyBlocks covRate v))²`.
-/
theorem ewR_le_lin_par (pol : DigestPolicy) (p : Pub) (v : (s : HPos) → XD s)
    (hπ : PermGood p.perm 18) :
    ewR p v (gameR pol (serialize Ap) p v) ≤
      (advAD q d + (advBD q d ^ 2 * covRate v) ^ (2⁻¹ : ℝ) + (twPR pol (serialize Ap) p v +
        (verLinSD q + ((3 * verifyBlocks : ℕ) : ℝ≥0∞) * covRate v)) ^ (2⁻¹ : ℝ)) ^ 2 := by
  have h := ewR_le_depth_of_par (fun pk ↦ isChargeBound_toSeq_perm (hq pk))
    (fun pk ↦ isChargeBound_toSeq_sign (hs pk)) pol p v hπ (prefixRPar Ap pol p v)
    (le_of_eq (eventWeight_prefixRPar_eq Ap pol p v _ _))
    (le_of_eq (twPR_eq_par Ap pol p v).symm) (prefixRPar_hWidth Ap hq pol p v)
    (prefixRPar_hDepth Ap hq hd pol p v) (prefixRPar_capWidth Ap hq pol p v)
    (prefixRPar_cls Ap hs pol p v) (prefixRPar_mixed Ap pol p v)
  refine h.trans (pow_le_pow_left₀ zero_le (add_le_add (advTermSD_add_verTerm_le v q d)
    (ENNReal.rpow_le_rpow (add_le_add le_rfl (verLin_le_D v q)) (by norm_num))) 2)

end event

/-! ## The bound for a parallel adversary, given the classical cap -/

section final

attribute [local instance] badDecES

variable (Ap : SAdversaryPar) {q d : ℕ}
  (hq : ∀ pk, IFreeM.IsChargeBound (Ap pk) (cmdChargePar Quantum.SufCma.widthCharge) q)
  (hd : ∀ pk, IFreeM.IsChargeBound (Ap pk) (cmdChargePar Quantum.SufCma.roundCharge) d)
  (hs : ∀ pk, IFreeM.IsChargeBound (Ap pk) (cmdChargePar signChargePar) signatureLimit)
include hq hd hs

set_option synthInstance.maxSize 2000 in
/-- **The depth-aware bound for a parallel adversary, given the averaged classical cost `C` of
its serialization** (Chain's `winProb_le_depth_of` on the serialized adversary, with Sim's
parallel canonical game, the masses of MassGame and Sim and the linearized event bound
`ewR_le_lin_par`). -/
theorem winProbPar_le_of_cls {C : ℝ≥0∞}
    (hcls : ∀ (par : PublicParameter) (perm : Equiv.Perm (X × Z)) (hk : Z → X),
      PermGood perm 18 → uavg (fun θ : ((X → Z) × (X → Z)) × ((s : HPos) → XD s) ↦
        if GoodES par perm hk θ then twPR strPol (serialize Ap) (pubES par perm hk θ.1) θ.2
          else 0) ≤ C) :
    winProbPar RandomPermutationModel.sufCmaScheme keccakStateEquiv Ap ≤
      (eventTermSphG (advAD q d) (advBD q d) C (verLinSD q) ^ (2⁻¹ : ℝ) +
        hybTermSD q d kappaSph readCapS) ^ 2 + stageCap := by
  have hperm := fun pk ↦ isChargeBound_toSeq_perm (hq pk)
  have hsign := fun pk ↦ isChargeBound_toSeq_sign (hs pk)
  exact winProb_le_depth_of hperm hsign
    (fun t ↦ gameRPar Ap msgPol (pubOf (tabOf t)) (valueAt (tabOf t)))
    (fun t ↦ p1R_eq_par Ap fullHw (tabOf t))
    (fun t ↦ p2R_eq_par Ap msgPol (pubOf (tabOf t)) (valueAt (tabOf t)))
    (fun t ↦ spongeRounds_gameRPar Ap hq hd msgPol (pubOf (tabOf t)) (valueAt (tabOf t)))
    (fun t ↦ totalWeight_parSpongeMassR_gameRPar_eq _ _ _ Ap msgPol _ _)
    (fun t ↦ (readMass_gameRPar_eq Ap msgPol _ _ _ _ _).symm)
    (fun _ _ _ hπ θ _ ↦ ewR_le_lin_par Ap hq hd hs strPol _ θ.2 hπ) hcls

end final

end Quantum.Sphincs.Assembly

end
