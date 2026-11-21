module

public import Quantum.Sphincs.Assembly.Security

@[expose] public section

/-!
# leanSPHINCS's event side for a general event bound

EventSide's `uavg_p2R_le_es` and Masked's `uavg_p2R_msgPol_full_le` with the event bound and the
classical cap as hypotheses, for the depth-aware chain (whose event bound is the parallel one and
whose classical cap holds for every call count).

* **The win at good data** (`p2R_le_goodES_of`): WinDecomp's `endReads_wGame_trialHit` with any
  bound `B` on the end event weight `ewR`.
* **The event term** (`eventTermG a b C L`): for an event bound linear in `covRate v` under the
  roots, `ewR ≤ (a + √(b² covRate v) + √(twPR + L + 3 verifyBlocks covRate v))²` on the good data,
  and the averaged classical cost at most `C`: `(a + √(b² covPS) + √(C + L + 3 verifyBlocks
  covPS))²`, the verification's read error, the trial-hit mass `2^-189` and the conflict cap.
* **The averaged event side** (`uavg_p2R_le_esG`, at `msgPol`: `uavg_p2R_msgPol_le_esG`, over
  `FullES`: `uavg_p2R_msgPol_full_leG`).
-/

open Matrix IPFunctor
open scoped ENNReal Kronecker ComplexOrder

open Quantum.SufCma

open Quantum QuantumRuntime Quantum.Sponge Sphincs
open HashSig (PublicParameter)
open Quantum.Xmss (X Z)
open Quantum.Xmss.Hybrid (uavg uavg_mono uavg_add uavg_const_mul)
open Quantum.Xmss.Assembly (runtimeR uavg_const_le uavg_const)
open Quantum.Sphincs.Hybrid (uavg_le_one_of_le)

namespace Quantum.Sphincs.Assembly

/-- **The event term for an event bound linear in the coverage rate**: `(a + √(b² covPS) +
√(C + L + 3 verifyBlocks covPS))²`, the verification's read error, the trial-hit mass and the
conflict cap. -/
noncomputable def eventTermG (a b C L : ℝ≥0∞) : ℝ≥0∞ :=
  (a + (b ^ 2 * covPS) ^ (2⁻¹ : ℝ) +
    (C + (L + ((3 * verifyBlocks : ℕ) : ℝ≥0∞) * covPS)) ^ (2⁻¹ : ℝ)) ^ 2 +
    ENNReal.ofReal (readError X Z verifyBlocks verifyBlocks verifyBlocks) +
      ENNReal.ofReal (1 / 2 ^ 189) + ENNReal.ofReal (hConflictCap signatureLimit)

section proof

attribute [local instance] badDecES

variable {q : ℕ} {A : SAdversary}
  (hperm : ∀ pk, IFreeM.IsChargeBound (A pk) (cmdCharge permCharge) q)
  (hsign : ∀ pk, IFreeM.IsChargeBound (A pk) (cmdCharge signCharge) signatureLimit)
include hperm hsign

set_option synthInstance.maxSize 2000 in
/-- **The win at good data for any event bound** (WinDecomp's `endReads_wGame_trialHit`): with
disjoint honest paths, `HmsgSep` and `HmsgHSep`, `p2R strPol ≤ B + readError + trialHitMass +
hConflictMass` for every bound `B` on the end event weight. -/
theorem p2R_le_goodES_of (p : Pub) (v : (s : HPos) → XD s)
    (hpd : PathsDisjoint p.xw p.keys.1 (valsOf v)) (hsepK : HmsgSep p v)
    (hsepH : HmsgHSep p v) {B : ℝ≥0∞} (hev : ewR p v (gameR strPol A p v) ≤ B) :
    p2R strPol A p v ≤ B +
        ENNReal.ofReal (readError X Z verifyBlocks verifyBlocks verifyBlocks) +
          trialHitMass m0R A p v + hConflictMass m0R A p v := by
  have h := @endReads_wGame_trialHit m0R A p v (badRDec p v progCap) hpd hsepK hsepH
    (fun _ _ h ↦ Finset.notMem_empty _ h) rfl (progCalls_gameR hperm hsign strPol p v)
  exact h.trans (add_le_add (add_le_add (add_le_add hev le_rfl) le_rfl) le_rfl)

variable (par : PublicParameter) (perm : Equiv.Perm (X × Z)) (hk : Z → X)
  (hπ : PermGood perm 18)
include hπ

set_option synthInstance.maxSize 2000 in
/-- **The averaged event side for a general event bound**: if on the good data `GoodES` the end
event weight is at most `(a + √(b² covRate v) + √(twPR + L + 3 verifyBlocks covRate v))²` and the
averaged classical cost on `GoodES` is at most `C`, the averaged win probability of `p2R strPol`
is at most `eventTermG a b C L` plus twice the fraction off `GoodES`. -/
theorem uavg_p2R_le_esG {a b C L : ℝ≥0∞}
    (hev : ∀ θ : ((X → Z) × (X → Z)) × ((s : HPos) → XD s), GoodES par perm hk θ →
      ewR (pubES par perm hk θ.1) θ.2 (gameR strPol A (pubES par perm hk θ.1) θ.2) ≤
        (a + (b ^ 2 * covRate θ.2) ^ (2⁻¹ : ℝ) + (twPR strPol A (pubES par perm hk θ.1) θ.2 +
          (L + ((3 * verifyBlocks : ℕ) : ℝ≥0∞) * covRate θ.2)) ^ (2⁻¹ : ℝ)) ^ 2)
    (hcls : uavg (fun θ : ((X → Z) × (X → Z)) × ((s : HPos) → XD s) ↦
      if GoodES par perm hk θ then twPR strPol A (pubES par perm hk θ.1) θ.2 else 0) ≤ C) :
    uavg (fun θ : ((X → Z) × (X → Z)) × ((s : HPos) → XD s) ↦
      p2R strPol A (pubES par perm hk θ.1) θ.2) ≤
      eventTermG a b C L + 2 * uavg (fun θ ↦ if GoodES par perm hk θ then (0 : ℝ≥0∞) else 1) := by
  set G := GoodES par perm hk
  set twg : ((X → Z) × (X → Z)) × ((s : HPos) → XD s) → ℝ≥0∞ := fun θ ↦
    if G θ then twPR strPol A (pubES par perm hk θ.1) θ.2 else 0
  set hitg : ((X → Z) × (X → Z)) × ((s : HPos) → XD s) → ℝ≥0∞ := fun θ ↦
    if G θ then trialHitMass m0R A (pubES par perm hk θ.1) θ.2 else 0
  set hcg : ((X → Z) × (X → Z)) × ((s : HPos) → XD s) → ℝ≥0∞ := fun θ ↦
    if G θ then hConflictMass m0R A (pubES par perm hk θ.1) θ.2 else 0
  set bad : ((X → Z) × (X → Z)) × ((s : HPos) → XD s) → ℝ≥0∞ := fun θ ↦ if G θ then 0 else 1
  set gg : ((X → Z) × (X → Z)) × ((s : HPos) → XD s) → ℝ≥0∞ := fun θ ↦ b ^ 2 * covRate θ.2
  set ff : ((X → Z) × (X → Z)) × ((s : HPos) → XD s) → ℝ≥0∞ := fun θ ↦
    twg θ + (L + ((3 * verifyBlocks : ℕ) : ℝ≥0∞) * covRate θ.2)
  set rdT : ℝ≥0∞ := ENNReal.ofReal (readError X Z verifyBlocks verifyBlocks verifyBlocks)
  have hpt : ∀ θ, p2R strPol A (pubES par perm hk θ.1) θ.2 ≤
      (a + gg θ ^ (2⁻¹ : ℝ) + ff θ ^ (2⁻¹ : ℝ)) ^ 2 + rdT + hitg θ + hcg θ + bad θ := by
    intro θ
    by_cases hg : G θ
    · simp only [twg, hitg, hcg, bad, ff, gg, ite_eq_left hg, add_zero]
      exact p2R_le_goodES_of hperm hsign _ θ.2 hg.disj hg.sep hg.hsep (hev θ hg)
    · simp only [bad, ite_eq_right hg]
      exact (QuantumRuntime.outcomeLawWith_le_one _ _ _ _ _ _).trans le_add_self
  have hJ := uavg_sq_add_sqrt_add_sqrt_le a gg ff
  have hgg : uavg gg ≤ b ^ 2 * covPS := by
    simp only [gg]
    rw [uavg_const_mul]
    exact mul_le_mul_of_nonneg_left uavg_covRate_le zero_le
  have hff : uavg ff ≤ C + (L + ((3 * verifyBlocks : ℕ) : ℝ≥0∞) * covPS) := by
    simp only [ff]
    rw [uavg_add, uavg_add, uavg_const, uavg_const_mul]
    exact add_le_add hcls (add_le_add le_rfl (mul_le_mul_of_nonneg_left uavg_covRate_le zero_le))
  have hhit : uavg hitg ≤ ENNReal.ofReal (1 / 2 ^ 189) := by
    refine (uavg_mono fun θ ↦ ?_).trans (uavg_const_le (ENNReal.ofReal (1 / 2 ^ 189)))
    by_cases hg : G θ
    · simp only [hitg, ite_eq_left hg]
      exact trialHitMassAt_le_keccak strPol m0R A hg.off hπ
    · simp only [hitg, ite_eq_right hg]
      exact zero_le
  have hhc : uavg hcg ≤ ENNReal.ofReal (hConflictCap signatureLimit) + uavg bad :=
    uavg_hConflict_goodES hsign par perm hk
  calc uavg (fun θ : ((X → Z) × (X → Z)) × ((s : HPos) → XD s) ↦
        p2R strPol A (pubES par perm hk θ.1) θ.2)
      ≤ uavg (fun θ ↦ (a + gg θ ^ (2⁻¹ : ℝ) + ff θ ^ (2⁻¹ : ℝ)) ^ 2 + rdT + hitg θ +
          hcg θ + bad θ) := uavg_mono hpt
    _ = uavg (fun θ ↦ (a + gg θ ^ (2⁻¹ : ℝ) + ff θ ^ (2⁻¹ : ℝ)) ^ 2) + rdT + uavg hitg +
          uavg hcg + uavg bad := by
        rw [uavg_add, uavg_add, uavg_add, uavg_add, uavg_const]
    _ ≤ (a + (b ^ 2 * covPS) ^ (2⁻¹ : ℝ) + (C +
          (L + ((3 * verifyBlocks : ℕ) : ℝ≥0∞) * covPS)) ^ (2⁻¹ : ℝ)) ^ 2 + rdT +
          ENNReal.ofReal (1 / 2 ^ 189) +
          (ENNReal.ofReal (hConflictCap signatureLimit) + uavg bad) + uavg bad := by
        refine add_le_add (add_le_add (add_le_add (add_le_add (hJ.trans ?_) le_rfl) hhit) hhc)
          le_rfl
        exact pow_le_pow_left₀ zero_le (add_le_add (add_le_add le_rfl
          (ENNReal.rpow_le_rpow hgg (by norm_num))) (ENNReal.rpow_le_rpow hff (by norm_num))) 2
    _ = eventTermG a b C L + 2 * uavg bad := by
        unfold eventTermG
        ring

set_option synthInstance.maxSize 2000 in
/-- **The event side at `msgPol`** (Stream's `uavg_p2R_msgPol_eq_strPol` at every pair of keys,
then `uavg_p2R_le_esG`). -/
theorem uavg_p2R_msgPol_le_esG {a b C L : ℝ≥0∞}
    (hev : ∀ θ : ((X → Z) × (X → Z)) × ((s : HPos) → XD s), GoodES par perm hk θ →
      ewR (pubES par perm hk θ.1) θ.2 (gameR strPol A (pubES par perm hk θ.1) θ.2) ≤
        (a + (b ^ 2 * covRate θ.2) ^ (2⁻¹ : ℝ) + (twPR strPol A (pubES par perm hk θ.1) θ.2 +
          (L + ((3 * verifyBlocks : ℕ) : ℝ≥0∞) * covRate θ.2)) ^ (2⁻¹ : ℝ)) ^ 2)
    (hcls : uavg (fun θ : ((X → Z) × (X → Z)) × ((s : HPos) → XD s) ↦
      if GoodES par perm hk θ then twPR strPol A (pubES par perm hk θ.1) θ.2 else 0) ≤ C) :
    uavg (fun θ : ((X → Z) × (X → Z)) × ((s : HPos) → XD s) ↦
      p2R msgPol A (pubES par perm hk θ.1) θ.2) ≤
      eventTermG a b C L + 2 * uavg (fun θ ↦ if GoodES par perm hk θ then (0 : ℝ≥0∞) else 1) := by
  have e : ∀ kk : (X → Z) × (X → Z), uavg (p2R msgPol A (pubES par perm hk kk)) =
      uavg (p2R strPol A (pubES par perm hk kk)) := fun kk ↦ uavg_p2R_msgPol_eq_strPol A _
  have h := uavg_p2R_le_esG hperm hsign par perm hk hπ hev hcls
  rw [uavg_prod_iter] at h ⊢
  exact (congrArg uavg (funext e)).trans_le h

end proof

section full

attribute [local instance] badDecES

variable {q : ℕ} {A : SAdversary}
  (hperm : ∀ pk, IFreeM.IsChargeBound (A pk) (cmdCharge permCharge) q)
  (hsign : ∀ pk, IFreeM.IsChargeBound (A pk) (cmdCharge signCharge) signatureLimit)
include hperm hsign

set_option synthInstance.maxSize 2000 in
/-- **The event side over `FullES` at `msgPol` for a general event bound**
(`uavg_p2R_msgPol_le_esG` at every `(PK.seed, π, h)` with `PermGood π 18`, GoodES's
`uavg_not_goodES_le`): at most `eventTermG a b C L + 2 goodESCap + 2^-777`. -/
theorem uavg_p2R_msgPol_full_leG {a b C L : ℝ≥0∞}
    (hev : ∀ (par : PublicParameter) (perm : Equiv.Perm (X × Z)) (hk : Z → X),
      PermGood perm 18 → ∀ θ : ((X → Z) × (X → Z)) × ((s : HPos) → XD s),
      GoodES par perm hk θ →
      ewR (pubES par perm hk θ.1) θ.2 (gameR strPol A (pubES par perm hk θ.1) θ.2) ≤
        (a + (b ^ 2 * covRate θ.2) ^ (2⁻¹ : ℝ) + (twPR strPol A (pubES par perm hk θ.1) θ.2 +
          (L + ((3 * verifyBlocks : ℕ) : ℝ≥0∞) * covRate θ.2)) ^ (2⁻¹ : ℝ)) ^ 2)
    (hcls : ∀ (par : PublicParameter) (perm : Equiv.Perm (X × Z)) (hk : Z → X),
      PermGood perm 18 → uavg (fun θ : ((X → Z) × (X → Z)) × ((s : HPos) → XD s) ↦
        if GoodES par perm hk θ then twPR strPol A (pubES par perm hk θ.1) θ.2 else 0) ≤ C) :
    uavg (fun ω : FullES ↦ p2R msgPol A (pubES ω.1.1 ω.1.2.1 ω.1.2.2 ω.2.1) ω.2.2) ≤
      eventTermG a b C L + 2 * goodESCap + ENNReal.ofReal (1 / 2 ^ 777) := by
  rw [uavg_prod_iter]
  have hpt : ∀ x : PublicParameter × Equiv.Perm (X × Z) × (Z → X),
      uavg (fun θ : ((X → Z) × (X → Z)) × ((s : HPos) → XD s) ↦
        p2R msgPol A (pubES x.1 x.2.1 x.2.2 θ.1) θ.2) ≤
      eventTermG a b C L +
        2 * uavg (fun θ ↦ if GoodES x.1 x.2.1 x.2.2 θ then (0 : ℝ≥0∞) else 1) +
        (if PermGood x.2.1 18 then 0 else 1) := fun x ↦ by
    by_cases hπ : PermGood x.2.1 18
    · rw [ite_eq_left hπ, add_zero]
      exact uavg_p2R_msgPol_le_esG hperm hsign x.1 x.2.1 x.2.2 hπ
        (hev x.1 x.2.1 x.2.2 hπ) (hcls x.1 x.2.1 x.2.2 hπ)
    · rw [ite_eq_right hπ]
      refine le_trans ?_ le_add_self
      exact uavg_le_one_of_le fun θ ↦ p2R_le_one A msgPol _ _
  refine (uavg_mono hpt).trans ?_
  rw [uavg_add, uavg_add, uavg_const, uavg_const_mul]
  refine add_le_add (add_le_add le_rfl (mul_le_mul_of_nonneg_left ?_ zero_le))
    uavg_not_permGood_es
  exact (uavg_prod_iter (fun ω : FullES ↦
    if GoodES ω.1.1 ω.1.2.1 ω.1.2.2 ω.2 then (0 : ℝ≥0∞) else 1)).symm.trans_le uavg_not_goodES_le

end full

end Quantum.Sphincs.Assembly

end
