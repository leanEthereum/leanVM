module

public import Quantum.Sphincs.Assembly.Security
public import Quantum.Xmss.Assembly.Depth.Hybrid

@[expose] public section

/-!
# leanSPHINCS's masked hybrid with rounds of every sponge port

Masked's `uavg_p1R_le` for a parallel program: runtime 1 with the full table against runtime 2 on
a family `xP t` of programs over `parSpec (recHwSpec X Z HPos Selections) portR` (the parallel
canonical game at `msgPol` and the padded table `t`), averaged over the padded tables, the masses
masked by ReparamFull's good set `FullG S`. XPD's `uavg_win_runtime1R_portR_le_masked` with at
most `10 min d q` single sponge calls and rounds of positive width (`spongeRounds`): the hybrid
term `√(4 · 10 min d q · 6q κ) + √ν` (`hybTermSD`).
-/

open IPFunctor
open scoped ENNReal

open Quantum.SufCma

open Quantum QuantumRuntime Quantum.Sponge Quantum.Par Sphincs
open Quantum.Xmss (X Z)
open Quantum.Xmss.Hybrid (uavg Covers parSpongeMassR readMass
  uavg_win_runtime1R_portR_le_masked)
open Quantum.Xmss.Assembly (runtimeR runtime1R recHwSpec recSpec extCls portR)

namespace Quantum.Sphincs.Assembly

/-- **The depth-aware target of the masked hybrid**: `√(4 · 10 min d q · 6q κ) + √ν`, the
sponge-port mass `6q κ` over at most `10 min d q` rounds. -/
noncomputable def hybTermSD (q d : ℕ) (κ ν : ℝ≥0∞) : ℝ≥0∞ :=
  (4 * (((10 * min d q : ℕ) : ℝ≥0∞) * (((6 * q : ℕ) : ℝ≥0∞) * κ))) ^ (2⁻¹ : ℝ) + ν ^ (2⁻¹ : ℝ)

theorem hybTermSD_mono (q d : ℕ) {κ κ' ν ν' : ℝ≥0∞} (hκ : κ ≤ κ') (hν : ν ≤ ν') :
    hybTermSD q d κ ν ≤ hybTermSD q d κ' ν' := by
  unfold hybTermSD
  exact add_le_add (ENNReal.rpow_le_rpow (by gcongr) (by norm_num))
    (ENNReal.rpow_le_rpow hν (by norm_num))

open scoped Classical in
/-- **leanSPHINCS's masked hybrid on a parallel program family.** If runtime 1 with the full
table and runtime 2 run the canonical game at `msgPol` as the parallel programs `xP t`, with at
most `10 min d q` single sponge calls and rounds of positive width, the masked hidden mass of the
quantum commands at most `6q κ` and that of the read ports at most `ν`, then
`E p1R ≤ (√(E p2R) + hybTermSD q d κ ν)² + stageFrac S`. -/
theorem uavg_p1R_leD_of_par {A : SAdversary} {q d : ℕ} (S : PP → ((s : HPos) → XD s) → Prop)
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
    (Hh : FT → Set Z) (Hk Hk' : FT → Set X)
    (hcov : ∀ t, Covers (fullHw (tabOf t)) (Hh t) (Hk t) (Hk' t)) (κ ν : ℝ≥0∞)
    (hμ : uavg (fun t : FT ↦ if FullG S t then ((runtimeR m0R).par
      (portR X Z HPos Selections)).totalWeight .instruments (parSpongeMassR (Hh t) (Hk t) (Hk' t))
        (xP t) initR else 0) ≤ ((6 * q : ℕ) : ℝ≥0∞) * κ)
    (hν : uavg (fun t : FT ↦ if FullG S t then ((runtimeR m0R).par
      (portR X Z HPos Selections)).totalWeight .instruments
        (parWeight (portR X Z HPos Selections) (readMass (Hh t) (Hk t) (Hk' t))) (xP t) initR
      else 0) ≤ ν) :
    uavg (p1R A fullHw) ≤
      (uavg (fun L ↦ p2R msgPol A (pubOf L) (valueAt L)) ^ (2⁻¹ : ℝ) + hybTermSD q d κ ν) ^ 2 +
        stageFrac S := by
  have h := uavg_win_runtime1R_portR_le_masked .instruments (fun t : FT ↦ fullHw (tabOf t))
    Hh Hk Hk' hcov m0R xP (fun _ ↦ SubState.basis ()) (fun _ ↦ winObs)
    (measurableSet_singleton true) (10 * min d q) hd (FullG S) _ ν hμ hν
  have e1 : uavg (fun t : FT ↦ p1R A fullHw (tabOf t)) = uavg (p1R A fullHw) :=
    uavg_tabOf (p1R A fullHw)
  have e2 : uavg (fun t : FT ↦ p2R msgPol A (pubOf (tabOf t)) (valueAt (tabOf t))) =
      uavg (fun L ↦ p2R msgPol A (pubOf L) (valueAt L)) :=
    uavg_tabOf (fun L ↦ p2R msgPol A (pubOf L) (valueAt L))
  rw [← e1, ← e2, show (fun t : FT ↦ p1R A fullHw (tabOf t)) = _ from funext h1,
    show (fun t : FT ↦ p2R msgPol A (pubOf (tabOf t)) (valueAt (tabOf t))) = _ from funext h2]
  refine h.trans_eq ?_
  unfold hybTermSD stageFrac
  rw [add_assoc]

end Quantum.Sphincs.Assembly

end
