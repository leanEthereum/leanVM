module

public import Quantum.Xmss.Assembly.Depth.Caps
public import Quantum.Xmss.Assembly.Depth.Refuse
public import Quantum.Xmss.Assembly.Depth.Hybrid
public import Quantum.Xmss.Assembly.Depth.EventGame
public import Quantum.Xmss.Assembly.Depth.BoundValue
public import Quantum.Xmss.Assembly.Depth.MassGame

@[expose] public section

/-!
# leanXMSS against depth-limited parallel adversaries in the QRPM (assembly)

Security's chain for the serialized refusing adversary `A = serialize (refusePar Ap)` of a
parallel adversary `Ap` of total width `q`, `d` rounds and `lifetime` signing requests:
`winProbPar Ap ≤ winProbPar (refusePar Ap) = winProb A` (`winProbPar_le_refusePar`,
`serialize_refusePar`), `A` within the budgets (`isChargeBound_toSeq_perm`,
`isChargeBound_toSeq_sign`) and without leaf reuse (`noLeafReuse_serialize_refusePar`). The depth
enters at two places:

* **the event** (`hev`): at a good table,
  `ewR (gameR A) L ≤ (advTermD q d + verTerm q + √(twPR A L + verLin q))²` (EventGame's
  `ewR_le_depth_serialize_refusePar`, on Sim's parallel prefix `prefixRPar`);
* **the hybrid** (`hhyb`): `E p1R ≤ (√(E p2R) + hybTermD q d)² + r0Term` (`uavg_p1R_leD_of_par`:
  Hybrid's masked hybrid on Sim's parallel game `gameRPar`, at most `10 min d q` quantum
  commands, the masses by MassGame).

With them as hypotheses, `winProb_le_qrpmDepthBound_of` (sequential) and
`winProbPar_le_qrpmDepthBound_of` (parallel) give `qrpmDepthBound q d`, the prefix's classical
costs averaged by Caps' `uavg_twPR_leD` (no range condition on `q`). Discharged:
`winProbPar_le_qrpmDepthBound`, the closed form `winProbPar_le_closedForm` (BoundValue, `q ≤ 2^84`)
and **`leanXmss_qrpm_depth_security`**.
-/

open MeasureTheory Matrix
open scoped ENNReal Kronecker

open Quantum.SufCma

namespace Quantum.Xmss.Assembly

open Quantum QuantumRuntime Quantum.Sponge Quantum.Xmss Quantum.Xmss.Hybrid HashSig LeanXmss
  LeanXmss.RandomPermutationModel Common Common.SufCma

section proof

attribute [local instance] badRDec

variable {q d : ℕ} {A : Adversary (X × Z)}
  (hperm : ∀ pk, IPFunctor.IFreeM.IsChargeBound (A pk) (cmdCharge permCharge) q)
  (hsign : ∀ pk, IPFunctor.IFreeM.IsChargeBound (A pk) (cmdCharge signCharge) lifetime)
include hperm hsign

/-- **Runtime 2's win at a good table**, from the depth-aware event bound `hev`. -/
theorem p2R_le_goodD (L : HonestTable) (hg : GoodL L)
    (hev : ewR (gameR A) L ≤ (advTermD q d + verTerm q + (twPR A L + verLin q) ^ (2⁻¹ : ℝ)) ^ 2) :
    p2R (gameR A) L ≤ (advTermD q d + verTerm q + (twPR A L + verLin q) ^ (2⁻¹ : ℝ)) ^ 2 +
      readTerm + trialHitMass m0R A L := by
  let : DecidablePred (· ∈ BadRS (S := HPos) L progCap) := badRDec L progCap
  have h := endReads_wGame_trialHit (m₀ := m0R) (A := A) hg.1 rfl (progCalls_gameR hperm hsign L)
  exact h.trans (add_le_add (add_le_add hev le_rfl) le_rfl)

/-- **Runtime 2's win probability**, averaged over the table, from the depth-aware event bound
at the good tables. -/
theorem uavg_p2R_leD (hleaf : NoLeafReuse A)
    (hev : ∀ L, GoodL L →
      ewR (gameR A) L ≤ (advTermD q d + verTerm q + (twPR A L + verLin q) ^ (2⁻¹ : ℝ)) ^ 2) :
    uavg (p2R (gameR A)) ≤ eventTermD q d := by
  set twg : HonestTable → ℝ≥0∞ := fun L ↦ if GoodL L then twPR A L else 0
  set hitg : HonestTable → ℝ≥0∞ := fun L ↦ if GoodL L then trialHitMass m0R A L else 0
  set bad : HonestTable → ℝ≥0∞ := fun L ↦ if GoodL L then 0 else 1
  have hpt : ∀ L, p2R (gameR A) L ≤
      (advTermD q d + verTerm q + (twg L + verLin q) ^ (2⁻¹ : ℝ)) ^ 2 + readTerm + hitg L +
        bad L := by
    intro L
    by_cases hg : GoodL L
    · simp only [twg, hitg, bad, hg, ↓reduceIte, add_zero]
      exact p2R_le_goodD hperm hsign L hg (hev L hg)
    · simp only [bad, hg, ↓reduceIte]
      exact (QuantumRuntime.outcomeLawWith_le_one _ _ _ _ _ _).trans le_add_self
  have htw : uavg twg ≤ clsBoundD q := uavg_twPR_leD hperm hsign hleaf
  have hJ : uavg (fun L ↦ (advTermD q d + verTerm q + (twg L + verLin q) ^ (2⁻¹ : ℝ)) ^ 2) ≤
      (advTermD q d + verTerm q + (uavg twg + verLin q) ^ (2⁻¹ : ℝ)) ^ 2 := by
    have h := uavg_sq_add_sqrt_le (advTermD q d + verTerm q) (fun L ↦ twg L + verLin q)
    rwa [uavg_add, uavg_const] at h
  calc uavg (p2R (gameR A))
      ≤ uavg (fun L ↦ (advTermD q d + verTerm q + (twg L + verLin q) ^ (2⁻¹ : ℝ)) ^ 2 +
          readTerm + hitg L + bad L) := uavg_mono hpt
    _ = uavg (fun L ↦ (advTermD q d + verTerm q + (twg L + verLin q) ^ (2⁻¹ : ℝ)) ^ 2) +
          readTerm + uavg hitg + uavg bad := by
      rw [uavg_add, uavg_add, uavg_add, uavg_const]
    _ ≤ (advTermD q d + verTerm q + (uavg twg + verLin q) ^ (2⁻¹ : ℝ)) ^ 2 + readTerm +
          trialCap + goodTerm :=
      add_le_add (add_le_add (add_le_add hJ le_rfl)
        (uavg_trialHitMass_le_of_good m0R A GoodL fun _ h ↦ ⟨h.2, h.1.1⟩)) uavg_not_goodL_le
    _ ≤ eventTermD q d := by
      unfold eventTermD
      gcongr

/-- **The depth-aware bound for one sequential adversary without leaf reuse**, from the
depth-aware event bound `hev` and hybrid `hhyb`. -/
theorem winProb_le_qrpmDepthBound_of (hleaf : NoLeafReuse A)
    (hev : ∀ L, GoodL L →
      ewR (gameR A) L ≤ (advTermD q d + verTerm q + (twPR A L + verLin q) ^ (2⁻¹ : ℝ)) ^ 2)
    (hhyb : uavg (p1R A fullHw) ≤
      (uavg (p2R (gameR A)) ^ (2⁻¹ : ℝ) + hybTermD q d) ^ 2 + r0Term) :
    winProb sufCmaScheme keccakStateEquiv A ≤ qrpmDepthBound q d := by
  have hK : uavg (p1T A fullHw) = uavg (p1R A fullHw) :=
    congrArg uavg (funext fun L ↦ (p1T_eq_p1K A tableLe_fullHw L).trans (p1K_eq_p1R A fullHw L))
  calc winProb sufCmaScheme keccakStateEquiv A = uavg (p1T A fullHw) := winProb_eq_uavg_full A
    _ = uavg (p1R A fullHw) := hK
    _ ≤ (uavg (p2R (gameR A)) ^ (2⁻¹ : ℝ) + hybTermD q d) ^ 2 + r0Term := hhyb
    _ ≤ (eventTermD q d ^ (2⁻¹ : ℝ) + hybTermD q d) ^ 2 + r0Term := by
      gcongr
      exact uavg_p2R_leD hperm hsign hleaf hev
    _ = qrpmDepthBound q d := rfl

end proof

/-! ## The depth-aware hybrid from a parallel program -/

section hyb

open Quantum.Par

/-- **The depth-aware masked hybrid** (`uavg_win_runtime1R_portR_le_masked_pad` over `maskG`):
if a parallel program `xP L` over the rounds of the sponge ports runs as `gameR A L` against
runtime 1 (cells `fullHw L`) and against `runtimeR` (`h1`, `h2`), has at most `10 min d q`
single sponge calls and rounds of positive width (`hd`), and its masked averaged hidden masses
are at most `6q kappaS` at the quantum commands (`hμ`) and `readCap` at the read ports (`hν`),
then `E p1R ≤ (√(E p2R) + hybTermD q d)² + r0Term`. -/
theorem uavg_p1R_leD_of_par {A : Adversary (X × Z)} {q d : ℕ}
    (xP : HonestTable → QComp (parSpec (recHwSpec X Z HPos Selections)
      (portR X Z HPos Selections)) (QReg.of Unit) (QReg.of Unit) Bool)
    (h1 : ∀ L, p1R A fullHw L = ((runtime1R X Z (fullHw L) m0R).par
      (portR X Z HPos Selections)).evalDistMap .instruments (xP L) (SubState.basis ()) winObs
        {true})
    (h2 : ∀ L, p2R (gameR A) L = ((runtimeR m0R).par
      (portR X Z HPos Selections)).evalDistMap .instruments (xP L) (SubState.basis ()) winObs
        {true})
    (hd : ∀ L, IPFunctor.IFreeM.IsChargeBound (xP L)
      (portCharge (spongeRounds (portR X Z HPos Selections)
        (extCls X Z (Finset HPos × Selections) (recSpec HPos Selections)))) (10 * min d q))
    (hμ : uavg (fun t : HonestTable × RE ↦ if maskG t then ((runtimeR m0R).par
      (portR X Z HPos Selections)).totalWeight .instruments
        (parSpongeMassR (coverH t.1) (coverK t.1) (coverK' t.1)) (xP t.1) initR else 0) ≤
      ((6 * q : ℕ) : ℝ≥0∞) * kappaS)
    (hν : uavg (fun t : HonestTable × RE ↦ if maskG t then ((runtimeR m0R).par
      (portR X Z HPos Selections)).totalWeight .instruments
        (parWeight (portR X Z HPos Selections) (readMass (coverH t.1) (coverK t.1) (coverK' t.1)))
          (xP t.1) initR else 0) ≤ readCap) :
    uavg (p1R A fullHw) ≤ (uavg (p2R (gameR A)) ^ (2⁻¹ : ℝ) + hybTermD q d) ^ 2 + r0Term := by
  rw [show p1R A fullHw = _ from funext h1, show p2R (gameR A) = _ from funext h2]
  refine (uavg_win_runtime1R_portR_le_masked_pad .instruments fullHw coverH coverK coverK'
    covers_fullHw m0R xP (fun _ ↦ SubState.basis ()) (fun _ ↦ winObs)
    (measurableSet_singleton true) (10 * min d q) hd maskG _ _ hμ hν).trans ?_
  refine add_le_add (le_of_eq ?_) maskG_frac_le
  rw [hybTermD, add_assoc]

end hyb

section par

attribute [local instance] badRDec

/-- **The depth-aware bound for a parallel adversary**, from the depth-aware event bound `hev`
and hybrid `hhyb` for its serialized refusing version `serialize (refusePar Ap)`: total width at
most `q`, at most `lifetime` signing requests. -/
theorem winProbPar_le_qrpmDepthBound_of {q d : ℕ}
    (Ap : AdversaryPar PublicKey SigningRequest (Option Signature) Forgery (X × Z))
    (hq : ∀ pk, IPFunctor.IFreeM.IsChargeBound (Ap pk) (cmdChargePar widthCharge) q)
    (hs : ∀ pk, IPFunctor.IFreeM.IsChargeBound (Ap pk) (cmdChargePar signChargePar) lifetime)
    (hev : ∀ L, GoodL L →
      ewR (gameR (serialize (refusePar Ap))) L ≤
        (advTermD q d + verTerm q +
          (twPR (serialize (refusePar Ap)) L + verLin q) ^ (2⁻¹ : ℝ)) ^ 2)
    (hhyb : uavg (p1R (serialize (refusePar Ap)) fullHw) ≤
      (uavg (p2R (gameR (serialize (refusePar Ap)))) ^ (2⁻¹ : ℝ) + hybTermD q d) ^ 2 + r0Term) :
    winProbPar sufCmaScheme keccakStateEquiv Ap ≤ qrpmDepthBound q d :=
  (winProbPar_le_refusePar keccakStateEquiv Ap).trans
    (winProb_le_qrpmDepthBound_of
      (fun pk ↦ isChargeBound_toSeq_perm (isChargeBound_refusePar (hq pk)))
      (fun pk ↦ isChargeBound_toSeq_sign (isChargeBound_refusePar (hs pk)))
      (noLeafReuse_serialize_refusePar Ap) hev hhyb)

end par

/-! ## The final theorem -/

section final

attribute [local instance] badRDec

variable (Ap : AdversaryPar PublicKey SigningRequest (Option Signature) Forgery (X × Z))
  {q d : ℕ}
  (hq : ∀ pk, IPFunctor.IFreeM.IsChargeBound (Ap pk)
    (cmdChargePar Quantum.SufCma.widthCharge) q)
  (hd : ∀ pk, IPFunctor.IFreeM.IsChargeBound (Ap pk)
    (cmdChargePar Quantum.SufCma.roundCharge) d)
  (hs : ∀ pk, IPFunctor.IFreeM.IsChargeBound (Ap pk) (cmdChargePar signChargePar) lifetime)

include hq hd hs in
/-- **The depth-aware hybrid for a parallel adversary** (`uavg_p1R_leD_of_par` at Sim's
`gameRPar (refusePar Ap)`), from the masked hidden mass `hμ` of its quantum commands. -/
theorem uavg_p1R_leD_par
    (hμ : uavg (fun t : HonestTable × RE ↦ if maskG t then ((runtimeR m0R).par
      (portR X Z HPos Selections)).totalWeight .instruments
        (parSpongeMassR (coverH t.1) (coverK t.1) (coverK' t.1)) (gameRPar (refusePar Ap) t.1)
          initR else 0) ≤ ((6 * q : ℕ) : ℝ≥0∞) * kappaS) :
    uavg (p1R (serialize (refusePar Ap)) fullHw) ≤
      (uavg (p2R (gameR (serialize (refusePar Ap)))) ^ (2⁻¹ : ℝ) + hybTermD q d) ^ 2 +
        r0Term :=
  uavg_p1R_leD_of_par (gameRPar (refusePar Ap)) (fun L ↦ p1R_eq_par (refusePar Ap) L fullHw)
    (fun L ↦ p2R_eq_par (refusePar Ap) L)
    (fun L ↦ spongeRounds_gameRPar (refusePar Ap) L
      (fun pk ↦ isChargeBound_refusePar (hq pk)) (fun pk ↦ isChargeBound_refusePar (hd pk)))
    hμ (uavg_mask_parReadMass_le (refusePar Ap)
      (fun pk ↦ isChargeBound_toSeq_perm (isChargeBound_refusePar (hq pk)))
      (fun pk ↦ isChargeBound_toSeq_sign (isChargeBound_refusePar (hs pk))))

include hq hd hs in
/-- **The depth-aware bound for a parallel adversary from the masked hidden mass** `hμ` of the
quantum commands of its parallel game: the event by EventGame's
`ewR_le_depth_serialize_refusePar`, the hybrid by `uavg_p1R_leD_par`. -/
theorem winProbPar_le_qrpmDepthBound_of_mass
    (hμ : uavg (fun t : HonestTable × RE ↦ if maskG t then ((runtimeR m0R).par
      (portR X Z HPos Selections)).totalWeight .instruments
        (parSpongeMassR (coverH t.1) (coverK t.1) (coverK' t.1)) (gameRPar (refusePar Ap) t.1)
          initR else 0) ≤ ((6 * q : ℕ) : ℝ≥0∞) * kappaS) :
    winProbPar sufCmaScheme keccakStateEquiv Ap ≤ qrpmDepthBound q d :=
  winProbPar_le_qrpmDepthBound_of Ap hq hs (ewR_le_depth_serialize_refusePar Ap hq hd hs)
    (uavg_p1R_leD_par Ap hq hd hs hμ)

include hq hd hs in
/-- **The depth-aware bound for a parallel adversary**: the masked hidden mass of its parallel
game's quantum commands by MassGame's `uavg_mask_parSpongeMass_le`. -/
theorem winProbPar_le_qrpmDepthBound :
    winProbPar sufCmaScheme keccakStateEquiv Ap ≤ qrpmDepthBound q d :=
  winProbPar_le_qrpmDepthBound_of_mass Ap hq hd hs (uavg_mask_parSpongeMass_le (refusePar Ap)
    (fun pk ↦ isChargeBound_toSeq_perm (isChargeBound_refusePar (hq pk)))
    (fun pk ↦ isChargeBound_toSeq_sign (isChargeBound_refusePar (hs pk))))

include hq hd hs in
/-- **The closed form** (BoundValue's `qrpmDepthBound_le`): for `q ≤ 2^84` and `d' = min d q`,
`winProbPar ≤ ((20.4 √(q d') + 11 · 2^-28 q + 21 · 2^14 √q + 75 · 2^30) / 2^64)²`. -/
theorem winProbPar_le_closedForm (hq84 : q ≤ 2 ^ 84) :
    winProbPar sufCmaScheme keccakStateEquiv Ap ≤ ENNReal.ofReal (((102 / 5 *
      √((q : ℝ) * (min d q : ℕ)) + 11 * q / 2 ^ 28 + 21 * 2 ^ 14 * √(q : ℝ) + 75 * 2 ^ 30) /
        2 ^ 64) ^ 2) :=
  (winProbPar_le_qrpmDepthBound Ap hq hd hs).trans (qrpmDepthBound_le hq84)

end final

/-- **leanXMSS is quantum SUF-CMA secure against depth-limited parallel adversaries in the
QRPM** with bound `qrpmDepthBound q d`: a parallel adversary making at most `q` permutation calls
in at most `d` rounds and at most `lifetime` signing requests forges with probability at most
`qrpmDepthBound q d` (closed form: `winProbPar_le_closedForm`). -/
theorem leanXmss_qrpm_depth_security :
    QuantumStronglyUnforgeablePar sufCmaScheme keccakStateEquiv lifetime qrpmDepthBound :=
  fun _ _ Ap hq hd hs ↦ winProbPar_le_qrpmDepthBound Ap hq hd hs

end Quantum.Xmss.Assembly

end
