module

public import Quantum.Qrom.Sphincs.DepthGame
public import Quantum.Qrom.Sphincs.DepthCharges
public import Quantum.Qrom.Sphincs.DepthBound
public import Quantum.Qrom.Xmss.DepthHybrid

@[expose] public section

/-!
# The hidden-value hybrid of leanSPHINCS in the QROM, with rounds

The sequential hybrid (Hybrid's `uavg_p1Q_le`) runs on the game of the serialized adversary. That
game runs as the game with batched rounds (`runTWEq_gameQ`, against runtime 1 and runtime 2),
the serialization of the game with rounds (`gameQB_serialize`), so both runtimes see the game with
rounds through their round runtimes (`evalDistMap_substitute_parToSeq`) and the graded hybrid of
the round runtime (`Hybrid.uavg_win_runtime1R_par_le_graded_total`) applies with `min d q`
rounds:

* the rounds' hidden masses are the hidden masses of their calls of `h` in the batched game
  (`Hybrid.totalWeight_parSpongeMass_eq`): at most `q · 2^-128`, averaged, by the masses' bound
  of Hybrid on the batched game (`uavg_spongeMassB_le`; the template facts of DepthCharges);
* the reads are single calls: at most `clsCapQ · 2^-128` (`uavg_readMassB_le`).

Result (`winProb_le_hybrid_depth`): `winProb ≤ (√(E p2Q strPol) + hybTermQD q d)²`.
-/

open IPFunctor
open scoped ENNReal Kronecker
open HashSig hiding PublicKey
open Sphincs hiding HashDomain

namespace Quantum.Qrom.Sphincs

open Quantum QuantumRuntime Quantum.Par Quantum.Sponge Quantum.Xmss.Hybrid
open Quantum.Xmss.Assembly (recHwSpec recSpec runtimeR runtime1R realizeT extCls
  sum_totalWeight_portMass_runtimeR_le_inv isChargeBound_mono_charge viewBy_runtimeR_of_disc)

attribute [local irreducible] sphincsRom

variable (hcomm : ∀ R : QuantumRuntime (RSpecS SelMem), RoundsCommute TPos SelMem hmsgRoute R)
  (A : SAdversaryPar) {q d : ℕ}
  (hw : ∀ pk, IFreeM.IsChargeBound (A pk) (SufCma.cmdChargePar SufCma.widthCharge) q)
  (hr : ∀ pk, IFreeM.IsChargeBound (A pk) (SufCma.cmdChargePar SufCma.roundCharge) d)
  (hs : ∀ pk, IFreeM.IsChargeBound (A pk) (SufCma.cmdChargePar SufCma.signChargePar)
    signatureLimit)

/-! ## The wins through the round runtimes -/

/-- Equal runs have equal observed distributions. -/
theorem evalDistMap_congr_run {spec : QuantumOracleSpec.{0, 0}} (R : QuantumRuntime spec)
    {X : QReg → Type} {A : QReg} {x y : QuantumComp LocalSig.instruments.{0} spec X A}
    (h : R.run .instruments x = R.run .instruments y) (ρ : SubState A) {γ : Type*}
    [MeasurableSpace γ] (f : (Σ u, X u) → γ) :
    R.evalDistMap .instruments x ρ f = R.evalDistMap .instruments y ρ f := by
  unfold QuantumRuntime.evalDistMap QuantumRuntime.jointPost
  rw [h]

include hcomm in
/-- Runtime 1's win for the serialization: the game with rounds against the round runtime. -/
theorem p1Q_serialize (θ : TVals) :
    p1Q (SufCma.serialize A) θ =
      ((runtime1R PairOut Qrom.HashDomain (hwT θ) m0H).par portS).evalDistMap .instruments
        (gameQPar msgPol A θ) (SubState.basis ()) winObsQ {true} := by
  unfold p1Q
  rw [evalDistMap_congr_run _ (runTWEq_gameQ (hcomm _) msgPol A θ).1, gameQB_serialize]
  exact congrArg (fun μ : MeasureTheory.Measure Bool ↦ μ {true})
    (evalDistMap_substitute_parToSeq _ portS (gameQPar msgPol A θ) _ winObsQ)

include hcomm in
/-- Runtime 2's win for the serialization at `msgPol`: the game with rounds against the round
runtime. -/
theorem p2Q_serialize (θ : TVals) :
    p2Q msgPol (SufCma.serialize A) θ =
      ((runtimeR m0H).par portS).evalDistMap .instruments (gameQPar msgPol A θ)
        (SubState.basis ()) winObsQ {true} := by
  unfold p2Q
  rw [evalDistMap_congr_run _ (runTWEq_gameQ (hcomm _) msgPol A θ).1, gameQB_serialize]
  exact congrArg (fun μ : MeasureTheory.Measure Bool ↦ μ {true})
    (evalDistMap_substitute_parToSeq _ portS (gameQPar msgPol A θ) _ winObsQ)

/-! ## The masses of the batched game -/

/-- **`ViewByOn` for the batched game.** -/
theorem viewByOn_gameTPar (pol : DigestPolicy)
    (ρ : Matrix (QReg.of Unit × QReg.of (HwReg PairOut Qrom.HashDomain (Finset TPos × SelMem)))
      (QReg.of Unit × QReg.of (HwReg PairOut Qrom.HashDomain (Finset TPos × SelMem))) ℂ)
    (j : ℕ) :
    ViewByOn (runtimeR m0H) LocalSig.Interp.instruments (fun i ↦ i.isLeft = true)
      (fun r ↦ r.2.2.1) (fun θ ↦ gameQB pol A θ) (fun _ ↦ ρ) j :=
  (viewBy_runtimeR_of_disc _ m0H (gameTPar pol A) ∅ (disc_gameTPar pol A ∅) (fun _ ↦ ρ)
    (lazy_const _ ρ) (fun _ ↦ suppAt_empty _ ρ) j).viewByOn _

/-- **`hinv` for the batched game.** -/
theorem hinvB (pol : DigestPolicy) (hpol : pol.NoVal)
    (Q : (recHwSpec PairOut Qrom.HashDomain TPos SelMem).Port → Prop)
    (hQ : ∀ c, ¬Q (.inl (.inr c))) (hQ' : ∀ T, ¬Q (.inr T)) (θ : TVals) :
    (runtimeR m0H).ForallQueries LocalSig.Interp.instruments
      (Quantum.Xmss.Assembly.invSupp (runtimeR m0H) Q (SrcInv SelMem θ)) (gameQB pol A θ)
        initH :=
  forallQueries_of_hp hQ hQ' m0H _ θ _ ∅ ∅ (hp_gameTPar θ hpol A) initH
    ((querySupportedOn_init m0H rfl _).imp fun _ ha ↦
      invP_of_label_empty (Set.mem_singleton_iff.1 ha))

include hw hs in
/-- **The masses at the calls of `F` of the batched game**: at most `q · 2^-128`, averaged. -/
theorem uavg_spongeMassB_le :
    uavg (fun θ : TVals ↦ (runtimeR m0H).totalWeight .instruments
      (spongeMass (hidCells θ) ∅ ∅) (gameQB msgPol A θ) initH) ≤ q * kappaQ := by
  have hc : (fun i ↦ if (extCls PairOut Qrom.HashDomain (Finset TPos × SelMem)
      (recSpec TPos SelMem) i = false) then 1 else 0) = spongeQS := by
    funext i
    rcases Bool.eq_false_or_eq_true (extCls PairOut Qrom.HashDomain (Finset TPos × SelMem)
      (recSpec TPos SelMem) i) with h | h <;> simp [h]
  refine Quantum.Qrom.Xmss.uavg_le_of_sum_le _ _ ((sum_totalWeight_portMass_runtimeR_le_inv
    .instruments
    (fun i ↦ extCls PairOut Qrom.HashDomain (Finset TPos × SelMem) (recSpec TPos SelMem) i = false)
    m0H (fun r ↦ r.2.2.1) (fun θ ↦ gameQB msgPol A θ) (fun _ ↦ initH)
    (fun _ ↦ initH_posSemidef) (fun j ↦ viewByOn_gameTPar A msgPol initH j)
    (fun θ ↦ SrcInv SelMem θ)
    (fun θ ↦ hinvB A msgPol noVal_msgPol _ (fun _ h ↦ Bool.noConfusion h)
      (fun _ h ↦ Bool.noConfusion h) θ) hidCells (fun _ ↦ ∅) (fun _ ↦ ∅) kappaQ sourcesQ
    (fun θ ↦ by rw [hc]; exact advCalls_gameQB msgPol A hw hs θ)).trans ?_)
  exact Quantum.Qrom.Xmss.sum_mul_trace_le kappaQ _ ofReal_trace_initH_le_one q

include hw hs in
/-- **At most `clsCapQ` reads** in the batched game. -/
theorem readCalls_gameQB (pol : DigestPolicy) (θ : TVals) :
    IFreeM.IsChargeBound (gameQB pol A θ)
      (portCharge fun i ↦ if readPortQ i = true then 1 else 0) clsCapQ := by
  have he : rChargeQ SelMem 0 1 0 1 = fun i ↦ if readRecPortQ SelMem i = true then 1 else 0 := by
    funext i
    rcases i with ((i | c) | c) | T <;> rfl
  have h := (isChargeBound_realizeT 0 1 0 1 θ (chg_gameTPar 0 1 0 1 pol A hw hs)).mono
    (show gameCallsQ 0 1 0 1 q ≤ clsCapQ by
      have h : signCallsQ 1 0 1 ≤ signCallsQ 1 1 1 := by
        simp only [signCallsQ, selCallsQ, pubCallsQ]
        omega
      have h' := Nat.mul_le_mul_right signatureLimit h
      simp only [clsCapQ, gameCallsQ]
      omega)
  rw [he] at h
  refine isChargeBound_mono_charge (fun s a ↦ ?_) h
  rcases a with o | ⟨i, E, ℓ⟩
  · exact le_rfl
  · show (if readPortQ i = true then 1 else 0) ≤ (if readRecPortQ SelMem i = true then 1 else 0)
    rcases i with ((i | c) | c) | T <;> simp [readPortQ, readRecPortQ]

include hw hs in
/-- **The read masses of the batched game**: at most `clsCapQ · 2^-128`, averaged. -/
theorem uavg_readMassB_le :
    uavg (fun θ : TVals ↦ (runtimeR m0H).totalWeight .instruments
      (readMass (hidCells θ) ∅ ∅) (gameQB msgPol A θ) initH) ≤ clsCapQ * kappaQ := by
  refine (uavg_mono fun θ ↦ totalWeight_le_totalWeight (runtimeR m0H) .instruments
    (fun i σ _ ↦ readMass_le_readPortQ θ i σ) (gameQB msgPol A θ) initH_posSemidef).trans ?_
  refine Quantum.Qrom.Xmss.uavg_le_of_sum_le _ _ ((sum_totalWeight_portMass_runtimeR_le_inv
    .instruments (fun i ↦ readPortQ i = true) m0H (fun r ↦ r.2.2.1)
    (fun θ ↦ gameQB msgPol A θ) (fun _ ↦ initH) (fun _ ↦ initH_posSemidef)
    (fun j ↦ viewByOn_gameTPar A msgPol initH j) (fun θ ↦ SrcInv SelMem θ)
    (fun θ ↦ hinvB A msgPol noVal_msgPol _ (fun _ h ↦ Bool.noConfusion h)
      (fun _ h ↦ Bool.noConfusion h) θ) hidCells (fun _ ↦ ∅) (fun _ ↦ ∅) kappaQ sourcesQ
    (fun θ ↦ readCalls_gameQB A hw hs msgPol θ)).trans ?_)
  exact Quantum.Qrom.Xmss.sum_mul_trace_le kappaQ _ ofReal_trace_initH_le_one clsCapQ

/-! ## The hybrid -/

/-- The reads carry no mass at the port of the rounds. -/
theorem readMass_portS (Hh : Set Qrom.HashDomain) (Hk Hk' : Set PairOut) (u : Unit)
    (σ : Matrix ((RSpecS SelMem).In (portS u) × QReg.of (RRegS SelMem))
      ((RSpecS SelMem).In (portS u) × QReg.of (RRegS SelMem)) ℂ) :
    readMass (S := TPos) (M' := SelMem) Hh Hk Hk' (portS u) σ = 0 :=
  rfl

include hw hs in
/-- **The rounds' hidden masses**: at most `q · 2^-128`, averaged over the hidden values. -/
theorem uavg_parSpongeMass_le :
    uavg (fun θ : TVals ↦ ((runtimeR m0H).par portS).totalWeight .instruments
      (parSpongeMass (S := TPos) (M' := SelMem) (hidCells θ) ∅ ∅) (gameQPar msgPol A θ)
      ((SubState.basis ()).matrix ⊗ₖ
        (runtimeR (X := PairOut) (Z := Qrom.HashDomain) m0H).init.matrix)) ≤ q * kappaQ := by
  have e : (fun θ : TVals ↦ ((runtimeR m0H).par portS).totalWeight .instruments
      (parSpongeMass (S := TPos) (M' := SelMem) (hidCells θ) ∅ ∅) (gameQPar msgPol A θ)
      ((SubState.basis ()).matrix ⊗ₖ
        (runtimeR (X := PairOut) (Z := Qrom.HashDomain) m0H).init.matrix)) =
      fun θ ↦ (runtimeR m0H).totalWeight .instruments (spongeMass (hidCells θ) ∅ ∅)
        (gameQB msgPol A θ) initH := by
    funext θ
    rw [gameQB_serialize]
    exact totalWeight_parSpongeMass_eq (hidCells θ) ∅ ∅ m0H (gameQPar msgPol A θ)
      initH_posSemidef
  rw [e]
  exact uavg_spongeMassB_le A hw hs

include hw hs in
/-- **The reads' hidden masses**: at most `clsCapQ · 2^-128`, averaged over the hidden values. -/
theorem uavg_parReadMass_le :
    uavg (fun θ : TVals ↦ ((runtimeR m0H).par portS).totalWeight .instruments
      (parWeight portS (readMass (S := TPos) (M' := SelMem) (hidCells θ) ∅ ∅))
      (gameQPar msgPol A θ) ((SubState.basis ()).matrix ⊗ₖ
        (runtimeR (X := PairOut) (Z := Qrom.HashDomain) m0H).init.matrix)) ≤
      clsCapQ * kappaQ := by
  have e : (fun θ : TVals ↦ ((runtimeR m0H).par portS).totalWeight .instruments
      (parWeight portS (readMass (S := TPos) (M' := SelMem) (hidCells θ) ∅ ∅))
      (gameQPar msgPol A θ) ((SubState.basis ()).matrix ⊗ₖ
        (runtimeR (X := PairOut) (Z := Qrom.HashDomain) m0H).init.matrix)) =
      fun θ ↦ (runtimeR m0H).totalWeight .instruments (readMass (hidCells θ) ∅ ∅)
        (gameQB msgPol A θ) initH := by
    funext θ
    rw [gameQB_serialize]
    exact ((runtimeR m0H).totalWeight_substitute_parToSeq_of_eq_zero portS
      (readMass_portS (hidCells θ) ∅ ∅) (gameQPar msgPol A θ) initH).symm
  rw [e]
  exact uavg_readMassB_le A hw hs

include hcomm hw hr hs in
/-- **The graded hybrid with rounds, averaged**: runtime 1 against runtime 2 at `msgPol`. -/
theorem uavg_p1Q_le_depth :
    uavg (p1Q (SufCma.serialize A)) ≤
      (uavg (p2Q msgPol (SufCma.serialize A)) ^ (2⁻¹ : ℝ) + hybTermQD q d) ^ 2 := by
  have h := uavg_win_runtime1R_par_le_graded_total .instruments hwT hidCells (fun _ ↦ ∅)
    (fun _ ↦ ∅) covers_hwT m0H (fun θ ↦ gameQPar msgPol A θ) (fun _ ↦ SubState.basis ())
    (fun _ ↦ winObsQ) (measurableSet_singleton true) (min d q)
    (fun θ ↦ rounds_gameQPar_min msgPol A hw hr hs θ) (q * kappaQ) (clsCapQ * kappaQ)
    (uavg_parSpongeMass_le A hw hs) (uavg_parReadMass_le A hw hs)
  have e1 : (fun θ ↦ ((runtime1R PairOut Qrom.HashDomain (hwT θ) m0H).par portS).evalDistMap
      .instruments (gameQPar msgPol A θ) (SubState.basis ()) winObsQ {true}) =
      p1Q (SufCma.serialize A) :=
    funext fun θ ↦ (p1Q_serialize hcomm A θ).symm
  have e2 : (fun θ ↦ ((runtimeR m0H).par portS).evalDistMap .instruments (gameQPar msgPol A θ)
      (SubState.basis ()) winObsQ {true}) = p2Q msgPol (SufCma.serialize A) :=
    funext fun θ ↦ (p2Q_serialize hcomm A θ).symm
  rw [e1, e2, add_assoc] at h
  exact h

include hcomm hw hr hs in
/-- **The hybrid with rounds, squared**: `winProb ≤ (√(E p2Q strPol) + hybTermQD q d)²`. -/
theorem winProb_le_hybrid_depth :
    SufCma.winProb sphincsRom (SufCma.serialize A) ≤
      (uavg (p2Q strPol (SufCma.serialize A)) ^ (2⁻¹ : ℝ) + hybTermQD q d) ^ 2 := by
  rw [← uavg_p2Q_msgPol_eq]
  exact (winProb_eq_uavg_p1Q (SufCma.serialize A)).trans_le (uavg_p1Q_le_depth hcomm A hw hr hs)

end Quantum.Qrom.Sphincs

end
