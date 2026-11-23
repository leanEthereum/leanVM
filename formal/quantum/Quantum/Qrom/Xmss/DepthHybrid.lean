module

public import Quantum.Qrom.Xmss.Depth

@[expose] public section

/-!
# The hidden-value hybrid of leanXMSS in the QROM, with rounds

The sequential hybrid (Hybrid's `winProb_le_hybrid_qrom`) runs on the game of the serialized
adversary. Its game is the serialization of the game with rounds (`gameQ_serialize`), so both
runtimes see the game with rounds through their round runtimes (`evalDistMap_substitute_parToSeq`)
and the graded hybrid of the round runtime (`Hybrid.uavg_win_runtime1R_par_le_graded_total`)
applies with `min d q` rounds:

* the rounds' hidden masses are the hidden masses of their calls of `h`
  (`Hybrid.totalWeight_parSpongeMass_eq`): at most `q · 2^-128` (Hybrid's `uavg_spongeMass_le`);
* the reads are single calls of both programs (`totalWeight_substitute_parToSeq_of_eq_zero`): at
  most `verifyCalls · 2^-128` (Hybrid's `uavg_readMass_le`).

Result (`winProb_le_hybrid_depth`): `winProb ≤ (√(E p2Q) + hybTermQD q d)²` with
`hybTermQD q d = √(4 · min d q · q · 2^-128) + √(verifyCalls · 2^-128)`.
-/

open IPFunctor
open scoped ENNReal Kronecker

universe u₁ v₁ w

namespace Quantum.QuantumRuntime

open Quantum.Par

/-- **The observed distribution of a serialized program** is that of the program with rounds
against the round runtime. -/
theorem evalDistMap_substitute_parToSeq {spec : QuantumOracleSpec.{u₁, v₁}}
    (R : QuantumRuntime spec) {Q : Type u₁} (port : Q → spec.Port) {X : QReg → Type w}
    {A : QReg} (x : QuantumComp LocalSig.instruments.{v₁} (parSpec spec port) X A)
    (ρ : SubState A) {γ : Type*} [MeasurableSpace γ] (f : (Σ u, X u) → γ) :
    R.evalDistMap .instruments (IFreeM.substitute (parToSeq port) x) ρ f =
      (R.par port).evalDistMap .instruments x ρ f := by
  unfold QuantumRuntime.evalDistMap QuantumRuntime.jointPost
  rw [R.run_substitute_parToSeq port x]
  rfl

end Quantum.QuantumRuntime

namespace Quantum.Qrom.Xmss

open Quantum QuantumRuntime Quantum.Par Quantum.Sponge Quantum.Xmss.Hybrid
open LeanXmss HashSig
open Quantum.Xmss.Assembly (recHwSpec recSpec runtimeR runtime1R extCls)

attribute [local irreducible] xmssRom

/-- Runtime 1's win for the serialization: the game with rounds against the round runtime. -/
theorem p1Q_serialize (A : AdversaryPar) (θ : HPos → Digest) :
    p1Q (SufCma.serialize A) θ =
      ((runtime1R HashOutput HashDomain (tableHwQ θ) m0H).par portQ).evalDistMap .instruments
        (gameQPar A θ) (SubState.basis ()) winObsQ {true} := by
  unfold p1Q
  rw [gameQ_serialize]
  exact congrArg (fun μ : MeasureTheory.Measure Bool ↦ μ {true})
    (evalDistMap_substitute_parToSeq _ portQ (gameQPar A θ) _ winObsQ)

/-- Runtime 2's win for the serialization: the game with rounds against the round runtime. -/
theorem p2Q_serialize (A : AdversaryPar) (θ : HPos → Digest) :
    p2Q (SufCma.serialize A) θ =
      ((runtimeR m0H).par portQ).evalDistMap .instruments (gameQPar A θ) (SubState.basis ())
        winObsQ {true} := by
  unfold p2Q
  rw [gameQ_serialize]
  exact congrArg (fun μ : MeasureTheory.Measure Bool ↦ μ {true})
    (evalDistMap_substitute_parToSeq _ portQ (gameQPar A θ) _ winObsQ)

/-- **The hybrid term with rounds**: `√(4 · min d q · q κ) + √(verifyCalls · κ)`
(`= 2√(q · min d q)·2^-64 + √(v·2^-128)`). -/
noncomputable def hybTermQD (q d : ℕ) : ℝ≥0∞ :=
  (4 * (((min d q : ℕ) : ℝ≥0∞) * (q * kappaQ))) ^ (2⁻¹ : ℝ) +
    (verifyCalls * kappaQ) ^ (2⁻¹ : ℝ)

/-- The reads carry no mass at the port of the rounds. -/
theorem readMass_portQ (Hh : Set HashDomain) (Hk Hk' : Set HashOutput) (u : Unit)
    (σ : Matrix ((RSpec SelMem).In (portQ u) × QReg.of (RReg SelMem))
      ((RSpec SelMem).In (portQ u) × QReg.of (RReg SelMem)) ℂ) :
    readMass (S := HPos) (M' := SelMem) Hh Hk Hk' (portQ u) σ = 0 :=
  rfl

variable (A : AdversaryPar) {q d : ℕ}
  (hw : ∀ pk, IFreeM.IsChargeBound (A pk) (SufCma.cmdChargePar SufCma.widthCharge) q)
  (hr : ∀ pk, IFreeM.IsChargeBound (A pk) (SufCma.cmdChargePar SufCma.roundCharge) d)
  (hs : ∀ pk, IFreeM.IsChargeBound (A pk) (SufCma.cmdChargePar SufCma.signChargePar) lifetime)

include hw hs in
/-- **The rounds' hidden masses**: at most `q · 2^-128`, averaged over the hidden values. -/
theorem uavg_parSpongeMass_le :
    uavg (fun θ : HPos → Digest ↦ ((runtimeR m0H).par portQ).totalWeight .instruments
      (parSpongeMass (S := HPos) (M' := SelMem) (hidCells θ) ∅ ∅) (gameQPar A θ)
      ((SubState.basis ()).matrix ⊗ₖ
        (runtimeR (X := HashOutput) (Z := HashDomain) m0H).init.matrix)) ≤ q * kappaQ := by
  have e : (fun θ : HPos → Digest ↦ ((runtimeR m0H).par portQ).totalWeight .instruments
      (parSpongeMass (S := HPos) (M' := SelMem) (hidCells θ) ∅ ∅) (gameQPar A θ)
      ((SubState.basis ()).matrix ⊗ₖ
        (runtimeR (X := HashOutput) (Z := HashDomain) m0H).init.matrix)) =
      fun θ ↦ (runtimeR m0H).totalWeight .instruments (spongeMass (hidCells θ) ∅ ∅)
        (gameQ (SufCma.serialize A) θ) initH := by
    funext θ
    rw [gameQ_serialize]
    exact totalWeight_parSpongeMass_eq (hidCells θ) ∅ ∅ m0H (gameQPar A θ) initH_posSemidef
  rw [e]
  exact uavg_spongeMass_le (SufCma.serialize A)
    (fun pk ↦ SufCma.isChargeBound_toSeq_hash (hw pk))
    (fun pk ↦ SufCma.isChargeBound_toSeq_sign (hs pk))

include hw hs in
/-- **The reads' hidden masses**: at most `verifyCalls · 2^-128`, averaged over the hidden
values. -/
theorem uavg_parReadMass_le :
    uavg (fun θ : HPos → Digest ↦ ((runtimeR m0H).par portQ).totalWeight .instruments
      (parWeight portQ (readMass (S := HPos) (M' := SelMem) (hidCells θ) ∅ ∅)) (gameQPar A θ)
      ((SubState.basis ()).matrix ⊗ₖ
        (runtimeR (X := HashOutput) (Z := HashDomain) m0H).init.matrix)) ≤
      verifyCalls * kappaQ := by
  have e : (fun θ : HPos → Digest ↦ ((runtimeR m0H).par portQ).totalWeight .instruments
      (parWeight portQ (readMass (S := HPos) (M' := SelMem) (hidCells θ) ∅ ∅)) (gameQPar A θ)
      ((SubState.basis ()).matrix ⊗ₖ
        (runtimeR (X := HashOutput) (Z := HashDomain) m0H).init.matrix)) =
      fun θ ↦ (runtimeR m0H).totalWeight .instruments (readMass (hidCells θ) ∅ ∅)
        (gameQ (SufCma.serialize A) θ) initH := by
    funext θ
    rw [gameQ_serialize]
    exact ((runtimeR m0H).totalWeight_substitute_parToSeq_of_eq_zero portQ
      (readMass_portQ (hidCells θ) ∅ ∅) (gameQPar A θ) initH).symm
  rw [e]
  exact uavg_readMass_le (SufCma.serialize A)
    (fun pk ↦ SufCma.isChargeBound_toSeq_hash (hw pk))
    (fun pk ↦ SufCma.isChargeBound_toSeq_sign (hs pk))

include hw hr hs in
/-- **The graded hybrid with rounds, averaged**: runtime 1 against runtime 2. -/
theorem uavg_p1Q_le_depth :
    uavg (p1Q (SufCma.serialize A)) ≤
      (uavg (p2Q (SufCma.serialize A)) ^ (2⁻¹ : ℝ) + hybTermQD q d) ^ 2 := by
  have h := uavg_win_runtime1R_par_le_graded_total .instruments tableHwQ hidCells (fun _ ↦ ∅)
    (fun _ ↦ ∅) covers_tableHwQ m0H (fun θ ↦ gameQPar A θ) (fun _ ↦ SubState.basis ())
    (fun _ ↦ winObsQ) (measurableSet_singleton true) (min d q)
    (fun θ ↦ rounds_gameQPar_min A hw hr hs θ) (q * kappaQ) (verifyCalls * kappaQ)
    (uavg_parSpongeMass_le A hw hs) (uavg_parReadMass_le A hw hs)
  have e1 : (fun θ ↦ ((runtime1R HashOutput HashDomain (tableHwQ θ) m0H).par portQ).evalDistMap
      .instruments (gameQPar A θ) (SubState.basis ()) winObsQ {true}) =
      p1Q (SufCma.serialize A) :=
    funext fun θ ↦ (p1Q_serialize A θ).symm
  have e2 : (fun θ ↦ ((runtimeR m0H).par portQ).evalDistMap .instruments (gameQPar A θ)
      (SubState.basis ()) winObsQ {true}) = p2Q (SufCma.serialize A) :=
    funext fun θ ↦ (p2Q_serialize A θ).symm
  rw [e1, e2, add_assoc] at h
  exact h

include hw hr hs in
/-- **The hybrid with rounds, squared**: `winProb ≤ (√(E p2Q) + hybTermQD q d)²`. -/
theorem winProb_le_hybrid_depth :
    SufCma.winProb xmssRom (SufCma.serialize A) ≤
      (uavg (p2Q (SufCma.serialize A)) ^ (2⁻¹ : ℝ) + hybTermQD q d) ^ 2 :=
  (winProb_eq_uavg_p1Q (SufCma.serialize A)).trans_le (uavg_p1Q_le_depth A hw hr hs)

end Quantum.Qrom.Xmss

end
