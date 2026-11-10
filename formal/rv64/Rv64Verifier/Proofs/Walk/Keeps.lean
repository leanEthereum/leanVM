import Rv64Verifier.Proofs.Walk.AtR17
import Rv64Verifier.Proofs.Pcs.VsoKeeps

/-!
# The phases after the bus keep the transcript's proof and roots

`Model.Pcs.Keeps`: the table sumcheck, the public input, `verify_keccak`, `ring_switch` and
`verify_bus_balance` keep the proof, the roots and the opening offset.
-/

namespace Rv64Verifier.Proofs.Walk
open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Verifier Rv64Verifier.Model
open Rv64Verifier.Model.Pcs (Keeps)

/-! ## The transcript's checks and loops -/

theorem keeps_streamPosition : Keeps TM.streamPosition := by
  intro t a t' h
  cases h
  exact ⟨rfl, rfl, rfl⟩

theorem keeps_fail {α : Type} : Keeps (TM.fail : TM α) := by
  intro t a t' h
  cases h

theorem keeps_ofOption {α : Type} (o : Option α) : Keeps (TM.ofOption o) := by
  cases o
  · exact keeps_fail
  · exact Keeps.pure _

theorem keeps_require (c : Prop) [Decidable c] : Keeps (TM.require c) := by
  intro t a t' h
  simp only [TM.require, StateT.run] at h
  split_ifs at h
  cases h
  exact ⟨rfl, rfl, rfl⟩

theorem keeps_ite {α : Type} {c : Prop} {_ : Decidable c} {a b : TM α} (ha : Keeps a)
    (hb : Keeps b) : Keeps (if c then a else b) := by
  split
  · exact ha
  · exact hb

/-- A `for` loop of keeping steps keeps. -/
theorem keeps_foldlM {α β : Type} {f : β → α → TM β} (hf : ∀ b a, Keeps (f b a)) :
    ∀ (l : List α) (init : β), Keeps (l.foldlM f init)
  | [], _ => Keeps.pure _
  | a :: l, init => by
    rw [List.foldlM_cons]
    exact Keeps.bind (hf init a) fun b ↦ keeps_foldlM hf l b

theorem keeps_sumcheckRound (count : ℕ) (acc : List E × E) (equality : Option E) :
    Keeps (TM.sumcheckRound count acc equality) :=
  Keeps.bind (Keeps.roundPoly _ _ _) fun _ ↦ Keeps.bind Keeps.sample fun _ ↦ Keeps.pure _

theorem keeps_sumcheck (claim : E) (count : ℕ) (equalities : List (Option E)) :
    Keeps (TM.sumcheck claim count equalities) :=
  keeps_foldlM (fun acc e ↦ keeps_sumcheckRound count acc e) _ _

/-! ## The table sumcheck and the public input -/

theorem keeps_readRowsM (point : List E) :
    ∀ (l : List (Table × ℕ)) (rows : List (List E × List E)), Keeps (readRowsM point l rows)
  | [], _ => Keeps.pure _
  | (_, _) :: rest, _ => Keeps.bind (Keeps.nextScalars _) fun _ ↦ keeps_readRowsM point rest _

/-- `table_sumcheck` keeps the proof, the roots and the opening offset. -/
theorem keeps_tableSumcheckM (tablesL : List Table) (heights : List ℕ)
    (busForms : List (List Form)) (constraintPowers formPowers equalityPoint : List E)
    (target : E) :
    Keeps (tableSumcheckM tablesL heights busForms constraintPowers formPowers equalityPoint
      target) := by
  unfold tableSumcheckM
  refine Keeps.bind (keeps_sumcheck _ _ _) fun ⟨_, _⟩ ↦ ?_
  exact Keeps.bind (keeps_readRowsM _ _ _) fun _ ↦ Keeps.bind (keeps_require _) fun _ ↦
    Keeps.pure _

/-- `walk`'s table phase keeps the proof, the roots and the opening offset. -/
theorem keeps_tablePhaseRust (layout : LayoutMirror.LayoutRust) (bus : BusResultRust) :
    Keeps (tablePhaseRust layout bus) :=
  Keeps.bind Keeps.sample fun _ ↦ keeps_tableSumcheckM _ _ _ _ _ _ _

/-- `walk`'s public-input phase keeps the proof, the roots and the opening offset. -/
theorem keeps_publicInputRust (layout : LayoutMirror.LayoutRust) (publicInput : List (BitVec 8)) :
    Keeps (publicInputRust layout publicInput) :=
  Keeps.bind Keeps.sample fun _ ↦ Keeps.bind (keeps_ofOption _) fun _ ↦
    Keeps.bind (keeps_ofOption _) fun _ ↦ Keeps.bind (keeps_ofOption _) fun _ ↦
      Keeps.bind (keeps_ofOption _) fun _ ↦ Keeps.pure _

/-! ## `verify_keccak` -/

theorem keeps_packRound (acc : E × E × List E) (r : E) : Keeps (Gkr.packRound acc r) :=
  Keeps.bind (Keeps.roundPoly _ _ _) fun _ ↦ Keeps.bind Keeps.sample fun _ ↦ Keeps.pure _

theorem keeps_verifyLayerRust (shape : Gkr.KeccakShape) (step : ℕ) (claim : KeccakClaim) :
    Keeps (Gkr.verifyLayerRust shape step claim) := by
  unfold Gkr.verifyLayerRust
  refine Keeps.bind (Keeps.nextScalars _) fun _ ↦ Keeps.bind (keeps_require _) fun _ ↦
    Keeps.bind Keeps.sample fun _ ↦ ?_
  refine Keeps.bind (keeps_foldlM (fun acc r ↦ keeps_packRound acc r) _ _) fun ⟨_, _, _⟩ ↦ ?_
  refine Keeps.bind (keeps_sumcheck _ _ _) fun ⟨_, _⟩ ↦ ?_
  exact Keeps.bind (Keeps.nextScalars _) fun _ ↦ Keeps.bind (keeps_require _) fun _ ↦
    Keeps.bind Keeps.sample fun _ ↦ Keeps.pure _

theorem keeps_openRust (shape : Gkr.KeccakShape) (claim : KeccakClaim) (first count : ℕ)
    (value : E) : Keeps (Gkr.openRust shape claim first count value) := by
  unfold Gkr.openRust
  exact Keeps.bind (keeps_sumcheck _ _ _) fun ⟨_, _⟩ ↦ Keeps.pure _

/-- `verify_keccak` keeps the proof, the roots and the opening offset. -/
theorem keeps_verifyKeccakRust (shape : Gkr.KeccakShape) (inst output : List E) :
    Keeps (Gkr.verifyKeccakRust shape inst output) := by
  unfold Gkr.verifyKeccakRust
  refine Keeps.bind (keeps_require _) fun _ ↦ Keeps.bind (Keeps.samples _) fun _ ↦
    Keeps.bind (Keeps.samples _) fun _ ↦ ?_
  dsimp only
  split <;> refine Keeps.bind (by first | exact Keeps.nextScalar | exact Keeps.pure _) fun _ ↦ ?_
  all_goals
    refine Keeps.bind (keeps_verifyLayerRust _ _ _) fun _ ↦ ?_
    refine Keeps.bind (keeps_foldlM (fun c s ↦ keeps_verifyLayerRust _ s c) _ _) fun _ ↦ ?_
  all_goals first
    | refine Keeps.bind (keeps_openRust _ _ _ _ _) fun ⟨_, _, _⟩ ↦ Keeps.bind Keeps.nextScalar
        fun _ ↦ Keeps.bind (keeps_require _) fun _ ↦ Keeps.bind (Keeps.pure _) fun _ ↦ ?_
    | refine Keeps.bind (Keeps.pure _) fun _ ↦ ?_
  all_goals
    refine Keeps.bind (keeps_sumcheck _ _ _) fun ⟨_, _⟩ ↦ ?_
    refine Keeps.bind (keeps_openRust _ _ _ _ _) fun ⟨_, _, _⟩ ↦ ?_
    exact Keeps.bind (Keeps.nextScalars _) fun _ ↦ Keeps.bind (keeps_ofOption _) fun _ ↦
      Keeps.bind (keeps_require _) fun _ ↦ Keeps.pure _

/-- `walk`'s `KECCAK` phase keeps the proof, the roots and the opening offset. -/
theorem keeps_keccakPhaseRust (layout : LayoutMirror.LayoutRust)
    (evaluations : List (List E × List E)) : Keeps (keccakPhaseRust layout evaluations) :=
  Keeps.bind (keeps_ofOption _) fun _ ↦ Keeps.bind keeps_streamPosition fun _ ↦
    Keeps.bind (keeps_ofOption _) fun _ ↦ Keeps.bind (keeps_verifyKeccakRust _ _ _) fun _ ↦
      Keeps.bind keeps_streamPosition fun _ ↦ Keeps.pure _

/-! ## `ring_switch` and `verify_bus_balance` -/

/-- `ring_switch` keeps the proof, the roots and the opening offset. -/
theorem keeps_ringSwitchRust (point s : List E) : Keeps (Pcs.ringSwitchRust point s) :=
  Keeps.bind (Keeps.samples _) fun _ ↦ Keeps.pure _

theorem keeps_gkrStepM (step : ℕ) (state : GkrState) : Keeps (gkrStepM step state) := by
  unfold gkrStepM
  refine Keeps.bind Keeps.sample fun _ ↦ Keeps.bind (keeps_sumcheck _ _ _) fun ⟨_, _⟩ ↦ ?_
  exact Keeps.bind (Keeps.nextScalars _) fun _ ↦ Keeps.bind (Keeps.nextScalars _) fun _ ↦
    Keeps.bind (Keeps.nextScalars _) fun _ ↦ Keeps.bind (keeps_require _) fun _ ↦
      Keeps.bind (Keeps.samples _) fun _ ↦ Keeps.bind (keeps_ofOption _) fun _ ↦ Keeps.pure _

theorem keeps_gkrLoopM : ∀ (layer : ℕ) (state : GkrState), Keeps (gkrLoopM layer state)
  | layer, state => by
    rw [gkrLoopM]
    split
    · exact Keeps.bind (keeps_gkrStepM _ _) fun s ↦ keeps_gkrLoopM _ s
    · exact Keeps.pure _
termination_by layer => layer
decreasing_by split <;> omega

theorem keeps_verifyGkrM (depth : ℕ) : Keeps (verifyGkrM depth) :=
  Keeps.bind Keeps.nextScalar fun _ ↦ Keeps.bind Keeps.nextScalar fun _ ↦
    Keeps.bind (keeps_gkrLoopM _ _) fun _ ↦ Keeps.pure _

/-- `verify_bus_balance` keeps the proof, the roots and the opening offset. -/
theorem keeps_verifyBusBalanceM (bytecodeEvaluate : List E → Option E) (layout : Layout) :
    Keeps (verifyBusBalanceM bytecodeEvaluate layout) := by
  unfold verifyBusBalanceM
  refine Keeps.bind (Keeps.samples _) fun _ ↦ Keeps.bind Keeps.sample fun _ ↦ ?_
  refine Keeps.bind (keeps_verifyGkrM _) fun ⟨_, _, _⟩ ↦ ?_
  exact Keeps.bind (keeps_require _) fun _ ↦ Keeps.bind (Keeps.nextScalars _) fun _ ↦
    Keeps.bind Keeps.nextScalar fun _ ↦ Keeps.bind Keeps.nextScalar fun _ ↦
      Keeps.bind (keeps_ofOption _) fun _ ↦ Keeps.pure _

end Rv64Verifier.Proofs.Walk

/-- info: 'Rv64Verifier.Proofs.Walk.keeps_streamPosition' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Walk.keeps_streamPosition

/-- info: 'Rv64Verifier.Proofs.Walk.keeps_fail' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Walk.keeps_fail

/-- info: 'Rv64Verifier.Proofs.Walk.keeps_ofOption' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Walk.keeps_ofOption

/-- info: 'Rv64Verifier.Proofs.Walk.keeps_require' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Walk.keeps_require

/-- info: 'Rv64Verifier.Proofs.Walk.keeps_foldlM' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Walk.keeps_foldlM

/-- info: 'Rv64Verifier.Proofs.Walk.keeps_tableSumcheckM' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Walk.keeps_tableSumcheckM

/-- info: 'Rv64Verifier.Proofs.Walk.keeps_tablePhaseRust' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Walk.keeps_tablePhaseRust

/-- info: 'Rv64Verifier.Proofs.Walk.keeps_publicInputRust' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Walk.keeps_publicInputRust

/-- info: 'Rv64Verifier.Proofs.Walk.keeps_verifyKeccakRust' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Walk.keeps_verifyKeccakRust

/-- info: 'Rv64Verifier.Proofs.Walk.keeps_keccakPhaseRust' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Walk.keeps_keccakPhaseRust

/-- info: 'Rv64Verifier.Proofs.Walk.keeps_ringSwitchRust' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Walk.keeps_ringSwitchRust

/-- info: 'Rv64Verifier.Proofs.Walk.keeps_verifyBusBalanceM' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Walk.keeps_verifyBusBalanceM
