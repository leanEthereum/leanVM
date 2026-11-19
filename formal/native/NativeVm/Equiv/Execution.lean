module

public import NativeVm.Equiv.Layout
public import NativeVm.Equiv.Stack
public import NativeVm.Equiv.Bus
public import NativeVm.Equiv.Tables
public import NativeVm.Equiv.TablesPure
public import NativeVm.Equiv.PublicInput
public import NativeVm.Equiv.KeccakGkr
public import NativeVm.Equiv.RingSwitch
public import NativeVm.Equiv.Whir
public import NativeVm.Equiv.Claims
public import NativeVm.Equiv.Verify
public import Mathlib.Data.List.Forall2

/-!
# The walk, and the model's verifier

`Sim.verifyExecution`: the model's walk simulates `verifyExecution computedBytecodeValue`, the
seven phases' simulations composed in order (`Sim.bind`), the column claims carried through
`ColumnClaimW.toSpec`, and the stacked opening's claims related one by one (the ring-switched
claim, every column claim with a placement, the out-of-domain claim). With it, `verify_eq`:
the model's verifier is `verifyWith keccakF1600`, with no hypothesis.
-/

@[expose] public section

namespace NativeVm.Equiv

open NativeVm.Model LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.Protocol.Verifier

attribute [local irreducible] keccakF1600

/-- The claims with a placement, on the stack, are the statement's. -/
theorem forall₂_filterMap_onStack (layout : LayoutW) : ∀ l : List ColumnClaimW,
    List.Forall₂ StackClaimW.Rel (l.filterMap (·.onStack layout))
      ((l.map ColumnClaimW.toSpec).filterMap (·.onStack layout.toSpec))
  | [] => .nil
  | c :: l => by
    have ih := forall₂_filterMap_onStack layout l
    have h := c.onStack_toSpec layout
    simp only [List.map_cons, List.filterMap_cons]
    revert h
    generalize c.onStack layout = x
    generalize c.toSpec.onStack layout.toSpec = y
    rintro (h | _)
    · exact .cons h ih
    · exact ih

/-- **The walk**: the model's `verifyExecution` simulates the statement's, with the deployed
bytecode check. -/
theorem Sim.verifyExecution (bytecode : Array UInt64) (publicInput : Vector UInt64 4) :
    Sim (Model.verifyExecution bytecode publicInput)
      (Verifier.verifyExecution Verifier.computedBytecodeValue (bytecode.toList.map K.ofLane)
        publicInput)
      fun _ _ ↦ True := by
  unfold Model.verifyExecution Verifier.verifyExecution
  refine Sim.bind (Sim.readAnnouncedSizes bytecode) fun ⟨layout, rate⟩ ⟨layout', rate'⟩ h ↦ ?_
  obtain ⟨rfl, rfl⟩ := h
  refine Sim.bind (Sim.commitStack layout.stackLog rate) fun _ _ _ ↦ ?_
  refine Sim.bind (Sim.readOod layout.stackLog) fun ood ood' hood ↦ ?_
  refine Sim.bind (Sim.verifyBusBalance layout) fun bus bus' hbus ↦ ?_
  subst hbus
  refine Sim.bind (Sim.tablePhase layout bus) fun ev ev' hev ↦ ?_
  refine Sim.bind (Sim.publicInputPhase layout publicInput) fun pc pc' hpc ↦ ?_
  refine Sim.bind (Keccak.sim_keccakPhase layout ev ev' hev) fun ⟨outs, kp, ks⟩ ⟨outs', kp', ks'⟩
    hk ↦ ?_
  obtain ⟨ho, hkp, hks⟩ := hk
  refine Sim.bind (Sim.ringSwitch hkp hks) fun ⟨t, rp, co⟩ ⟨t', w'⟩ hrs ↦ ?_
  refine Sim.verifyStackedOpening layout.stackLog rate ?_
  have hclaims : (bus.claims ++ tableColumnClaims ev ++ pc ++ outs).toList.map ColumnClaimW.toSpec =
      bus.toSpec.claims ++ Verifier.tableColumnClaims ev' ++ pc' ++ outs' := by
    simp only [Array.toList_append, List.map_append, tableColumnClaims_toSpec, hev, hpc, ho,
      BusResultW.toSpec]
  have hfm := forall₂_filterMap_onStack layout (bus.claims ++ tableColumnClaims ev ++ pc ++ outs).toList
  rw [hclaims, ← Array.toList_filterMap] at hfm
  have hl : (#[Model.ringSwitchClaim layout t rp co] ++
      Array.filterMap (fun x ↦ x.onStack layout) (bus.claims ++ tableColumnClaims ev ++ pc ++ outs) ++
        #[ood]).toList = Model.ringSwitchClaim layout t rp co ::
      ((Array.filterMap (fun x ↦ x.onStack layout)
        (bus.claims ++ tableColumnClaims ev ++ pc ++ outs)).toList ++ [ood]) := by
    simp only [Array.toList_append, List.cons_append, List.nil_append]
  rw [hl]
  dsimp only
  have hr := ringSwitchClaim_rel layout hrs
  dsimp only at hr
  exact .cons hr (List.rel_append hfm (.cons hood .nil))

/-- **The model's verifier is the statement's**: `Model.verify` of the bytecode, the public input,
the decoded stream and openings is `verifyWith keccakF1600` of the bytecode's `K` words, the public
input and the proof they denote. -/
theorem verify_eq (bytecode : Array UInt64) (publicInput : Vector UInt64 4) (stream : Array EW)
    (openings : Array (Array OpeningW)) :
    Model.verify bytecode publicInput stream openings =
      Id.run (verifyWith (m := Id) keccakF1600 (bytecode.toList.map K.ofLane) publicInput
        ⟨stream.toList.map EW.toE, openings.toList.map phaseOpenings⟩) :=
  verify_eq_of_sim bytecode publicInput stream openings (Sim.verifyExecution bytecode publicInput)

end NativeVm.Equiv
