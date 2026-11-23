module

public import NativeVm.Equiv.LayoutSpec
public import NativeVm.Equiv.Transcript
public import NativeVm.Model.PublicInput

/-!
# Phase 5: the public input

`Sim.publicInputPhase`: the model's `publicInputPhase` simulates the statement's on the layout read
as the statement's (`LayoutW.toSpec`) and the same digest; the claims are the statement's through
`ColumnClaimW.toSpec`. The public input's halves are `digestHalves`' limbs, each limb's line
evaluated by `toE_multilinearEval`.
-/

@[expose] public section

namespace NativeVm.Equiv

open NativeVm.Model LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile

/-- `Layout.placement`. -/
theorem _root_.NativeVm.Model.LayoutW.placement_toSpec (layout : LayoutW) (column : ℕ) :
    layout.placement column = layout.toSpec.placement column := by
  simp [LayoutW.placement, Verifier.Layout.placement, LayoutW.toSpec, List.getD_eq_getElem?_getD]

/-- **Phase 5** (`publicInputPhase`): the two memory columns' claims. -/
theorem Sim.publicInputPhase (layout : LayoutW) (publicInput : Vector UInt64 4) :
    Sim (Model.publicInputPhase layout publicInput)
      (Verifier.publicInputPhase layout.toSpec publicInput)
      (fun a b ↦ a.toList.map ColumnClaimW.toSpec = b) := by
  unfold Model.publicInputPhase Verifier.publicInputPhase
  refine Sim.bind Sim.sampleChallenge fun c c' hc ↦ Sim.pure ?_
  subst hc
  simp [ColumnClaimW.toSpec, toE_multilinearEval, LayoutW.placement_toSpec, KeccakHash.digestHalves,
    Verifier.memory0, Verifier.memory1]

end NativeVm.Equiv
