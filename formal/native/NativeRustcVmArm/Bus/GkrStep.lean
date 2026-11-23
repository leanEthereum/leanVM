module

public import NativeRustcVmArm.Code.Vm.BitLength.Names
public import NativeRustcVmArm.Code.Vm.GkrStep.Names
public import NativeRustcVmArm.Code.Vm.MultilinearEvalByOfMultilinearEval.Names
public import NativeRustcVmArm.Code.Vm.PolyEval.Names
public import NativeRustcVmArm.Code.Vm.ProdE.Names
public import NativeRustcVmArm.Code.Vm.SpongeWSqueeze.Names
public import NativeRustcVmArm.Code.Vm.SumcheckOfGkrStep.Names
public import NativeRustcVmArm.Code.Vm.TStateGrind.Names
public import NativeRustcVmArm.Code.Vm.TStateReadScalars.Names
public import NativeRustcVmArm.Code.Vm.TStateSampleChallenges.Names
public import NativeRustcVmArm.Bus.GkrStep.Head
public import NativeRustcVmArm.Bus.GkrStep.Finish

/-!
# `gkr_step`

The parts in order (`GkrStep/*`): `Head` (the prologue, the first grind, the combiner, its
evaluation of the values, the sumcheck: `AtChildren`), `Children` (the three children read:
`AtProds`), `Prods` (their products checked against the claim: `AtTail`), `Tail` (the second
grind, the coordinates `y`: `AtEval`), `Values` (the new values, the point's length and `y`:
`AtCopy`), `Finish` (the challenges copied after `y`, X0 = `1`). `gkrStep_spec`.
-/

namespace NativeRustcVmArm.Bus.GkrStep

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.GkrStep
open NativeVm.Model NativeRustcVmArm.Ring NativeRustcVm.Transcript NativeRustcVm.Bus

public section
variable [Host] {a : DecArea} {s0 : TState} {g0 : GkrStateW} {k : Nat}

/-- **`gkr_step`'s contract.** -/
theorem gkrStep_spec (hp : Placed code k)
    (hbl : Spec (Labels.label NativeRustcVmArm.Vm.BitLength.entryLabel) BitLengthPre BitLengthPost)
    (hgr : ∀ s, Spec (Labels.label NativeRustcVmArm.Vm.TStateGrind.entryLabel) (GrindPre a s) (GrindPost a s))
    (hsq : ∀ sp, Spec (Labels.label NativeRustcVmArm.Vm.SpongeWSqueeze.entryLabel) (SqueezePre sp) (SqueezePost sp))
    (hpe : Spec (Labels.label NativeRustcVmArm.Vm.PolyEval.entryLabel) PolyEvalPre PolyEvalPost)
    (hsc : ∀ s pt n, Spec (Labels.label NativeRustcVmArm.Vm.SumcheckOfGkrStep.entryLabel) (SumcheckGkrPre a s pt n)
      (SumcheckGkrPost a s pt n))
    (hrs : ∀ s, Spec (Labels.label NativeRustcVmArm.Vm.TStateReadScalars.entryLabel) (ReadScalarsPre a s) (ReadScalarsPost a s))
    (hpr : Spec (Labels.label NativeRustcVmArm.Vm.ProdE.entryLabel) ProdEPre ProdEPost)
    (hsm : ∀ s, Spec (Labels.label NativeRustcVmArm.Vm.TStateSampleChallenges.entryLabel) (SampleChallengesPre a s)
      (SampleChallengesPost a s))
    (hmle : Spec (Labels.label NativeRustcVmArm.Vm.MultilinearEvalByOfMultilinearEval.entryLabel) MleOfMultilinearEvalPre
      MleOfMultilinearEvalPost) :
    Spec (Labels.label NativeRustcVmArm.Vm.GkrStep.entryLabel) (GkrStepPre a s0 g0) (GkrStepPost a s0 g0) := by
  intro m0 h
  rw [show Labels.label NativeRustcVmArm.Vm.GkrStep.entryLabel = Host.addrOf (k + NativeRustcVmArm.Vm.GkrStep.b0Offset) from hp.label (j := NativeRustcVmArm.Vm.GkrStep.entryOffset) NativeRustcVmArm.Vm.GkrStep.entry_at]
  exact head_spec hp h hbl hgr hsq hpe hsc fun _ _ _ _ _ hi ↦
    reads_spec hp h hrs (fun _ _ _ _ _ hj ↦ prods_spec hp h hpr hpe
      (fun _ hk ↦ coords_spec hp h hbl hgr hsm
        (fun _ _ _ hl ↦ eval_spec hp h hmle (fun _ hc ↦ copy_spec hp h hc) hl) hk) hj) hi

end

end NativeRustcVmArm.Bus.GkrStep
