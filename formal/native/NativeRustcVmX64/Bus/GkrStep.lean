module

public import NativeRustcVmX64.Bus.GkrStep.Sc
public import NativeRustcVmX64.Bus.GkrStep.Cp
public import NativeRustcVmX64.Code.Vm.BitLength.Names
public import NativeRustcVmX64.Code.Vm.GkrStep.Names
public import NativeRustcVmX64.Code.Vm.MultilinearEvalByOfMultilinearEval.Names
public import NativeRustcVmX64.Code.Vm.PolyEval.Names
public import NativeRustcVmX64.Code.Vm.ProdE.Names
public import NativeRustcVmX64.Code.Vm.SpongeWSqueeze.Names
public import NativeRustcVmX64.Code.Vm.SumcheckOfGkrStep.Names
public import NativeRustcVmX64.Code.Vm.TStateGrind.Names
public import NativeRustcVmX64.Code.Vm.TStateReadScalars.Names
public import NativeRustcVmX64.Code.Vm.TStateSampleChallenges.Names

/-!
# `gkr_step` on x86-64

The prologue, the first grind and the combiner's evaluation of the values (`pre_spec`), the
sumcheck (`sc_spec`), the children (`ch_spec`), their products and the check against the claim
(`pr_spec`), the second grind and the coordinates `y` (`ya_spec`), the new values (`mv_spec`) and
the new point `y ++ xs` (`cp_spec`): `gkrStep_spec`.
-/

namespace NativeRustcVmX64.Bus.GkrStep

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Vm.GkrStep
open NativeRustcVmX64.Transcript NativeRustcVmX64.Sumcheck NativeRustcVmX64.Bus.Gkr
open NativeVm.Model NativeRustcVm.Transcript NativeRustcVm.Bus

public section

variable [Host] {a : DecArea} {s0 : TState} {g0 : GkrStateW} {k : Nat}

/-- **`gkr_step` meets its contract**, given its callees'. -/
theorem gkrStep_spec (hp : Placed code k)
    (hbl : Spec (Labels.label NativeRustcVmX64.Vm.BitLength.entryLabel) BitLengthPre BitLengthPost)
    (hgr : ∀ s, Spec (Labels.label NativeRustcVmX64.Vm.TStateGrind.entryLabel) (GrindPre a s) (GrindPost a s))
    (hsq : ∀ sp, Spec (Labels.label NativeRustcVmX64.Vm.SpongeWSqueeze.entryLabel) (SqueezePre sp) (SqueezePost sp))
    (hpe : Spec (Labels.label NativeRustcVmX64.Vm.PolyEval.entryLabel) PolyEvalPre PolyEvalPost)
    (hsc : ∀ s pt n, Spec (Labels.label NativeRustcVmX64.Vm.SumcheckOfGkrStep.entryLabel) (SumcheckGkrPre a s pt n)
      (SumcheckGkrPost a s pt n))
    (hrs : ∀ s, Spec (Labels.label NativeRustcVmX64.Vm.TStateReadScalars.entryLabel) (ReadScalarsPre a s) (ReadScalarsPost a s))
    (hpr : Spec (Labels.label NativeRustcVmX64.Vm.ProdE.entryLabel) ProdEPre ProdEPost)
    (hsm : ∀ s, Spec (Labels.label NativeRustcVmX64.Vm.TStateSampleChallenges.entryLabel) (SampleChallengesPre a s)
      (SampleChallengesPost a s))
    (hmle : Spec (Labels.label NativeRustcVmX64.Vm.MultilinearEvalByOfMultilinearEval.entryLabel) MleOfMultilinearEvalPre
      MleOfMultilinearEvalPost) :
    Spec (Labels.label NativeRustcVmX64.Vm.GkrStep.entryLabel) (GkrStepPre a s0 g0) (GkrStepPost a s0 g0) := by
  intro m0 h
  unfold NativeRustcVmX64.Vm.GkrStep.entryLabel
  rw [hp.label NativeRustcVmX64.Vm.GkrStep.entry_at]
  exact pre_spec hp h hbl hgr hsq hpe fun _ at5 ↦ sc_spec hp h hsc
    (fun _ _ _ _ _ at9 ↦ ch_spec hp h hrs
      (fun _ _ _ _ _ _ _ _ atp ↦ pr_spec hp h hpr hpe
        (fun _ _ _ _ _ _ att ↦ ya_spec hp h hbl hgr hsm
          (fun _ _ _ aty ↦ mv_spec hp h hmle (fun _ atc ↦ cp_spec hp h atc) aty) att) atp) at9) at5

end

end NativeRustcVmX64.Bus.GkrStep
