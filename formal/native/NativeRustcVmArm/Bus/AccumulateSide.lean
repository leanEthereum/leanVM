module

public import NativeRustcVmArm.Code.Vm.AccumulateSide.Names
public import NativeRustcVmArm.Code.Vm.BlockForm.Names
public import NativeRustcVmArm.Code.Vm.EWMul.Names
public import NativeRustcVmArm.Code.Vm.EqEvalFnOfEqAbove.Names
public import NativeRustcVmArm.Code.Vm.Evaluate.Names
public import NativeRustcVmArm.Code.Vm.FormBufAddScaled.Names
public import NativeRustcVmArm.Code.Vm.Memcpy.Names
public import NativeRustcVmArm.Code.Vm.PaddingWeight.Names
public import NativeRustcVmArm.Bus.AccumulateSide.Start
public import NativeRustcVmArm.Bus.AccumulateSide.Body

/-!
# `accumulate_side` on AArch64

The entry computes the framework's known part and selectors, the table loop updates the forms and padding sum, and the epilogue writes the result and restores the caller's frame.
-/

namespace NativeRustcVmArm.Bus.AccumulateSide

open NativeRustcArm NativeRustcVmArm.Vm.AccumulateSide
open NativeVm.Model NativeRustcVmArm.Ring NativeRustcVm.Bus NativeRustcVm.Layout

public section

variable [Host] {k : Nat}

/-- The complete rustc-generated function meets its contract. -/
theorem accumulateSide_spec (hp : Placed code k)
    (hee : Spec (Labels.label NativeRustcVmArm.Vm.EqEvalFnOfEqAbove.entryLabel) EqEvalFnOfEqAbovePre EqEvalFnOfEqAbovePost)
    (hmul : Spec (Labels.label NativeRustcVmArm.Vm.EWMul.entryLabel) EWMulPre EWMulPost)
    (hmc : Spec (Labels.label NativeRustcVmArm.Vm.Memcpy.entryLabel) MemcpyPre MemcpyPost)
    (hbf : Spec (Labels.label NativeRustcVmArm.Vm.BlockForm.entryLabel) BlockFormPre BlockFormPost)
    (has : ∀ f g, Spec (Labels.label NativeRustcVmArm.Vm.FormBufAddScaled.entryLabel) (FormBufAddScaledPre f g) (FormBufAddScaledPost f g))
    (hpw : Spec (Labels.label NativeRustcVmArm.Vm.PaddingWeight.entryLabel) PaddingWeightPre PaddingWeightPost)
    (hev : ∀ f, Spec (Labels.label NativeRustcVmArm.Vm.Evaluate.entryLabel) (EvaluatePre f) (EvaluatePost f))
    {L : LayoutW} {rows : Array Nat} {bl : List NativeRustcVm.Data.Block}
    {Fm : Array (Array FormW)} {SL : BusLayoutW} :
    Spec (Labels.label NativeRustcVmArm.Vm.AccumulateSide.entryLabel) (AccumulateSidePre L rows bl Fm SL)
      (AccumulateSidePost L rows bl Fm SL) := by
  intro m0 hpre
  have he : Labels.label NativeRustcVmArm.Vm.AccumulateSide.entryLabel = Host.addrOf (k + NativeRustcVmArm.Vm.AccumulateSide.b0Offset) := hp.label (j := NativeRustcVmArm.Vm.AccumulateSide.entryOffset) NativeRustcVmArm.Vm.AccumulateSide.entry_at
  rw [he]
  have h := pre_of hpre
  exact start_spec hp h hee hmul hmc fun _ hs hf ↦ body_spec hp h hee hbf has hpw hmul hev hs hf

end

end NativeRustcVmArm.Bus.AccumulateSide
