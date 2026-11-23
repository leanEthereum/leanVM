module

public import NativeRustcVmX64.Bus.AccumulateSide.Exit
public import NativeRustcVmX64.Code.Vm.AccumulateSide.Names
public import NativeRustcVmX64.Code.Vm.BlockForm.Names
public import NativeRustcVmX64.Code.Vm.EWMul.Names
public import NativeRustcVmX64.Code.Vm.EqEvalFnOfEqAbove.Names
public import NativeRustcVmX64.Code.Vm.Evaluate.Names
public import NativeRustcVmX64.Code.Vm.FormBufAddScaled.Names
public import NativeRustcVmX64.Code.Vm.Memcpy.Names
public import NativeRustcVmX64.Code.Vm.PaddingWeight.Names

/-! # `accumulate_side`: entry-to-return contract (x86-64)

The known and framework loops, initialization, table loop and output epilogue compose without
additional entry assumptions. Callee contracts are discharged by the x86 assembly integration.
-/

namespace NativeRustcVmX64.Bus.AccumulateSide

open NativeRustcX64 NativeRustcVmX64.Transcript NativeRustcVmX64.Vm.AccumulateSide
open NativeVm.Model NativeRustcVm.Bus

public section

variable [Host] {k : Nat}

 theorem accumulateSide_spec (hp : Placed code k)
    (hee : Spec (Labels.label NativeRustcVmX64.Vm.EqEvalFnOfEqAbove.entryLabel) EqEvalFnOfEqAbovePre EqEvalFnOfEqAbovePost)
    (hmul : Spec (Labels.label NativeRustcVmX64.Vm.EWMul.entryLabel) EWMulPre EWMulPost)
    (hmc : Spec (Labels.label NativeRustcVmX64.Vm.Memcpy.entryLabel) MemcpyPre MemcpyPost)
    (hbf : Spec (Labels.label NativeRustcVmX64.Vm.BlockForm.entryLabel) BlockFormPre BlockFormPost)
    (has : ∀ f g, Spec (Labels.label NativeRustcVmX64.Vm.FormBufAddScaled.entryLabel) (FormBufAddScaledPre f g) (FormBufAddScaledPost f g))
    (hpw : Spec (Labels.label NativeRustcVmX64.Vm.PaddingWeight.entryLabel) PaddingWeightPre PaddingWeightPost)
    (hev : ∀ f, Spec (Labels.label NativeRustcVmX64.Vm.Evaluate.entryLabel) (EvaluatePre f) (EvaluatePost f)) :
    ∀ L rows bl Fm SL, Spec (Labels.label NativeRustcVmX64.Vm.AccumulateSide.entryLabel)
      (AccumulateSidePre L rows bl Fm SL) (AccumulateSidePost L rows bl Fm SL) := by
  intro L rows bl Fm SL m0 hpre
  have h := pre_of hpre
  refine Eventually.bind (front hp h hee hmul (lpT L rows bl Fm SL m0 0)) fun st ⟨hpc, hst⟩ ↦ ?_
  obtain ⟨d, pc⟩ := st
  simp only at hpc hst
  subst hpc
  refine Eventually.bind (toTables hp h hmc hst) fun st ⟨hpc, hst⟩ ↦ ?_
  obtain ⟨d, pc⟩ := st
  simp only at hpc hst
  subst hpc
  refine Eventually.bind (tableLoop hp h hee hmul hbf has hpw hev (by have := h.blen; omega) hst)
    fun st ⟨hpc, hst⟩ ↦ ?_
  obtain ⟨d, pc⟩ := st
  simp only at hpc hst
  subst hpc
  exact finish hp h hst

end

end NativeRustcVmX64.Bus.AccumulateSide
