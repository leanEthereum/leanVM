module

public import NativeRustcVmX64.Ring.Target.Wrap
public import NativeRustcVmX64.Code.Vm.EWMul.Names
public import NativeRustcVmX64.Code.Vm.EWSqIter.Names
public import NativeRustcVmX64.Code.Vm.PolyEval.Names

/-!
# `ring_target`: the turns' blocks `b28` to `b35` (x86-64)

Generated from the assembly: each block from its template `t<j>` with the values `v<j>`, its call
(`sqS`, `polyS`, `mulS`), the callee's result the table `E`'s next entry (`Good`).
-/

namespace NativeRustcVmX64.Ring.Target

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Ring NativeVm.Model NativeRustcVm.Ring
open NativeRustcVmX64.Vm.RingTarget

public section

variable {m0 : MachineData} {E : Nat → EW} [Host] {k : Nat}

/-- **The blocks `b28` to `b35`.** -/
theorem chainD (hp : Placed code k) (hpre : RingTargetPre m0)
    (hsq : Spec (Labels.label NativeRustcVmX64.Vm.EWSqIter.entryLabel) EWSqIterPre EWSqIterPost)
    (hpoly : Spec (Labels.label NativeRustcVmX64.Vm.PolyEval.entryLabel) PolyEvalPre PolyEvalPost)
    (hmul : Spec (Labels.label NativeRustcVmX64.Vm.EWMul.entryLabel) EWMulPre EWMulPost) (hG : Good m0 E)
    {st : MachineState} (h : At m0 k NativeRustcVmX64.Vm.RingTarget.b28Offset (rsC m0) t28 (v28 m0 E) (CAt m0) st) :
    Eventually (step1 Host.exe) (At m0 k NativeRustcVmX64.Vm.RingTarget.b36Offset (rsC m0) t36 (v36 m0 E) (CAt m0)) st := by
  refine Eventually.bind (mulS hp hpre hmul hG b28_in_code (by simp [b28]) rfl (T' := t29)
    (vals' := v29 m0 E) run_b28 rfl rfl rfl rfl rfl (fun m hB ret ↦ by vtac hpre hG hB)
    (fun mc m' hm hq ↦ mul_res hm hq rfl rfl rfl rfl rfl rfl rfl rfl (hG.mv 3 (by decide)).symm)
    rfl rfl rfl rfl rfl (fun _ _ ↦ keyOk rfl rfl) rfl h) fun st h ↦ ?_
  refine Eventually.bind (mulS hp hpre hmul hG b29_in_code (by simp [b29]) rfl (T' := t30)
    (vals' := v30 m0 E) run_b29 rfl rfl rfl rfl rfl (fun m hB ret ↦ by vtac hpre hG hB)
    (fun mc m' hm hq ↦ mul_res hm hq rfl rfl rfl rfl rfl rfl rfl rfl (hG.mv 4 (by decide)).symm)
    rfl rfl rfl rfl rfl (fun _ _ ↦ keyOk rfl rfl) rfl h) fun st h ↦ ?_
  refine Eventually.bind (mulS hp hpre hmul hG b30_in_code (by simp [b30]) rfl (T' := t31)
    (vals' := v31 m0 E) run_b30 rfl rfl rfl rfl rfl (fun m hB ret ↦ by vtac hpre hG hB)
    (fun mc m' hm hq ↦ mul_res hm hq rfl rfl rfl rfl rfl rfl rfl rfl (hG.mv 5 (by decide)).symm)
    rfl rfl rfl rfl rfl (fun _ _ ↦ keyOk rfl rfl) rfl h) fun st h ↦ ?_
  refine Eventually.bind (mulS hp hpre hmul hG b31_in_code (by simp [b31]) rfl (T' := t32)
    (vals' := v32 m0 E) run_b31 rfl rfl rfl rfl rfl (fun m hB ret ↦ by vtac hpre hG hB)
    (fun mc m' hm hq ↦ mul_res hm hq rfl rfl rfl rfl rfl rfl rfl rfl (hG.mv 6 (by decide)).symm)
    rfl rfl rfl rfl rfl (fun _ _ ↦ keyOk rfl rfl) rfl h) fun st h ↦ ?_
  refine Eventually.bind (mulS hp hpre hmul hG b32_in_code (by simp [b32]) rfl (T' := t33)
    (vals' := v33 m0 E) run_b32 rfl rfl rfl rfl rfl (fun m hB ret ↦ by vtac hpre hG hB)
    (fun mc m' hm hq ↦ mul_res hm hq rfl rfl rfl rfl rfl rfl rfl rfl (hG.mv 7 (by decide)).symm)
    rfl rfl rfl rfl rfl (fun _ _ ↦ keyOk rfl rfl) rfl h) fun st h ↦ ?_
  refine Eventually.bind (polyS hp hpre hpoly hG b33_in_code (by simp [b33]) rfl (T' := t34)
    (vals' := v34 m0 E) run_b33 rfl rfl rfl rfl rfl rfl rfl (fun m hB ret ↦ by vtac hpre hG hB)
    (fun mc m' hm hs hq ↦ poly_res hm hq hs rfl rfl rfl rfl (hG.pv 0 (by decide)).symm) rfl rfl rfl
    rfl rfl (fun _ _ ↦ noKeys rfl) rfl h) fun st h ↦ ?_
  refine Eventually.bind (sqS hp hpre hsq hG b34_in_code (by simp [b34]) rfl (T' := t35)
    (vals' := v35 m0 E) run_b34 rfl rfl rfl rfl rfl (fun m hB ret ↦ by vtac hpre hG hB)
    (fun mc m' hm hq ↦ sq_res hm hq (by decide) rfl rfl rfl rfl rfl (hG.tv 0 (by decide)).symm) rfl rfl rfl rfl rfl
    (fun _ _ ↦ noKeys rfl) rfl h) fun st h ↦ ?_
  refine Eventually.bind (mulS hp hpre hmul hG b35_in_code (by simp [b35]) rfl (T' := t36)
    (vals' := v36 m0 E) run_b35 rfl rfl rfl rfl rfl (fun m hB ret ↦ by vtac hpre hG hB)
    (fun mc m' hm hq ↦ mul_res hm hq rfl rfl rfl rfl rfl rfl rfl rfl (hG.mv 0 (by decide)).symm)
    rfl rfl rfl rfl rfl (fun _ _ ↦ noKeys rfl) rfl h) fun st h ↦ ?_
  exact .done _ h

end

end NativeRustcVmX64.Ring.Target
