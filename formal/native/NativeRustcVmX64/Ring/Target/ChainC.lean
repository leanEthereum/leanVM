module

public import NativeRustcVmX64.Ring.Target.Wrap
public import NativeRustcVmX64.Code.Vm.EWMul.Names
public import NativeRustcVmX64.Code.Vm.EWSqIter.Names
public import NativeRustcVmX64.Code.Vm.PolyEval.Names

/-!
# `ring_target`: the turns' blocks `b20` to `b27` (x86-64)

Generated from the assembly: each block from its template `t<j>` with the values `v<j>`, its call
(`sqS`, `polyS`, `mulS`), the callee's result the table `E`'s next entry (`Good`).
-/

namespace NativeRustcVmX64.Ring.Target

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Ring NativeVm.Model NativeRustcVm.Ring
open NativeRustcVmX64.Vm.RingTarget

public section

variable {m0 : MachineData} {E : Nat → EW} [Host] {k : Nat}

/-- **The blocks `b20` to `b27`.** -/
theorem chainC (hp : Placed code k) (hpre : RingTargetPre m0)
    (hsq : Spec (Labels.label NativeRustcVmX64.Vm.EWSqIter.entryLabel) EWSqIterPre EWSqIterPost)
    (hpoly : Spec (Labels.label NativeRustcVmX64.Vm.PolyEval.entryLabel) PolyEvalPre PolyEvalPost)
    (hmul : Spec (Labels.label NativeRustcVmX64.Vm.EWMul.entryLabel) EWMulPre EWMulPost) (hG : Good m0 E)
    {st : MachineState} (h : At m0 k NativeRustcVmX64.Vm.RingTarget.b20Offset (rsC m0) t20 (v20 m0 E) (CAt m0) st) :
    Eventually (step1 Host.exe) (At m0 k NativeRustcVmX64.Vm.RingTarget.b28Offset (rsC m0) t28 (v28 m0 E) (CAt m0)) st := by
  refine Eventually.bind (polyS hp hpre hpoly hG b20_in_code (by simp [b20]) rfl (T' := t21)
    (vals' := v21 m0 E) run_b20 rfl rfl rfl rfl rfl rfl rfl (fun m hB ret ↦ by vtac hpre hG hB)
    (fun mc m' hm hs hq ↦ poly_res hm hq hs rfl rfl rfl rfl (hG.pv 2 (by decide)).symm) rfl rfl rfl
    rfl rfl (fun _ _ ↦ keyOk rfl rfl) rfl h) fun st h ↦ ?_
  refine Eventually.bind (sqS hp hpre hsq hG b21_in_code (by simp [b21]) rfl (T' := t22)
    (vals' := v22 m0 E) run_b21 rfl rfl rfl rfl rfl (fun m hB ret ↦ by vtac hpre hG hB)
    (fun mc m' hm hq ↦ sq_res hm hq (by decide) rfl rfl rfl rfl rfl (hG.tv 2 (by decide)).symm) rfl rfl rfl rfl rfl
    (fun _ _ ↦ keyOk rfl rfl) rfl h) fun st h ↦ ?_
  refine Eventually.bind (sqS hp hpre hsq hG b22_in_code (by simp [b22]) rfl (T' := t23)
    (vals' := v23 m0 E) run_b22 rfl rfl rfl rfl rfl (fun m hB ret ↦ by vtac hpre hG hB)
    (fun mc m' hm hq ↦ sq_res hm hq (by decide) rfl rfl rfl rfl rfl (hG.z 6 (by decide) (by decide)).symm) rfl rfl rfl rfl rfl
    (fun _ _ ↦ keyOk rfl rfl) rfl h) fun st h ↦ ?_
  refine Eventually.bind (polyS hp hpre hpoly hG b23_in_code (by simp [b23]) rfl (T' := t24)
    (vals' := v24 m0 E) run_b23 rfl rfl rfl rfl rfl rfl rfl (fun m hB ret ↦ by vtac hpre hG hB)
    (fun mc m' hm hs hq ↦ poly_res hm hq hs rfl rfl rfl rfl (hG.pv 1 (by decide)).symm) rfl rfl rfl
    rfl rfl (fun _ _ ↦ keyOk rfl rfl) rfl h) fun st h ↦ ?_
  refine Eventually.bind (sqS hp hpre hsq hG b24_in_code (by simp [b24]) rfl (T' := t25)
    (vals' := v25 m0 E) run_b24 rfl rfl rfl rfl rfl (fun m hB ret ↦ by vtac hpre hG hB)
    (fun mc m' hm hq ↦ sq_res hm hq (by decide) rfl rfl rfl rfl rfl (hG.tv 1 (by decide)).symm) rfl rfl rfl rfl rfl
    (fun _ _ ↦ keyOk rfl rfl) rfl h) fun st h ↦ ?_
  refine Eventually.bind (sqS hp hpre hsq hG b25_in_code (by simp [b25]) rfl (T' := t26)
    (vals' := v26 m0 E) run_b25 rfl rfl rfl rfl rfl (fun m hB ret ↦ by vtac hpre hG hB)
    (fun mc m' hm hq ↦ sq_res hm hq (by decide) rfl rfl rfl rfl rfl (hG.z 7 (by decide) (by decide)).symm) rfl rfl rfl rfl rfl
    (fun _ _ ↦ keyOk rfl rfl) rfl h) fun st h ↦ ?_
  refine Eventually.bind (mulS hp hpre hmul hG b26_in_code (by simp [b26]) rfl (T' := t27)
    (vals' := v27 m0 E) run_b26 rfl rfl rfl rfl rfl (fun m hB ret ↦ by vtac hpre hG hB)
    (fun mc m' hm hq ↦ mul_res hm hq rfl rfl rfl rfl rfl rfl rfl rfl (hG.mv 1 (by decide)).symm)
    rfl rfl rfl rfl rfl (fun _ _ ↦ keyOk rfl rfl) rfl h) fun st h ↦ ?_
  refine Eventually.bind (mulS hp hpre hmul hG b27_in_code (by simp [b27]) rfl (T' := t28)
    (vals' := v28 m0 E) run_b27 rfl rfl rfl rfl rfl (fun m hB ret ↦ by vtac hpre hG hB)
    (fun mc m' hm hq ↦ mul_res hm hq rfl rfl rfl rfl rfl rfl rfl rfl (hG.mv 2 (by decide)).symm)
    rfl rfl rfl rfl rfl (fun _ _ ↦ keyOk rfl rfl) rfl h) fun st h ↦ ?_
  exact .done _ h

end

end NativeRustcVmX64.Ring.Target
