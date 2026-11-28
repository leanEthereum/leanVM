module

public import NativeRustcVmX64.Ring.Target.Wrap
public import NativeRustcVmX64.Code.Vm.EWMul.Names
public import NativeRustcVmX64.Code.Vm.EWSqIter.Names
public import NativeRustcVmX64.Code.Vm.PolyEval.Names

/-!
# `ring_target`: the turns' blocks `b12` to `b19` (x86-64)

Generated from the assembly: each block from its template `t<j>` with the values `v<j>`, its call
(`sqS`, `polyS`, `mulS`), the callee's result the table `E`'s next entry (`Good`).
-/

namespace NativeRustcVmX64.Ring.Target

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Ring NativeVm.Model NativeRustcVm.Ring
open NativeRustcVmX64.Vm.RingTarget

public section

variable {m0 : MachineData} {E : Nat → EW} [Host] {k : Nat}

/-- **The blocks `b12` to `b19`.** -/
theorem chainB (hp : Placed code k) (hpre : RingTargetPre m0)
    (hsq : Spec (Labels.label NativeRustcVmX64.Vm.EWSqIter.entryLabel) EWSqIterPre EWSqIterPost)
    (hpoly : Spec (Labels.label NativeRustcVmX64.Vm.PolyEval.entryLabel) PolyEvalPre PolyEvalPost)
    (_hmul : Spec (Labels.label NativeRustcVmX64.Vm.EWMul.entryLabel) EWMulPre EWMulPost) (hG : Good m0 E)
    {st : MachineState} (h : At m0 k NativeRustcVmX64.Vm.RingTarget.b12Offset (rsC m0) t12 (v12 m0 E) (CAt m0) st) :
    Eventually (step1 Host.exe) (At m0 k NativeRustcVmX64.Vm.RingTarget.b20Offset (rsC m0) t20 (v20 m0 E) (CAt m0)) st := by
  refine Eventually.bind (sqS hp hpre hsq hG b12_in_code (by simp [b12]) rfl (T' := t13)
    (vals' := v13 m0 E) run_b12 rfl rfl rfl rfl rfl (fun m hB ret ↦ by vtac hpre hG hB)
    (fun mc m' hm hq ↦ sq_res hm hq (by decide) rfl rfl rfl rfl rfl (hG.tv 5 (by decide)).symm) rfl rfl rfl rfl rfl
    (fun _ _ ↦ keyOk rfl rfl) rfl h) fun st h ↦ ?_
  refine Eventually.bind (sqS hp hpre hsq hG b13_in_code (by simp [b13]) rfl (T' := t14)
    (vals' := v14 m0 E) run_b13 rfl rfl rfl rfl rfl (fun m hB ret ↦ by vtac hpre hG hB)
    (fun mc m' hm hq ↦ sq_res hm hq (by decide) rfl rfl rfl rfl rfl (hG.z 3 (by decide) (by decide)).symm) rfl rfl rfl rfl rfl
    (fun _ _ ↦ keyOk rfl rfl) rfl h) fun st h ↦ ?_
  refine Eventually.bind (polyS hp hpre hpoly hG b14_in_code (by simp [b14]) rfl (T' := t15)
    (vals' := v15 m0 E) run_b14 rfl rfl rfl rfl rfl rfl rfl (fun m hB ret ↦ by vtac hpre hG hB)
    (fun mc m' hm hs hq ↦ poly_res hm hq hs rfl rfl rfl rfl (hG.pv 4 (by decide)).symm) rfl rfl rfl
    rfl rfl (fun _ _ ↦ keyOk rfl rfl) rfl h) fun st h ↦ ?_
  refine Eventually.bind (sqS hp hpre hsq hG b15_in_code (by simp [b15]) rfl (T' := t16)
    (vals' := v16 m0 E) run_b15 rfl rfl rfl rfl rfl (fun m hB ret ↦ by vtac hpre hG hB)
    (fun mc m' hm hq ↦ sq_res hm hq (by decide) rfl rfl rfl rfl rfl (hG.tv 4 (by decide)).symm) rfl rfl rfl rfl rfl
    (fun _ _ ↦ keyOk rfl rfl) rfl h) fun st h ↦ ?_
  refine Eventually.bind (sqS hp hpre hsq hG b16_in_code (by simp [b16]) rfl (T' := t17)
    (vals' := v17 m0 E) run_b16 rfl rfl rfl rfl rfl (fun m hB ret ↦ by vtac hpre hG hB)
    (fun mc m' hm hq ↦ sq_res hm hq (by decide) rfl rfl rfl rfl rfl (hG.z 4 (by decide) (by decide)).symm) rfl rfl rfl rfl rfl
    (fun _ _ ↦ keyOk rfl rfl) rfl h) fun st h ↦ ?_
  refine Eventually.bind (polyS hp hpre hpoly hG b17_in_code (by simp [b17]) rfl (T' := t18)
    (vals' := v18 m0 E) run_b17 rfl rfl rfl rfl rfl rfl rfl (fun m hB ret ↦ by vtac hpre hG hB)
    (fun mc m' hm hs hq ↦ poly_res hm hq hs rfl rfl rfl rfl (hG.pv 3 (by decide)).symm) rfl rfl rfl
    rfl rfl (fun _ _ ↦ keyOk rfl rfl) rfl h) fun st h ↦ ?_
  refine Eventually.bind (sqS hp hpre hsq hG b18_in_code (by simp [b18]) rfl (T' := t19)
    (vals' := v19 m0 E) run_b18 rfl rfl rfl rfl rfl (fun m hB ret ↦ by vtac hpre hG hB)
    (fun mc m' hm hq ↦ sq_res hm hq (by decide) rfl rfl rfl rfl rfl (hG.tv 3 (by decide)).symm) rfl rfl rfl rfl rfl
    (fun _ _ ↦ keyOk rfl rfl) rfl h) fun st h ↦ ?_
  refine Eventually.bind (sqS hp hpre hsq hG b19_in_code (by simp [b19]) rfl (T' := t20)
    (vals' := v20 m0 E) run_b19 rfl rfl rfl rfl rfl (fun m hB ret ↦ by vtac hpre hG hB)
    (fun mc m' hm hq ↦ sq_res hm hq (by decide) rfl rfl rfl rfl rfl (hG.z 5 (by decide) (by decide)).symm) rfl rfl rfl rfl rfl
    (fun _ _ ↦ keyOk rfl rfl) rfl h) fun st h ↦ ?_
  exact .done _ h

end

end NativeRustcVmX64.Ring.Target
