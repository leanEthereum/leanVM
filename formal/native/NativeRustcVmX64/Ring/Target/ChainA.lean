module

public import NativeRustcVmX64.Ring.Target.Wrap
public import NativeRustcVmX64.Code.Vm.EWMul.Names
public import NativeRustcVmX64.Code.Vm.EWSqIter.Names
public import NativeRustcVmX64.Code.Vm.PolyEval.Names

/-!
# `ring_target`: the turns' blocks `b4` to `b11` (x86-64)

Generated from the assembly: each block from its template `t<j>` with the values `v<j>`, its call
(`sqS`, `polyS`, `mulS`), the callee's result the table `E`'s next entry (`Good`).
-/

namespace NativeRustcVmX64.Ring.Target

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Ring NativeVm.Model NativeRustcVm.Ring
open NativeRustcVmX64.Vm.RingTarget

public section

variable {m0 : MachineData} {E : Nat → EW} [Host] {k : Nat}

/-- **The blocks `b4` to `b11`.** -/
theorem chainA (hp : Placed code k) (hpre : RingTargetPre m0)
    (hsq : Spec (Labels.label NativeRustcVmX64.Vm.EWSqIter.entryLabel) EWSqIterPre EWSqIterPost)
    (hpoly : Spec (Labels.label NativeRustcVmX64.Vm.PolyEval.entryLabel) PolyEvalPre PolyEvalPost)
    (_hmul : Spec (Labels.label NativeRustcVmX64.Vm.EWMul.entryLabel) EWMulPre EWMulPost) (hG : Good m0 E)
    {st : MachineState} (h : At m0 k NativeRustcVmX64.Vm.RingTarget.b4Offset (rsC m0) t4 (v4 m0 E) (CAt m0) st) :
    Eventually (step1 Host.exe) (At m0 k NativeRustcVmX64.Vm.RingTarget.b12Offset (rsC m0) t12 (v12 m0 E) (CAt m0)) st := by
  refine Eventually.bind (sqS hp hpre hsq hG b4_in_code (by simp [b4]) rfl (T' := t5)
    (vals' := v5 m0 E) run_b4 rfl rfl rfl rfl rfl (fun m hB ret ↦ by vtac hpre hG hB)
    (fun mc m' hm hq ↦ sq_res hm hq (by decide) rfl rfl rfl rfl rfl hG.z1.symm) rfl rfl rfl rfl rfl
    (fun _ _ ↦ keyOk rfl rfl) rfl h) fun st h ↦ ?_
  refine Eventually.bind (polyS hp hpre hpoly hG b5_in_code (by simp [b5]) rfl (T' := t6)
    (vals' := v6 m0 E) run_b5 rfl rfl rfl rfl rfl rfl rfl (fun m hB ret ↦ by vtac hpre hG hB)
    (fun mc m' hm hs hq ↦ poly_res hm hq hs rfl rfl rfl rfl (hG.pv 7 (by decide)).symm) rfl rfl rfl
    rfl rfl (fun _ _ ↦ keyOk rfl rfl) rfl h) fun st h ↦ ?_
  refine Eventually.bind (sqS hp hpre hsq hG b6_in_code (by simp [b6]) rfl (T' := t7)
    (vals' := v7 m0 E) run_b6 rfl rfl rfl rfl rfl (fun m hB ret ↦ by vtac hpre hG hB)
    (fun mc m' hm hq ↦ sq_res hm hq (by decide) rfl rfl rfl rfl rfl (hG.tv 7 (by decide)).symm) rfl rfl rfl rfl rfl
    (fun _ _ ↦ keyOk rfl rfl) rfl h) fun st h ↦ ?_
  refine Eventually.bind (sqS hp hpre hsq hG b7_in_code (by simp [b7]) rfl (T' := t8)
    (vals' := v8 m0 E) run_b7 rfl rfl rfl rfl rfl (fun m hB ret ↦ by vtac hpre hG hB)
    (fun mc m' hm hq ↦ sq_res hm hq (by decide) rfl rfl rfl rfl rfl (hG.z 1 (by decide) (by decide)).symm) rfl rfl rfl rfl rfl
    (fun _ _ ↦ keyOk rfl rfl) rfl h) fun st h ↦ ?_
  refine Eventually.bind (polyS hp hpre hpoly hG b8_in_code (by simp [b8]) rfl (T' := t9)
    (vals' := v9 m0 E) run_b8 rfl rfl rfl rfl rfl rfl rfl (fun m hB ret ↦ by vtac hpre hG hB)
    (fun mc m' hm hs hq ↦ poly_res hm hq hs rfl rfl rfl rfl (hG.pv 6 (by decide)).symm) rfl rfl rfl
    rfl rfl (fun _ _ ↦ keyOk rfl rfl) rfl h) fun st h ↦ ?_
  refine Eventually.bind (sqS hp hpre hsq hG b9_in_code (by simp [b9]) rfl (T' := t10)
    (vals' := v10 m0 E) run_b9 rfl rfl rfl rfl rfl (fun m hB ret ↦ by vtac hpre hG hB)
    (fun mc m' hm hq ↦ sq_res hm hq (by decide) rfl rfl rfl rfl rfl (hG.tv 6 (by decide)).symm) rfl rfl rfl rfl rfl
    (fun _ _ ↦ keyOk rfl rfl) rfl h) fun st h ↦ ?_
  refine Eventually.bind (sqS hp hpre hsq hG b10_in_code (by simp [b10]) rfl (T' := t11)
    (vals' := v11 m0 E) run_b10 rfl rfl rfl rfl rfl (fun m hB ret ↦ by vtac hpre hG hB)
    (fun mc m' hm hq ↦ sq_res hm hq (by decide) rfl rfl rfl rfl rfl (hG.z 2 (by decide) (by decide)).symm) rfl rfl rfl rfl rfl
    (fun _ _ ↦ keyOk rfl rfl) rfl h) fun st h ↦ ?_
  refine Eventually.bind (polyS hp hpre hpoly hG b11_in_code (by simp [b11]) rfl (T' := t12)
    (vals' := v12 m0 E) run_b11 rfl rfl rfl rfl rfl rfl rfl (fun m hB ret ↦ by vtac hpre hG hB)
    (fun mc m' hm hs hq ↦ poly_res hm hq hs rfl rfl rfl rfl (hG.pv 5 (by decide)).symm) rfl rfl rfl
    rfl rfl (fun _ _ ↦ keyOk rfl rfl) rfl h) fun st h ↦ ?_
  exact .done _ h

end

end NativeRustcVmX64.Ring.Target
