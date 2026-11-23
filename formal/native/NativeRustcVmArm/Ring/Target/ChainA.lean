module

public import NativeRustcVmArm.Code.Vm.EWSqIter.Names
public import NativeRustcVmArm.Code.Vm.PolyEval.Names
public import NativeRustcVmArm.Ring.Target.Chain

/-!
# `ring_target`: the turns `p = 7 … 3`

From the state after the images' copy (`D4`, `b4`): for each `p`, the point `Z_p` (`EW::sq_iter`),
`P_p` (`poly_eval`), `T_p` (`EW::sq_iter`), up to `T_3` in X0, X1 before `b19`.
-/

namespace NativeRustcVmArm.Ring.Target

open NativeRustcArm NativeRustcArm.Sym NativeVm.Model NativeRustcVm.Ring
open NativeRustcVmArm.Vm.RingTarget

public section

variable [Host] {k : Nat} {m0 : MachineData}

theorem hb {ds : List Directive} {j : Nat} (h : ds.IsInfixAt code j) (hne : ds ≠ [])
    (hp : Placed code k) : ds.IsInfixAt Host.prog (k + j) :=
  h.trans hp.1 hne

/-- **The turns `p = 7 … 3`** (`b4` to `b18`). -/
theorem chainA (hp : Placed code k) (h : P m0)
    (hsq : Spec (Labels.label NativeRustcVmArm.Vm.EWSqIter.entryLabel) EWSqIterPre EWSqIterPost)
    (hpoly : Spec (Labels.label NativeRustcVmArm.Vm.PolyEval.entryLabel) PolyEvalPre PolyEvalPost) {m : MachineData}
    (hst : St m0 D4 m) {R : MachineState → Prop}
    (cont : ∀ m', St m0 ((.reg .X0, tI 3) :: (.reg .X1, tI 3 + 1) :: K17) m' →
      Eventually (step1 Host.exe) R ⟨m', Host.addrOf (k + NativeRustcVmArm.Vm.RingTarget.b19Offset)⟩) :
    Eventually (step1 Host.exe) R ⟨m, Host.addrOf (k + NativeRustcVmArm.Vm.RingTarget.b4Offset)⟩ := by
  refine sqStep h hsq (hb b4_in_code (by simp [b4]) hp) run_b4
    hst.ptr (hst.mid h (by decide)) rfl
    (by decide) (D' := bD) (by decide) (by decide) rfl (by decide) (by decide)
    (by decide) hrZ7 fun m hst ↦ ?_
  rw [show k + NativeRustcVmArm.Vm.RingTarget.b4Offset + b4.length = k + NativeRustcVmArm.Vm.RingTarget.b5Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.RingTarget.b4_next]]
  refine polyStep h hpoly (hb b5_in_code (by simp [b5]) hp) run_b5
    hst.ptr (hst.mid h (by decide)) rfl
    (by decide) (D' := K5) (by decide) (by decide) rfl rfl (by decide)
    (by decide) (hrP 7 (by decide)) (E := []) nilE nilH fun m hst ↦ ?_
  rw [show k + NativeRustcVmArm.Vm.RingTarget.b5Offset + b5.length = k + NativeRustcVmArm.Vm.RingTarget.b6Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.RingTarget.b5_next]]
  refine sqStep h hsq (hb b6_in_code (by simp [b6]) hp) run_b6
    hst.ptr (hst.mid h (by decide)) rfl
    (by decide) (D' := K5) (by decide) (by decide) rfl (by decide) (by decide)
    (by decide) (hrT 7 (by decide)) fun m hst ↦ ?_
  rw [show k + NativeRustcVmArm.Vm.RingTarget.b6Offset + b6.length = k + NativeRustcVmArm.Vm.RingTarget.b7Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.RingTarget.b6_next]]
  refine sqStep h hsq (hb b7_in_code (by simp [b7]) hp) run_b7
    hst.ptr (hst.mid h (by decide)) rfl
    (by decide) (D' := K7) (by decide) (by decide) rfl (by decide) (by decide)
    (by decide) (hrZ 6 (by decide)) fun m hst ↦ ?_
  rw [show k + NativeRustcVmArm.Vm.RingTarget.b7Offset + b7.length = k + NativeRustcVmArm.Vm.RingTarget.b8Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.RingTarget.b7_next]]
  refine polyStep h hpoly (hb b8_in_code (by simp [b8]) hp) run_b8
    hst.ptr (hst.mid h (by decide)) rfl
    (by decide) (D' := K8) (by decide) (by decide) rfl rfl (by decide)
    (by decide) (hrP 6 (by decide)) (E := []) nilE nilH fun m hst ↦ ?_
  rw [show k + NativeRustcVmArm.Vm.RingTarget.b8Offset + b8.length = k + NativeRustcVmArm.Vm.RingTarget.b9Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.RingTarget.b8_next]]
  refine sqStep h hsq (hb b9_in_code (by simp [b9]) hp) run_b9
    hst.ptr (hst.mid h (by decide)) rfl
    (by decide) (D' := K8) (by decide) (by decide) rfl (by decide) (by decide)
    (by decide) (hrT 6 (by decide)) fun m hst ↦ ?_
  rw [show k + NativeRustcVmArm.Vm.RingTarget.b9Offset + b9.length = k + NativeRustcVmArm.Vm.RingTarget.b10Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.RingTarget.b9_next]]
  refine sqStep h hsq (hb b10_in_code (by simp [b10]) hp) run_b10
    hst.ptr (hst.mid h (by decide)) rfl
    (by decide) (D' := K10) (by decide) (by decide) rfl (by decide) (by decide)
    (by decide) (hrZ 5 (by decide)) fun m hst ↦ ?_
  rw [show k + NativeRustcVmArm.Vm.RingTarget.b10Offset + b10.length = k + NativeRustcVmArm.Vm.RingTarget.b11Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.RingTarget.b10_next]]
  refine polyStep h hpoly (hb b11_in_code (by simp [b11]) hp) run_b11
    hst.ptr (hst.mid h (by decide)) rfl
    (by decide) (D' := K11) (by decide) (by decide) rfl rfl (by decide)
    (by decide) (hrP 5 (by decide)) (E := []) nilE nilH fun m hst ↦ ?_
  rw [show k + NativeRustcVmArm.Vm.RingTarget.b11Offset + b11.length = k + NativeRustcVmArm.Vm.RingTarget.b12Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.RingTarget.b11_next]]
  refine sqStep h hsq (hb b12_in_code (by simp [b12]) hp) run_b12
    hst.ptr (hst.mid h (by decide)) rfl
    (by decide) (D' := K11) (by decide) (by decide) rfl (by decide) (by decide)
    (by decide) (hrT 5 (by decide)) fun m hst ↦ ?_
  rw [show k + NativeRustcVmArm.Vm.RingTarget.b12Offset + b12.length = k + NativeRustcVmArm.Vm.RingTarget.b13Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.RingTarget.b12_next]]
  refine sqStep h hsq (hb b13_in_code (by simp [b13]) hp) run_b13
    hst.ptr (hst.mid h (by decide)) rfl
    (by decide) (D' := K13) (by decide) (by decide) rfl (by decide) (by decide)
    (by decide) (hrZ 4 (by decide)) fun m hst ↦ ?_
  rw [show k + NativeRustcVmArm.Vm.RingTarget.b13Offset + b13.length = k + NativeRustcVmArm.Vm.RingTarget.b14Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.RingTarget.b13_next]]
  refine polyStep h hpoly (hb b14_in_code (by simp [b14]) hp) run_b14
    hst.ptr (hst.mid h (by decide)) rfl
    (by decide) (D' := K14) (by decide) (by decide) rfl rfl (by decide)
    (by decide) (hrP 4 (by decide)) (E := []) nilE nilH fun m hst ↦ ?_
  rw [show k + NativeRustcVmArm.Vm.RingTarget.b14Offset + b14.length = k + NativeRustcVmArm.Vm.RingTarget.b15Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.RingTarget.b14_next]]
  refine sqStep h hsq (hb b15_in_code (by simp [b15]) hp) run_b15
    hst.ptr (hst.mid h (by decide)) rfl
    (by decide) (D' := K14) (by decide) (by decide) rfl (by decide) (by decide)
    (by decide) (hrT 4 (by decide)) fun m hst ↦ ?_
  rw [show k + NativeRustcVmArm.Vm.RingTarget.b15Offset + b15.length = k + NativeRustcVmArm.Vm.RingTarget.b16Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.RingTarget.b15_next]]
  refine sqStep h hsq (hb b16_in_code (by simp [b16]) hp) run_b16
    hst.ptr (hst.mid h (by decide)) rfl
    (by decide) (D' := K16) (by decide) (by decide) rfl (by decide) (by decide)
    (by decide) (hrZ 3 (by decide)) fun m hst ↦ ?_
  rw [show k + NativeRustcVmArm.Vm.RingTarget.b16Offset + b16.length = k + NativeRustcVmArm.Vm.RingTarget.b17Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.RingTarget.b16_next]]
  refine polyStep h hpoly (hb b17_in_code (by simp [b17]) hp) run_b17
    hst.ptr (hst.mid h (by decide)) rfl
    (by decide) (D' := K17) (by decide) (by decide) rfl rfl (by decide)
    (by decide) (hrP 3 (by decide)) (E := []) nilE nilH fun m hst ↦ ?_
  rw [show k + NativeRustcVmArm.Vm.RingTarget.b17Offset + b17.length = k + NativeRustcVmArm.Vm.RingTarget.b18Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.RingTarget.b17_next]]
  refine sqStep h hsq (hb b18_in_code (by simp [b18]) hp) run_b18
    hst.ptr (hst.mid h (by decide)) rfl
    (by decide) (D' := K17) (by decide) (by decide) rfl (by decide) (by decide)
    (by decide) (hrT 3 (by decide)) fun m hst ↦ ?_
  rw [show k + NativeRustcVmArm.Vm.RingTarget.b18Offset + b18.length = k + NativeRustcVmArm.Vm.RingTarget.b19Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.RingTarget.b18_next]]
  exact cont m hst

end

end NativeRustcVmArm.Ring.Target
