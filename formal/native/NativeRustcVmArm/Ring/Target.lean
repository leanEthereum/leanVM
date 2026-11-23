module

public import NativeRustcVmArm.Code.Vm.EWMul.Names
public import NativeRustcVmArm.Code.Vm.EWSqIter.Names
public import NativeRustcVmArm.Code.Vm.Memcpy.Names
public import NativeRustcVmArm.Code.Vm.PolyEval.Names
public import NativeRustcVmArm.Code.Vm.RingPsi.Names
public import NativeRustcVmArm.Code.Vm.RingTarget.Names
public import NativeRustcVmArm.Ring.Target.Copy

/-!
# `ring_target`'s contract

The prologue (`b0`), the images loop `Ψ(s_i)` (`b1`, `b2`), their copy (`b3`), the turns
`p = 7 … 0` and the products (`b4` to `b35`, `ChainA`, `ChainB`, `Ends`), the sum returned
(`b36`).
-/

namespace NativeRustcVmArm.Ring.Target

open NativeRustcArm NativeRustcArm.Sym NativeVm.Model NativeRustcVm.Ring
open NativeRustcVmArm.Vm.RingTarget

public section

variable [Host] {k : Nat}

/-- **`ring_target`'s contract.** -/
theorem ringTarget_spec (hp : Placed code k)
    (hpsi : Spec (Labels.label NativeRustcVmArm.Vm.RingPsi.entryLabel) RingPsiPre RingPsiPost)
    (hmemcpy : Spec (Labels.label NativeRustcVmArm.Vm.Memcpy.entryLabel) MemcpyPre MemcpyPost)
    (hsq : Spec (Labels.label NativeRustcVmArm.Vm.EWSqIter.entryLabel) EWSqIterPre EWSqIterPost)
    (hpoly : Spec (Labels.label NativeRustcVmArm.Vm.PolyEval.entryLabel) PolyEvalPre PolyEvalPost)
    (hmul : Spec (Labels.label NativeRustcVmArm.Vm.EWMul.entryLabel) EWMulPre EWMulPost) :
    Spec (Labels.label NativeRustcVmArm.Vm.RingTarget.entryLabel) RingTargetPre RingTargetPost := by
  intro m0 hpre
  have h := P.intro hpre
  rw [show Labels.label NativeRustcVmArm.Vm.RingTarget.entryLabel = Host.addrOf (k + NativeRustcVmArm.Vm.RingTarget.b0Offset) from hp.label (j := NativeRustcVmArm.Vm.RingTarget.entryOffset) NativeRustcVmArm.Vm.RingTarget.entry_at]
  refine stepEntry h (hb b0_in_code (by simp [b0]) hp) fun m1 h1 ↦ ?_
  rw [show k + NativeRustcVmArm.Vm.RingTarget.b0Offset + b0.length = k + NativeRustcVmArm.Vm.RingTarget.b1Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.RingTarget.b0_next]]
  refine images hp h hpsi h1 fun m2 h2 ↦ ?_
  refine stepCopy hp h hmemcpy h2 fun m3 h3 ↦ ?_
  refine chainA hp h hsq hpoly h3 fun m4 h4 ↦ ?_
  refine chainB hp h hsq hpoly hmul h4 fun m5 h5 ↦ ?_
  exact chainC hp h hsq hpoly hmul h5

end

end NativeRustcVmArm.Ring.Target
