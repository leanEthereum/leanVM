module

public import NativeRustcVmArm.Code.Vm.BufEW230Extend.Names
public import NativeRustcVmArm.Arrays.BufEW
public import NativeRustcVmArm.Code.Vm.BufEW230Extend
public meta import NativeRustcVmArm.Code.Vm.BufEW230Extend
public meta import NativeRustcVmArm.Arrays.BufEW

/-!
# `Buf<EW, 230>::extend` on AArch64

**`bufEW230Extend_spec`**: the instance's blocks run by the symbolic executor from
`NativeRustcVmArm.Arrays.BufEW`'s states, their facts decided, and `BufEW.spec_of`.
-/

namespace NativeRustcVmArm.Arrays.BufEW230Extend

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.BufEW230Extend NativeRustcVmArm.Arrays.BufEW

set_option Elab.async false

sym_block run_b0 := exec b0 entryS
sym_block run_b1 := exec b1 (after b0 entryS)
sym_block run_b2 := exec b2 regsS
sym_block run_b3 := exec b3 bodyS
sym_block run_b4 := exec b4 regsS
sym_block run_b5 := exec b5 regsS

variable [NativeRustcArm.Host] {k : Nat}

/-- **`Buf<EW, 230>::extend` meets its contract.** -/
public theorem bufEW230Extend_spec (hp : Placed code k) :
    Spec (Labels.label NativeRustcVmArm.Vm.BufEW230Extend.entryLabel) (BufEWExtendPre 230) (BufEWExtendPost 230) :=
  spec_of (k2 := k + NativeRustcVmArm.Vm.BufEW230Extend.b2Offset) (k3 := k + NativeRustcVmArm.Vm.BufEW230Extend.b3Offset) (k4 := k + NativeRustcVmArm.Vm.BufEW230Extend.b4Offset) (k5 := k + NativeRustcVmArm.Vm.BufEW230Extend.b5Offset)
    { hb0 := b0_in_code.trans hp.1 (by simp [b0])
      hb1 := b1_in_code.trans hp.1 (by simp [b1])
      hb2 := b2_in_code.trans hp.1 (by simp [b2])
      hb3 := b3_in_code.trans hp.1 (by simp [b3])
      hb4 := b4_in_code.trans hp.1 (by simp [b4])
      hb5 := b5_in_code.trans hp.1 (by simp [b5])
      e2 := by
        rw [← b1_next, ← b0_next]
        simp only [b0Offset, Nat.zero_add, Nat.add_assoc]
      e3 := by rw [Nat.add_assoc, b2_next]
      e4 := by rw [Nat.add_assoc, b3_next]
      hl2 := hp.label (j := NativeRustcVmArm.Vm.BufEW230Extend.b2Offset) NativeRustcVmArm.Vm.BufEW230Extend.label_2_at
      hl4 := hp.label (j := NativeRustcVmArm.Vm.BufEW230Extend.b4Offset) NativeRustcVmArm.Vm.BufEW230Extend.label_4_at
      hl5 := hp.label (j := NativeRustcVmArm.Vm.BufEW230Extend.b5Offset) NativeRustcVmArm.Vm.BufEW230Extend.label_5_at
      x0 := run_b0
      x1 := exec_after run_b0 run_b1
      x2 := run_b2
      x3 := run_b3
      x4 := run_b4
      x5 := run_b5
      f0 := by decide +kernel
      f1 := by decide +kernel
      f2 := by decide +kernel
      f3 := by decide +kernel
      f4 := by decide +kernel
      f5 := by decide +kernel }
    (hp.label (j := NativeRustcVmArm.Vm.BufEW230Extend.entryOffset) NativeRustcVmArm.Vm.BufEW230Extend.entry_at)

end NativeRustcVmArm.Arrays.BufEW230Extend
