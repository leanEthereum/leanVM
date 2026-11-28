module

public import NativeRustcVmArm.Code.Vm.EWMul.Names
public import NativeRustcVmArm.Code.Vm.RingPsi.Names
public import NativeRustcVmArm.Ring.Psi.Ends

/-!
# `ring_psi`'s contract

rustc unrolled the loop over `g`'s 8 elements: the prologue and `g_0 · v` (`b0`), the sum and
`v²` (`b1`), then for `j = 1 … 6` the product `g_j · v^(2^j)` (`b2j`) and the sum and the next
square (`b(2j+1)`), the last product (`b14`), the last sum and the epilogue (`b15`).
-/

namespace NativeRustcVmArm.Ring.Psi

open NativeRustcArm NativeRustcArm.Sym NativeVm.Model NativeRustcVm.Ring
open NativeRustcVmArm.Vm.RingPsi

public section

variable [Host] {k : Nat}

theorem hb {ds : List Directive} {j : Nat} (h : ds.IsInfixAt code j) (hne : ds ≠ [])
    (hp : Placed code k) : ds.IsInfixAt Host.prog (k + j) :=
  h.trans hp.1 hne

/-- **`ring_psi`'s contract.** -/
theorem ringPsi_spec (hp : Placed code k)
    (hmul : Spec (Labels.label NativeRustcVmArm.Vm.EWMul.entryLabel) EWMulPre EWMulPost) :
    Spec (Labels.label NativeRustcVmArm.Vm.RingPsi.entryLabel) RingPsiPre RingPsiPost := by
  intro m0 hpre
  rw [show Labels.label NativeRustcVmArm.Vm.RingPsi.entryLabel = Host.addrOf (k + NativeRustcVmArm.Vm.RingPsi.b0Offset) from hp.label (j := NativeRustcVmArm.Vm.RingPsi.entryOffset) NativeRustcVmArm.Vm.RingPsi.entry_at]
  refine stepEntry hpre hmul (hb (j := NativeRustcVmArm.Vm.RingPsi.b0Offset) b0_in_code (by simp [b0]) hp) fun m1 h1 ↦ ?_
  rw [show k + NativeRustcVmArm.Vm.RingPsi.b0Offset + b0.length = k + NativeRustcVmArm.Vm.RingPsi.b1Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.RingPsi.b0_next]]
  refine stepFirst hpre hmul (hb b1_in_code (by simp [b1]) hp) run_b1 (by decide) rfl rfl h1
    fun m2 h2 ↦ ?_
  rw [show k + NativeRustcVmArm.Vm.RingPsi.b1Offset + b1.length = k + NativeRustcVmArm.Vm.RingPsi.b2Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.RingPsi.b1_next]]
  refine stepEven hpre hmul (hb b2_in_code (by simp [b2]) hp) run_b2 (by decide) rfl rfl
    (by decide) h2 fun m h ↦ ?_
  rw [show k + NativeRustcVmArm.Vm.RingPsi.b2Offset + b2.length = k + NativeRustcVmArm.Vm.RingPsi.b3Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.RingPsi.b2_next]]
  refine stepOdd hpre hmul (hb b3_in_code (by simp [b3]) hp) run_b3 (by decide) rfl rfl
    (by decide) h fun m h ↦ ?_
  rw [show k + NativeRustcVmArm.Vm.RingPsi.b3Offset + b3.length = k + NativeRustcVmArm.Vm.RingPsi.b4Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.RingPsi.b3_next]]
  refine stepEven hpre hmul (hb b4_in_code (by simp [b4]) hp) run_b4 (by decide) rfl rfl
    (by decide) h fun m h ↦ ?_
  rw [show k + NativeRustcVmArm.Vm.RingPsi.b4Offset + b4.length = k + NativeRustcVmArm.Vm.RingPsi.b5Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.RingPsi.b4_next]]
  refine stepOdd hpre hmul (hb b5_in_code (by simp [b5]) hp) run_b5 (by decide) rfl rfl
    (by decide) h fun m h ↦ ?_
  rw [show k + NativeRustcVmArm.Vm.RingPsi.b5Offset + b5.length = k + NativeRustcVmArm.Vm.RingPsi.b6Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.RingPsi.b5_next]]
  refine stepEven hpre hmul (hb b6_in_code (by simp [b6]) hp) run_b6 (by decide) rfl rfl
    (by decide) h fun m h ↦ ?_
  rw [show k + NativeRustcVmArm.Vm.RingPsi.b6Offset + b6.length = k + NativeRustcVmArm.Vm.RingPsi.b7Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.RingPsi.b6_next]]
  refine stepOdd hpre hmul (hb b7_in_code (by simp [b7]) hp) run_b7 (by decide) rfl rfl
    (by decide) h fun m h ↦ ?_
  rw [show k + NativeRustcVmArm.Vm.RingPsi.b7Offset + b7.length = k + NativeRustcVmArm.Vm.RingPsi.b8Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.RingPsi.b7_next]]
  refine stepEven hpre hmul (hb b8_in_code (by simp [b8]) hp) run_b8 (by decide) rfl rfl
    (by decide) h fun m h ↦ ?_
  rw [show k + NativeRustcVmArm.Vm.RingPsi.b8Offset + b8.length = k + NativeRustcVmArm.Vm.RingPsi.b9Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.RingPsi.b8_next]]
  refine stepOdd hpre hmul (hb b9_in_code (by simp [b9]) hp) run_b9 (by decide) rfl rfl
    (by decide) h fun m h ↦ ?_
  rw [show k + NativeRustcVmArm.Vm.RingPsi.b9Offset + b9.length = k + NativeRustcVmArm.Vm.RingPsi.b10Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.RingPsi.b9_next]]
  refine stepEven hpre hmul (hb b10_in_code (by simp [b10]) hp) run_b10 (by decide) rfl rfl
    (by decide) h fun m h ↦ ?_
  rw [show k + NativeRustcVmArm.Vm.RingPsi.b10Offset + b10.length = k + NativeRustcVmArm.Vm.RingPsi.b11Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.RingPsi.b10_next]]
  refine stepOdd hpre hmul (hb b11_in_code (by simp [b11]) hp) run_b11 (by decide) rfl rfl
    (by decide) h fun m h ↦ ?_
  rw [show k + NativeRustcVmArm.Vm.RingPsi.b11Offset + b11.length = k + NativeRustcVmArm.Vm.RingPsi.b12Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.RingPsi.b11_next]]
  refine stepEven hpre hmul (hb b12_in_code (by simp [b12]) hp) run_b12 (by decide) rfl rfl
    (by decide) h fun m h ↦ ?_
  rw [show k + NativeRustcVmArm.Vm.RingPsi.b12Offset + b12.length = k + NativeRustcVmArm.Vm.RingPsi.b13Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.RingPsi.b12_next]]
  refine stepOdd hpre hmul (hb b13_in_code (by simp [b13]) hp) run_b13 (by decide) rfl rfl
    (by decide) h fun m h ↦ ?_
  rw [show k + NativeRustcVmArm.Vm.RingPsi.b13Offset + b13.length = k + NativeRustcVmArm.Vm.RingPsi.b14Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.RingPsi.b13_next]]
  refine stepLast hpre hmul (hb b14_in_code (by simp [b14]) hp) run_b14 (by decide) rfl rfl h
    fun m h ↦ ?_
  rw [show k + NativeRustcVmArm.Vm.RingPsi.b14Offset + b14.length = k + NativeRustcVmArm.Vm.RingPsi.b15Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.RingPsi.b14_next]]
  exact stepExit hpre (hb b15_in_code (by simp [b15]) hp) h

end

end NativeRustcVmArm.Ring.Psi
