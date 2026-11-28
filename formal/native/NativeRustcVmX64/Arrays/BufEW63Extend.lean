module

public import NativeRustcVmX64.Arrays.BufEW
public import NativeRustcVmX64.Code.Vm.BufEW63Extend
public import NativeRustcVmX64.Code.Vm.BufEW63Extend.Names
public meta import NativeRustcVmX64.Code.Vm.BufEW63Extend
public meta import NativeRustcVmX64.Arrays.BufEW

/-!
# `Buf<EW, 63>::extend` on x86-64

**`bufEW63Extend_spec`**: the instance's blocks run by the symbolic executor from
`NativeRustcVmX64.Arrays.BufEW`'s states, their facts decided, and `BufEW.spec_of`.
-/

namespace NativeRustcVmX64.Arrays.BufEW63Extend

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Vm.BufEW63Extend
  NativeRustcVmX64.Arrays.BufEW

set_option Elab.async false

sym_block run_b0 := exec b0 entryS
sym_block run_b7a := exec b7 (after b0 entryS)
sym_block run_b1 := exec b1 countS
sym_block run_b2 := exec b2 regsS
sym_block run_b3 := exec b3 bodyS
sym_block run_b4 := exec b4 regsS
sym_block run_b567 := exec (b5 ++ b6 ++ b7) endS
sym_block run_b67 := exec (b6 ++ b7) endS

variable [Host] {k : Nat}

theorem hb5 (hp : Placed code k) : b5.IsInfixAt Host.prog (k + NativeRustcVmX64.Vm.BufEW63Extend.b5Offset) :=
  b5_in_code.trans hp.1 (by simp [b5])
theorem hb6 (hp : Placed code k) : b6.IsInfixAt Host.prog (k + NativeRustcVmX64.Vm.BufEW63Extend.b6Offset) :=
  b6_in_code.trans hp.1 (by simp [b6])
theorem hb7 (hp : Placed code k) : b7.IsInfixAt Host.prog (k + NativeRustcVmX64.Vm.BufEW63Extend.b7Offset) :=
  b7_in_code.trans hp.1 (by simp [b7])

theorem hb67 (hp : Placed code k) : (b6 ++ b7).IsInfixAt Host.prog (k + NativeRustcVmX64.Vm.BufEW63Extend.b6Offset) :=
  isInfixAt_concat (hb6 hp) (hb7 hp)

theorem hb567 (hp : Placed code k) : (b5 ++ b6 ++ b7).IsInfixAt Host.prog (k + NativeRustcVmX64.Vm.BufEW63Extend.b5Offset) :=
  isInfixAt_concat (isInfixAt_concat (hb5 hp) (hb6 hp)) (hb7 hp)

/-- **`Buf<EW, 63>::extend` meets its contract.** -/
public theorem bufEW63Extend_spec (hp : Placed code k) :
    Spec (Labels.label NativeRustcVmX64.Vm.BufEW63Extend.entryLabel) (BufEWExtendPre 63) (BufEWExtendPost 63) :=
  spec_of (k1 := k + NativeRustcVmX64.Vm.BufEW63Extend.b1Offset) (k2 := k + NativeRustcVmX64.Vm.BufEW63Extend.b2Offset) (k3 := k + NativeRustcVmX64.Vm.BufEW63Extend.b3Offset) (k4 := k + NativeRustcVmX64.Vm.BufEW63Extend.b4Offset) (k5 := k + NativeRustcVmX64.Vm.BufEW63Extend.b5Offset) (k6 := k + NativeRustcVmX64.Vm.BufEW63Extend.b6Offset)
    (k7 := k + NativeRustcVmX64.Vm.BufEW63Extend.b7Offset)
    { hb0 := b0_in_code.trans hp.1 (by simp [b0])
      hb1 := b1_in_code.trans hp.1 (by simp [b1])
      hb2 := b2_in_code.trans hp.1 (by simp [b2])
      hb3 := b3_in_code.trans hp.1 (by simp [b3])
      hb4 := b4_in_code.trans hp.1 (by simp [b4])
      hb567 := hb567 hp
      hb67 := hb67 hp
      hb7 := hb7 hp
      e1 := rfl
      e2 := rfl
      e3 := rfl
      e4 := rfl
      hl2 := hp.label NativeRustcVmX64.Vm.BufEW63Extend.label_2_at
      hl3 := hp.label NativeRustcVmX64.Vm.BufEW63Extend.label_3_at
      hl5 := hp.label NativeRustcVmX64.Vm.BufEW63Extend.label_5_at
      hl6 := hp.label NativeRustcVmX64.Vm.BufEW63Extend.label_6_at
      x0 := run_b0
      x7a := exec_after run_b0 run_b7a
      x1 := run_b1
      x2 := run_b2
      x3 := run_b3
      x4 := run_b4
      x7 := run_b567
      x7' := run_b67
      f0 := by decide +kernel
      f7a := by decide +kernel
      f1 := by decide +kernel
      f2 := by decide +kernel
      f3 := by decide +kernel
      f4 := by decide +kernel
      f7 := by decide +kernel
      f7' := by decide +kernel }
    (hp.label NativeRustcVmX64.Vm.BufEW63Extend.entry_at)

end NativeRustcVmX64.Arrays.BufEW63Extend
