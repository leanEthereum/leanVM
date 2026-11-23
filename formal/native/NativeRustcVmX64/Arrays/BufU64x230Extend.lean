module

public import NativeRustcVmX64.Arrays.BufU64
public import NativeRustcVmX64.Code.Vm.BufU64x230Extend
public import NativeRustcVmX64.Code.Vm.BufU64x230Extend.Names
public meta import NativeRustcVmX64.Code.Vm.BufU64x230Extend
public meta import NativeRustcVmX64.Arrays.BufU64

/-!
# `Buf<u64, 230>::extend` on x86-64

**`bufU64x230Extend_spec`**: the instance's blocks run by the symbolic executor from
`NativeRustcVmX64.Arrays.BufU64`'s states, their facts decided, and `BufU64.spec_of`.
-/

namespace NativeRustcVmX64.Arrays.BufU64x230Extend

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Vm.BufU64x230Extend
  NativeRustcVmX64.Arrays.BufU64

set_option Elab.async false

sym_block run_b0 := exec b0 retS
sym_block run_b1 := exec b1 countS
sym_block run_b2 := exec b2 regsS
sym_block run_b3 := exec b3 bodyS
sym_block run_b4 := exec b4 retS
sym_block run_b5 := exec b5 retS

variable [Host] {k : Nat}

/-- **`Buf<u64, 230>::extend` meets its contract.** -/
public theorem bufU64x230Extend_spec (hp : Placed code k) :
    Spec (Labels.label NativeRustcVmX64.Vm.BufU64x230Extend.entryLabel) (BufU64ExtendPre 230) (BufU64ExtendPost 230) :=
  spec_of (k1 := k + NativeRustcVmX64.Vm.BufU64x230Extend.b1Offset) (k2 := k + NativeRustcVmX64.Vm.BufU64x230Extend.b2Offset) (k3 := k + NativeRustcVmX64.Vm.BufU64x230Extend.b3Offset) (k4 := k + NativeRustcVmX64.Vm.BufU64x230Extend.b4Offset) (k5 := k + NativeRustcVmX64.Vm.BufU64x230Extend.b5Offset)
    { hb0 := b0_in_code.trans hp.1 (by simp [b0])
      hb1 := b1_in_code.trans hp.1 (by simp [b1])
      hb2 := b2_in_code.trans hp.1 (by simp [b2])
      hb3 := b3_in_code.trans hp.1 (by simp [b3])
      hb4 := b4_in_code.trans hp.1 (by simp [b4])
      hb5 := b5_in_code.trans hp.1 (by simp [b5])
      e1 := rfl
      e2 := rfl
      e3 := rfl
      e4 := rfl
      hl2 := hp.label NativeRustcVmX64.Vm.BufU64x230Extend.label_2_at
      hl3 := hp.label NativeRustcVmX64.Vm.BufU64x230Extend.label_3_at
      hl5 := hp.label NativeRustcVmX64.Vm.BufU64x230Extend.label_5_at
      x0 := run_b0
      x1 := run_b1
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
    (hp.label NativeRustcVmX64.Vm.BufU64x230Extend.entry_at)

end NativeRustcVmX64.Arrays.BufU64x230Extend
