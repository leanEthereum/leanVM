module

public import NativeRustcVmArm.Code.Vm.Memcpy.Names
public import NativeRustcVmArm.Code.Vm.Memset.Names
public import NativeRustcArm.Mem.Memcpy
public import NativeRustcArm.Mem.Memset
public import NativeRustcVmArm.Code.Vm.Memcpy
public import NativeRustcVmArm.Code.Vm.Memset

/-!
# `memcpy` and `memset` of `leanvm_verify`'s program

rustc compiles `rustc/vm/src/mem.rs`, the signature verifiers' `rustc/mem.rs`, to the same code:
the VM program's `memcpy` and `memset` are the signature programs' (`memcpy_code`, `memset_code`),
so their contracts (`NativeRustcArm.Mem.Memcpy.memcpy_spec`, `…Memset.memset_spec`) hold here.
-/

namespace NativeRustcVmArm.Mem

open NativeRustcArm

public section

theorem memcpy_code : Vm.Memcpy.code = NativeRustcArm.Common.Memcpy.code := rfl

theorem memset_code : Vm.Memset.code = NativeRustcArm.Common.Memset.code := rfl

variable [NativeRustcArm.Host] {k : Nat}

/-- **`memcpy`'s contract** in the VM program. -/
theorem memcpy_spec (hp : Placed Vm.Memcpy.code k) : Spec (label NativeRustcVmArm.Vm.Memcpy.entryLabel) MemcpyPre MemcpyPost :=
  NativeRustcArm.Mem.Memcpy.memcpy_spec (memcpy_code ▸ hp)

/-- **`memset`'s contract** in the VM program. -/
theorem memset_spec (hp : Placed Vm.Memset.code k) : Spec (label NativeRustcVmArm.Vm.Memset.entryLabel) MemsetPre MemsetPost :=
  NativeRustcArm.Mem.Memset.memset_spec (memset_code ▸ hp)

end

end NativeRustcVmArm.Mem
