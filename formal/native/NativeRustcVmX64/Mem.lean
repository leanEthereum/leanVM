module

public import NativeRustcX64.Mem.Memcpy
public import NativeRustcX64.Mem.Memset
public import NativeRustcVmX64.Code.Vm.Memcpy
public import NativeRustcVmX64.Code.Vm.Memset
public import NativeRustcVmX64.Code.Vm.Memcpy.Names
public import NativeRustcVmX64.Code.Vm.Memset.Names

/-!
# `memcpy` and `memset` of `leanvm_verify`'s x86-64 program

rustc compiles `rustc/vm/src/mem.rs`, the signature verifiers' `rustc/mem.rs`, to the same code:
the VM program's `memcpy` and `memset` are the signature programs' (`memcpy_code`, `memset_code`),
so their contracts (`NativeRustcX64.Mem.Memcpy.memcpy_spec`, `…Memset.memset_spec`) hold here.
-/

namespace NativeRustcVmX64.Mem

open NativeRustcX64

public section

theorem memcpy_code : Vm.Memcpy.code = NativeRustcX64.Common.Memcpy.code := rfl

theorem memset_code : Vm.Memset.code = NativeRustcX64.Common.Memset.code := rfl

variable [Host] {k : Nat}

/-- **`memcpy`'s contract** in the VM program. -/
theorem memcpy_spec (hp : Placed Vm.Memcpy.code k) : Spec (label NativeRustcVmX64.Vm.Memcpy.entryLabel) MemcpyPre MemcpyPost :=
  NativeRustcX64.Mem.Memcpy.memcpy_spec (memcpy_code ▸ hp)

/-- **`memset`'s contract** in the VM program. -/
theorem memset_spec (hp : Placed Vm.Memset.code k) : Spec (label NativeRustcVmX64.Vm.Memset.entryLabel) MemsetPre MemsetPost :=
  NativeRustcX64.Mem.Memset.memset_spec (memset_code ▸ hp)

end

end NativeRustcVmX64.Mem
