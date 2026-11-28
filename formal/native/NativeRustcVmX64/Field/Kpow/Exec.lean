module

public import NativeRustcVmX64.Field.Frame
public meta import NativeRustcVmX64.Field.Frame
public import NativeRustcVmX64.Code.Vm.Kpow
public meta import NativeRustcVmX64.Code.Vm.Kpow

/-!
# `kpow`'s blocks, run by the symbolic executor (x86-64)

The prologue `b0` from `frameS 32` (its 3 pushes and its calls' slot), the others (`b2`, a
padding, is never run) from `midS 32`: `b3` and `b6` end in `call kmul`, `b9` is the epilogue.
-/

namespace NativeRustcVmX64.Field.Kpow

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Field NativeRustcVmX64.Vm.Kpow

set_option Elab.async false

sym_block run_b0 := exec b0 (frameS 32)
sym_block run_b1 := exec b1 (midS 32)
sym_block run_b3 := exec b3 (midS 32)
sym_block run_b4 := exec b4 (midS 32)
sym_block run_b5 := exec b5 (midS 32)
sym_block run_b6 := exec b6 (midS 32)
sym_block run_b7 := exec b7 (midS 32)
sym_block run_b8 := exec b8 (midS 32)
sym_block run_b9 := exec b9 (midS 32)

end NativeRustcVmX64.Field.Kpow
