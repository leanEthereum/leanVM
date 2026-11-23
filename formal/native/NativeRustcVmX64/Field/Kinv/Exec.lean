module

public import NativeRustcVmX64.Field.Frame
public meta import NativeRustcVmX64.Field.Frame
public import NativeRustcVmX64.Code.Vm.Kinv
public meta import NativeRustcVmX64.Code.Vm.Kinv

/-!
# `kinv`'s blocks, run by the symbolic executor (x86-64)

The prologue `b0` (ending in `call kinv::sq`) from `frameS 32` (its 3 pushes and its calls' slot),
the others from `midS 32`: `b1` to `b15` each end in a call, the epilogue `b16` in the tail call
`jmp kinv::sq`.
-/

namespace NativeRustcVmX64.Field.Kinv

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Field NativeRustcVmX64.Vm.Kinv

set_option Elab.async false

sym_block run_b0 := exec b0 (frameS 32)
sym_block run_b1 := exec b1 (midS 32)
sym_block run_b2 := exec b2 (midS 32)
sym_block run_b3 := exec b3 (midS 32)
sym_block run_b4 := exec b4 (midS 32)
sym_block run_b5 := exec b5 (midS 32)
sym_block run_b6 := exec b6 (midS 32)
sym_block run_b7 := exec b7 (midS 32)
sym_block run_b8 := exec b8 (midS 32)
sym_block run_b9 := exec b9 (midS 32)
sym_block run_b10 := exec b10 (midS 32)
sym_block run_b11 := exec b11 (midS 32)
sym_block run_b12 := exec b12 (midS 32)
sym_block run_b13 := exec b13 (midS 32)
sym_block run_b14 := exec b14 (midS 32)
sym_block run_b15 := exec b15 (midS 32)
sym_block run_b16 := exec b16 (midS 32)

end NativeRustcVmX64.Field.Kinv
