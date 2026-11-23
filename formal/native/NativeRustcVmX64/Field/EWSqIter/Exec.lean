module

public import NativeRustcVmX64.Field.Frame
public meta import NativeRustcVmX64.Field.Frame
public import NativeRustcVmX64.Code.Vm.EWSqIter
public meta import NativeRustcVmX64.Code.Vm.EWSqIter

/-!
# `EW::sq_iter`'s blocks, run by the symbolic executor (x86-64)

`b0` (the test of the count), `b1` (the push), and `b5` (the return) from `frameS 16` (its push
and its call's slot); the loop's blocks `b2` (ending in `call EW::mul`) and `b3`, and the pop
`b4`, from `midS 16`.
-/

namespace NativeRustcVmX64.Field.EWSqIter

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Field NativeRustcVmX64.Vm.EWSqIter

set_option Elab.async false

sym_block run_b0 := exec b0 (frameS 16)
sym_block run_b1 := exec b1 (frameS 16)
sym_block run_b2 := exec b2 (midS 16)
sym_block run_b3 := exec b3 (midS 16)
sym_block run_b4 := exec b4 (midS 16)
sym_block run_b5 := exec b5 (frameS 16)

end NativeRustcVmX64.Field.EWSqIter
