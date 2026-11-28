module

public import NativeRustcVmArm.KeccakGkr.KeccakOpen.States
public import NativeRustcVmArm.Code.Vm.KeccakOpen
public meta import NativeRustcVmArm.KeccakGkr.KeccakOpen.States
public meta import NativeRustcVmArm.Code.Vm.KeccakOpen

/-!
# `keccak_open`'s blocks, run by the symbolic executor: the looped rounds 0 and 1
-/

namespace NativeRustcVmArm.KeccakGkr.KeccakOpen

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.KeccakOpen

set_option Elab.async false

sym_block run_b5 := exec b5 (pS kO)
sym_block run_b6 := exec b6 (pS kM)
sym_block run_b7 := exec b7 (pS kM)
sym_block run_b8 := exec b8 (loS .X27 .X28 .X29)
sym_block run_b9 := exec b9 (lstS .X19)
sym_block run_b10 := exec b10 (pS kOE)
sym_block run_b11 := exec b11 (pS kP)
sym_block run_b12 := exec b12 (pS kO)
sym_block run_b13 := exec b13 (pS kM)
sym_block run_b14 := exec b14 (pS kM)
sym_block run_b15 := exec b15 (loS .X27 .X28 .X19)
sym_block run_b16 := exec b16 (lstS .X29)
sym_block run_b17 := exec b17 (pS kOE)

end NativeRustcVmArm.KeccakGkr.KeccakOpen
