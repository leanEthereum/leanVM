module

public import NativeRustcVmArm.KeccakGkr.KeccakOpen.States
public import NativeRustcVmArm.Code.Vm.KeccakOpen
public meta import NativeRustcVmArm.KeccakGkr.KeccakOpen.States
public meta import NativeRustcVmArm.Code.Vm.KeccakOpen

/-!
# `keccak_open`'s blocks, run by the symbolic executor: the prologue and the epilogue
-/

namespace NativeRustcVmArm.KeccakGkr.KeccakOpen

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.KeccakOpen

set_option Elab.async false

sym_block run_b0a := exec (b0.take 8) frS
sym_block run_b0b := exec (b0.drop 8) argS
sym_block run_b1 := exec b1 argS
sym_block run_b2 := exec b2 argS
sym_block run_b3 := exec b3 regsS
sym_block run_b4 := exec b4 b4S
sym_block run_b93 := exec b93 outS
sym_block run_b94 := exec b94 regsS
sym_block run_b95a := exec (b95.take 2) resS
sym_block run_b95b := exec (b95.drop 2) epiS

end NativeRustcVmArm.KeccakGkr.KeccakOpen
