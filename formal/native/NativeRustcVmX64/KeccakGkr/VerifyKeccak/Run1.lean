module

public import NativeRustcVmX64.KeccakGkr.VerifyKeccak.Tpl
public import NativeRustcVmX64.Code.Vm.VerifyKeccak
public meta import NativeRustcVmX64.KeccakGkr.VerifyKeccak.Tpl
public meta import NativeRustcVmX64.Code.Vm.VerifyKeccak

/-!
# `verify_keccak`'s blocks b0–b16, run from their templates (x86-64)
-/

namespace NativeRustcVmX64.KeccakGkr.VerifyKeccak

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Vm.VerifyKeccak

set_option Elab.async false

sym_block run_b0 := exec b0 tE
sym_block run_b1 := exec b1 t1
sym_block run_b2 := exec b2 t2
sym_block run_b3 := exec b3 t2
sym_block run_b4 := exec b4 t2
sym_block run_b5 := exec b5 t2
sym_block run_b6 := exec b6 t2
sym_block run_b7 := exec b7 t2
sym_block run_b8 := exec b8 t8
sym_block run_b9 := exec b9 t9G
sym_block run_b10 := exec b10 t10
sym_block run_b11 := exec b11 t11
sym_block run_b12 := exec b12 t11
sym_block run_b13 := exec b13 t11
sym_block run_b14 := exec b14 t11
sym_block run_b15 := exec b15 t15
sym_block run_b16 := exec b16 t16

end NativeRustcVmX64.KeccakGkr.VerifyKeccak
