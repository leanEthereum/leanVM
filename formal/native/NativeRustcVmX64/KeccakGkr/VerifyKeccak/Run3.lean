module

public import NativeRustcVmX64.KeccakGkr.VerifyKeccak.Tpl
public import NativeRustcVmX64.Code.Vm.VerifyKeccak
public meta import NativeRustcVmX64.KeccakGkr.VerifyKeccak.Tpl
public meta import NativeRustcVmX64.Code.Vm.VerifyKeccak

/-!
# `verify_keccak`'s blocks b41–b73, run from their templates (x86-64)
-/

namespace NativeRustcVmX64.KeccakGkr.VerifyKeccak

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Vm.VerifyKeccak

set_option Elab.async false

sym_block run_b41 := exec b41 t41
sym_block run_b42 := exec b42 t42
sym_block run_b43 := exec b43 t43
sym_block run_b44 := exec b44 t44
sym_block run_b45 := exec b45 t45
sym_block run_b46 := exec b46 t45
sym_block run_b47 := exec b47 t45
sym_block run_b48 := exec b48 t45
sym_block run_b49 := exec b49 t45
sym_block run_b50 := exec b50 t45
sym_block run_b51 := exec b51 t45
sym_block run_b52 := exec b52 t52
sym_block run_b53 := exec b53 t52
sym_block run_b54 := exec b54 t52
sym_block run_b55 := exec b55 t52
sym_block run_b56 := exec b56 t56
sym_block run_b57 := exec b57 t57
sym_block run_b58 := exec b58 t58
sym_block run_b59 := exec b59 t59
sym_block run_b60 := exec b60 t60
sym_block run_b61 := exec b61 t60
sym_block run_b62 := exec b62 t61
sym_block run_b63 := exec b63 t62
sym_block run_b64 := exec b64 t60
sym_block run_b65 := exec b65 t60
sym_block run_b66 := exec b66 t66
sym_block run_b67 := exec b67 t60
sym_block run_b68 := exec b68 t60
sym_block run_b69 := exec b69 t69
sym_block run_b70 := exec b70 t69
sym_block run_b71 := exec b71 t69
sym_block run_b72 := exec b72 tM
sym_block run_b73 := exec b73 tF
sym_block run_b73ok := exec b73 tOk
sym_block run_b73e := exec b73 t2

end NativeRustcVmX64.KeccakGkr.VerifyKeccak
