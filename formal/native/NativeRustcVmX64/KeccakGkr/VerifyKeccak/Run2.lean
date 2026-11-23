module

public import NativeRustcVmX64.KeccakGkr.VerifyKeccak.Tpl
public import NativeRustcVmX64.Code.Vm.VerifyKeccak
public meta import NativeRustcVmX64.KeccakGkr.VerifyKeccak.Tpl
public meta import NativeRustcVmX64.Code.Vm.VerifyKeccak

/-!
# `verify_keccak`'s blocks b17–b40, run from their templates (x86-64)
-/

namespace NativeRustcVmX64.KeccakGkr.VerifyKeccak

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Vm.VerifyKeccak

set_option Elab.async false

sym_block run_b17 := exec b17 tL
sym_block run_b18 := exec b18 tL
sym_block run_b19 := exec b19 tL
sym_block run_b20 := exec b20 tL
sym_block run_b21 := exec b21 tL
sym_block run_b22 := exec b22 tL
sym_block run_b23 := exec b23 tL
sym_block run_b24 := exec b24 tL
sym_block run_b25 := exec b25 tL
sym_block run_b26 := exec b26 tL
sym_block run_b27 := exec b27 tL
sym_block run_b28 := exec b28 tL
sym_block run_b29 := exec b29 tL
sym_block run_b30 := exec b30 tL
sym_block run_b31 := exec b31 tL
sym_block run_b32 := exec b32 tL
sym_block run_b33 := exec b33 tL
sym_block run_b34 := exec b34 tL
sym_block run_b35 := exec b35 tL
sym_block run_b36 := exec b36 tL
sym_block run_b37 := exec b37 tL
sym_block run_b38 := exec b38 tL
sym_block run_b39 := exec b39 tL
sym_block run_b40 := exec b40 tL

end NativeRustcVmX64.KeccakGkr.VerifyKeccak
