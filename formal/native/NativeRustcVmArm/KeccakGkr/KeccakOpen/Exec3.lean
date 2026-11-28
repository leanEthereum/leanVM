module

public import NativeRustcVmArm.KeccakGkr.KeccakOpen.States
public import NativeRustcVmArm.Code.Vm.KeccakOpen
public meta import NativeRustcVmArm.KeccakGkr.KeccakOpen.States
public meta import NativeRustcVmArm.Code.Vm.KeccakOpen

/-!
# `keccak_open`'s blocks, run by the symbolic executor: the unrolled rounds 3 to 5
-/

namespace NativeRustcVmArm.KeccakGkr.KeccakOpen

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.KeccakOpen

set_option Elab.async false

sym_block run_b58 := exec b58 (pS k58)
sym_block run_b59 := exec b59 (pS k38)
sym_block run_b60 := exec b60 (pS k38)
sym_block run_b61 := exec b61 (loS .X27 .X28 .X29)
sym_block run_b62 := exec b62 (dstS 0)
sym_block run_b63 := exec b63 (pS k38)
sym_block run_b64 := exec b64 (pS k38)
sym_block run_b65 := exec b65 (pS k38)
sym_block run_b66 := exec b66 (loS .X27 .X28 .X29)
sym_block run_b67 := exec b67 (dstS 1024)
sym_block run_b68 := exec b68 (pS k38)
sym_block run_b69 := exec b69 (pS k38)
sym_block run_b70 := exec b70 (pS k70)
sym_block run_b71 := exec b71 (loS .X27 .X24 .X28)
sym_block run_b72 := exec b72 (dstS 2048)
sym_block run_b73 := exec b73 (pS k73)
sym_block run_b74 := exec b74 (pS k74)
sym_block run_b75 := exec b75 (pS k75)
sym_block run_b76 := exec b76 (loS .X24 .X25 .X26)
sym_block run_b77 := exec b77 (dstS 3072)
sym_block run_b78 := exec b78 (pS k78)
sym_block run_b79 := exec b79 (pS k79)
sym_block run_b80 := exec b80 (pS k79)
sym_block run_b81 := exec b81 (loS .X24 .X25 .X26)
sym_block run_b82 := exec b82 (dstS 0)
sym_block run_b83 := exec b83 (pS k79)
sym_block run_b84 := exec b84 (pS k79)
sym_block run_b85 := exec b85 (pS k79)
sym_block run_b86 := exec b86 (loS .X24 .X25 .X26)
sym_block run_b87 := exec b87 (dstS 1024)
sym_block run_b88 := exec b88 (pS k88)
sym_block run_b89 := exec b89 (pS k89)
sym_block run_b90 := exec b90 (pS k90)
sym_block run_b91 := exec b91 lo5S
sym_block run_b92 := exec b92 st5S

end NativeRustcVmArm.KeccakGkr.KeccakOpen
