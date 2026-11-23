module

public import NativeRustcVmArm.KeccakGkr.KeccakOpen.States
public import NativeRustcVmArm.Code.Vm.KeccakOpen
public meta import NativeRustcVmArm.KeccakGkr.KeccakOpen.States
public meta import NativeRustcVmArm.Code.Vm.KeccakOpen

/-!
# `keccak_open`'s blocks, run by the symbolic executor: the unrolled round 2
-/

namespace NativeRustcVmArm.KeccakGkr.KeccakOpen

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.KeccakOpen

set_option Elab.async false

sym_block run_b18 := exec b18 (pS kP)
sym_block run_b19 := exec b19 (pS k19)
sym_block run_b20 := exec b20 (pS k20)
sym_block run_b21 := exec b21 (loS .X24 .X25 .X26)
sym_block run_b22 := exec b22 (dstS 0)
sym_block run_b23 := exec b23 (pS k20)
sym_block run_b24 := exec b24 (pS k20)
sym_block run_b25 := exec b25 (pS k20)
sym_block run_b26 := exec b26 (loS .X24 .X25 .X26)
sym_block run_b27 := exec b27 (dstS 1024)
sym_block run_b28 := exec b28 (pS k20)
sym_block run_b29 := exec b29 (pS k29)
sym_block run_b30 := exec b30 (pS k30)
sym_block run_b31 := exec b31 (loS .X25 .X26 .X27)
sym_block run_b32 := exec b32 (dstS 2048)
sym_block run_b33 := exec b33 (pS k30)
sym_block run_b34 := exec b34 (pS k34)
sym_block run_b35 := exec b35 (pS k35)
sym_block run_b36 := exec b36 (loS .X27 .X28 .X29)
sym_block run_b37 := exec b37 (dstS 3072)
sym_block run_b38 := exec b38 (pS k38)
sym_block run_b39 := exec b39 (pS k38)
sym_block run_b40 := exec b40 (pS k38)
sym_block run_b41 := exec b41 (loS .X27 .X28 .X29)
sym_block run_b42 := exec b42 (dstS 4096)
sym_block run_b43 := exec b43 (pS k38)
sym_block run_b44 := exec b44 (pS k38)
sym_block run_b45 := exec b45 (pS k38)
sym_block run_b46 := exec b46 (loS .X27 .X28 .X29)
sym_block run_b47 := exec b47 (dstS 5120)
sym_block run_b48 := exec b48 (pS k38)
sym_block run_b49 := exec b49 (pS k38)
sym_block run_b50 := exec b50 (pS k38)
sym_block run_b51 := exec b51 (loS .X27 .X28 .X29)
sym_block run_b52 := exec b52 (dstS 6144)
sym_block run_b53 := exec b53 (pS k38)
sym_block run_b54 := exec b54 (pS k38)
sym_block run_b55 := exec b55 (pS k38)
sym_block run_b56 := exec b56 (loS .X27 .X28 .X29)
sym_block run_b57 := exec b57 (dstS 7168)

end NativeRustcVmArm.KeccakGkr.KeccakOpen
