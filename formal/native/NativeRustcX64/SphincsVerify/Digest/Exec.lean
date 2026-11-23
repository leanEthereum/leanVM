module

public import NativeRustcX64.SphincsVerify.Digest.Keep
public import NativeRustcX64.Sym
public meta import NativeRustcX64.Code.Sphincs.SphincsVerify
public meta import NativeRustcX64.SphincsVerify.Digest.State

/-!
# The digest's and the FORS key's blocks, run by the symbolic executor (x86-64)

The blocks `b43 .. b54`, `b56`, `b57` (the digest, around its bit loop) and `b97 .. b103` (the
FORS key) run in the frame (`frameS`: region 0 the frame, RSP its base, region 1 the slots below
it), from the registers each reads (`run_b<k>`).
-/

namespace NativeRustcX64.SphincsVerifyProof.Digest

open NativeRustcX64.Sym NativeRustcX64.Sphincs.SphincsVerify

set_option Elab.async false

sym_block run_b43 := exec b43 (frameS [])
sym_block run_b44 := exec b44 (frameS [(.rbp, .ptr 0 25180), (.r14, .ptr 0 576)])
sym_block run_b45 := exec b45 (frameS [(.r14, .ptr 0 576)])
sym_block run_b46 := exec b46 (frameS [(.r14, .ptr 0 576)])
sym_block run_b47 := exec b47 (frameS [(.r14, .ptr 0 576)])
sym_block run_b48 := exec b48 (frameS [(.r14, .ptr 0 576), (.r12, .label "memcpy")])
sym_block run_b49 := exec b49 (frameS [(.rbp, .ptr 0 4096)])
sym_block run_b50 := exec b50 (frameS [(.rbp, .ptr 0 4096)])
sym_block run_b51 := exec b51 (frameS [(.rbp, .ptr 0 4096), (.r14, .ptr 0 576), (.r12, .label "memcpy")])
sym_block run_b52 := exec b52 (frameS [(.rbp, .ptr 0 4096), (.rbx, .ptr 0 9344)])
sym_block run_b53 := exec b53 (frameS [(.rbp, .ptr 0 4096), (.r15, .ptr 0 11392)])
sym_block run_b54 := exec b54 (frameS [])
sym_block run_b56 := exec b56 (frameS [])
sym_block run_b57 := exec b57 (frameS [])

sym_block run_b97 := exec b97 (frameS [])
sym_block run_b98 := exec b98 (frameS [(.r12, .ptr 0 4096)])
sym_block run_b99 := exec b99 (frameS [(.r12, .ptr 0 4096)])
sym_block run_b100 := exec b100 (frameS [(.r12, .ptr 0 4096)])
sym_block run_b101 := exec b101 (frameS [(.rbp, .ptr 0 576)])
sym_block run_b102 := exec b102 (frameS [(.rbp, .ptr 0 576)])
sym_block run_b103 := exec b103 (frameS [])

end NativeRustcX64.SphincsVerifyProof.Digest
