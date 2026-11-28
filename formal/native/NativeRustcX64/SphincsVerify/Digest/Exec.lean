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

sym_block run_b34 := exec b34 (frameS [])
sym_block run_b35 := exec b35 (frameS [(.r13, .ptr 0 17420), (.r14, .ptr 0 560)])
sym_block run_b36 := exec b36 (frameS [(.r14, .ptr 0 560)])
sym_block run_b37 := exec b37 (frameS [(.r14, .ptr 0 560)])
sym_block run_b38 := exec b38 (frameS [(.r14, .ptr 0 560)])
sym_block run_b39 := exec b39 (frameS [(.r14, .ptr 0 560), (.rbp, .label "memcpy")])
sym_block run_b40 := exec b40 (frameS [(.r13, .ptr 0 4072)])
sym_block run_b41 := exec b41 (frameS [(.r13, .ptr 0 4072)])
sym_block run_b42 := exec b42 (frameS [(.r13, .ptr 0 4072), (.r14, .ptr 0 560), (.rbp, .label "memcpy")])
sym_block run_b43 := exec b43 (frameS [(.r13, .ptr 0 4072), (.rbx, .ptr 0 3048)])
sym_block run_b44 := exec b44 (frameS [(.r13, .ptr 0 4072), (.r15, .ptr 0 10344)])
sym_block run_b45 := exec b45 (frameS [])
sym_block run_b47 := exec b47 (frameS [])
sym_block run_b48 := exec b48 (frameS [])

sym_block run_b88 := exec b88 (frameS [])
sym_block run_b89 := exec b89 (frameS [(.r12, .ptr 0 4072)])
sym_block run_b90 := exec b90 (frameS [(.r12, .ptr 0 4072)])
sym_block run_b91 := exec b91 (frameS [(.r12, .ptr 0 4072)])
sym_block run_b92 := exec b92 (frameS [(.rbp, .ptr 0 560)])
sym_block run_b93 := exec b93 (frameS [(.rbp, .ptr 0 560)])
sym_block run_b94 := exec b94 (frameS [])

end NativeRustcX64.SphincsVerifyProof.Digest
