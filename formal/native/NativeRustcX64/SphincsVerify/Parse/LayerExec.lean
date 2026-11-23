module

public import NativeRustcX64.SphincsVerify.Parse.Env
public meta import NativeRustcX64.Code.Sphincs.SphincsVerify
public meta import NativeRustcX64.SphincsVerify.Parse.State

/-!
# The layers' and the assembly's blocks run by the executor (`b14 .. b42`, x86-64)

In the frame (`fS`, the registers each reads known); a layer's chain-value loop (`b16`, `b24`,
`b32`) with region 0 the frame's bytes from the turn's source to its destination (`spanS`).
-/

namespace NativeRustcX64.SphincsVerifyProof.Parse

open NativeRustcX64.Sym NativeRustcX64.Sphincs.SphincsVerify

set_option Elab.async false

sym_block run_b14 := exec b14 (fS [])
sym_block run_b15 := exec b15 (fS [])
sym_block run_b16 := exec b16 (spanS .r14 (20588 - 15648) (-((15648 : Nat) : Int)))
sym_block run_b17 := exec b17 (fS [])
sym_block run_b18 := exec b18 (fS [(.r14, .ptr 0 560), (.r13, .label "memcpy")])
sym_block run_b19 := exec b19 (fS [(.r12, .ptr 0 2056), (.r13, .label "memcpy")])
sym_block run_b20 := exec b20 (fS [(.r14, .ptr 0 3080), (.r13, .label "memcpy")])
sym_block run_b21 := exec b21 (fS [(.r12, .ptr 0 19144), (.r13, .label "memcpy")])
sym_block run_b22 := exec b22 (fS [(.r14, .ptr 0 10376), (.r13, .label "memcpy")])
sym_block run_b23 := exec b23 (fS [])
sym_block run_b24 := exec b24 (spanS .rax (20588 - 16804) (-((16804 : Nat) : Int)))
sym_block run_b25 := exec b25 (fS [])
sym_block run_b26 := exec b26 (fS [(.rbx, .ptr 0 1720), (.r14, .ptr 0 560), (.rbp, .label "memcpy")])
sym_block run_b27 := exec b27 (fS [(.rbx, .ptr 0 2056), (.rbp, .label "memcpy")])
sym_block run_b28 := exec b28 (fS [(.r14, .ptr 0 3080), (.rbp, .label "memcpy")])
sym_block run_b29 := exec b29 (fS [(.rbx, .ptr 0 19144), (.rbp, .label "memcpy")])
sym_block run_b30 := exec b30 (fS [(.r14, .ptr 0 10376), (.rbp, .label "memcpy")])
sym_block run_b31 := exec b31 (fS [])
sym_block run_b32 := exec b32 (spanS .rax (20588 - 17960) (-((17960 : Nat) : Int)))
sym_block run_b33 := exec b33 (fS [(.rbp, .label "memcpy")])
sym_block run_b34 := exec b34 (fS [(.rbx, .ptr 0 560), (.rbp, .label "memcpy")])
sym_block run_b35 := exec b35 (fS [(.r14, .ptr 0 2056), (.rbp, .label "memcpy")])
sym_block run_b36 := exec b36 (fS [(.rbx, .ptr 0 3080), (.rbp, .label "memcpy")])
sym_block run_b37 := exec b37 (fS [(.r15, .ptr 0 19144), (.rbp, .label "memcpy")])
sym_block run_b38 := exec b38 (fS [(.rbp, .label "memcpy")])
sym_block run_b39 := exec b39 (fS [(.rbp, .label "memcpy")])
sym_block run_b40 := exec b40 (fS [(.rbp, .label "memcpy")])
sym_block run_b41 := exec b41 (fS [(.rbx, .ptr 0 10376), (.rbp, .label "memcpy")])
sym_block run_b42 := exec b42 (fS [(.rbp, .label "memcpy")])

end NativeRustcX64.SphincsVerifyProof.Parse
