module

public import NativeRustcX64.SphincsVerify.Parse.Env
public meta import NativeRustcX64.Code.Sphincs.SphincsVerify
public meta import NativeRustcX64.SphincsVerify.Parse.State

/-!
# The layers' and the assembly's blocks run by the executor (`b5 .. b33`, x86-64)

Blocks that read from `sigPtr` run in `fSig`, pure frame blocks in `fS`, and the three layer
chain-value copy loops (`b7`, `b15`, `b23`) in `sigTurnS`.
-/

namespace NativeRustcX64.SphincsVerifyProof.Parse

open NativeRustcX64.Sym NativeRustcX64.Sphincs.SphincsVerify

set_option Elab.async false

sym_block run_b5 := exec b5 (fS [])
sym_block run_b6 := exec b6 (fSig [])
sym_block run_b7 := exec b7 (sigTurnS .r15 4244)
sym_block run_b8 := exec b8 (fS [])
sym_block run_b9 := exec b9 (fSig [(.r13, .ptr 0 560), (.r15, .label "memcpy")])
sym_block run_b10 := exec b10 (fS [(.rbp, .ptr 0 2024), (.r15, .label "memcpy")])
sym_block run_b11 := exec b11 (fS [(.r13, .ptr 0 3048), (.r15, .label "memcpy")])
sym_block run_b12 := exec b12 (fS [(.rbp, .ptr 0 11368), (.r15, .label "memcpy")])
sym_block run_b13 := exec b13 (fS [(.r13, .ptr 0 10344), (.r15, .label "memcpy")])
sym_block run_b14 := exec b14 (fSig [])
sym_block run_b15 := exec b15 (sigTurnS .rax 5400)
sym_block run_b16 := exec b16 (fS [])
sym_block run_b17 := exec b17 (fSig [(.r14, .ptr 0 1720), (.r13, .ptr 0 560), (.r15, .label "memcpy")])
sym_block run_b18 := exec b18 (fS [(.r14, .ptr 0 2024), (.r15, .label "memcpy")])
sym_block run_b19 := exec b19 (fS [(.r13, .ptr 0 3048), (.r15, .label "memcpy")])
sym_block run_b20 := exec b20 (fS [(.r14, .ptr 0 11368), (.r15, .label "memcpy")])
sym_block run_b21 := exec b21 (fS [(.r13, .ptr 0 10344), (.r15, .label "memcpy")])
sym_block run_b22 := exec b22 (fSig [])
sym_block run_b23 := exec b23 (sigTurnS .rax 6556)
sym_block run_b24 := exec b24 (fS [])
sym_block run_b25 := exec b25 (fSig [(.r14, .ptr 0 560), (.rbp, .label "memcpy")])
sym_block run_b26 := exec b26 (fS [(.r13, .ptr 0 2024), (.rbp, .label "memcpy")])
sym_block run_b27 := exec b27 (fS [(.r14, .ptr 0 3048), (.rbp, .label "memcpy")])
sym_block run_b28 := exec b28 (fS [(.r13, .ptr 0 11368), (.rbp, .label "memcpy")])
sym_block run_b29 := exec b29 (fSig [(.rbp, .label "memcpy")])
sym_block run_b30 := exec b30 (fS [(.rbp, .label "memcpy")])
sym_block run_b31 := exec b31 (fS [(.rbp, .label "memcpy")])
sym_block run_b32 := exec b32 (fS [(.r14, .ptr 0 10344), (.rbp, .label "memcpy")])
sym_block run_b33 := exec b33 (fS [(.rbp, .label "memcpy")])

end NativeRustcX64.SphincsVerifyProof.Parse
