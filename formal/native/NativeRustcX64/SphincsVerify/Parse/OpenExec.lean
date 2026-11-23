module

public import NativeRustcX64.SphincsVerify.Parse.Env
public meta import NativeRustcX64.Code.Sphincs.SphincsVerify
public meta import NativeRustcX64.SphincsVerify.Parse.State

/-!
# The openings' blocks run by the executor (`b9 .. b13`, x86-64)

In the frame (`fS`): `b9` the key's words stored and the loop's registers; `b10` an opening's
path and secret, its loads at the bounded offset R13 (`fS … [(R13, 4225)]`); `b11`, `b12` the
`memcpy`s' arguments; `b13` the count (no memory).
-/

namespace NativeRustcX64.SphincsVerifyProof.Parse

open NativeRustcX64.Sym NativeRustcX64.Sphincs.SphincsVerify

set_option Elab.async false

sym_block run_b9 := exec b9 (fS [])
sym_block run_b10 := exec b10 (fS [(.rbp, .ptr 0 20700), (.r15, .ptr 0 592), (.r12, .label "memcpy")] [(.reg .r13, 4225)])
sym_block run_b11 := exec b11 (fS [(.r14, .ptr 0 576), (.rbx, .ptr 0 20540), (.r12, .label "memcpy")])
sym_block run_b12 := exec b12 (fS [(.r14, .ptr 0 576), (.r12, .label "memcpy")])
sym_block run_b13 := exec b13 (init [])

end NativeRustcX64.SphincsVerifyProof.Parse
