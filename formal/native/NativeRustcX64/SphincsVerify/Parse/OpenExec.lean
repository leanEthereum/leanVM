module

public import NativeRustcX64.SphincsVerify.Parse.Env
public meta import NativeRustcX64.Code.Sphincs.SphincsVerify
public meta import NativeRustcX64.SphincsVerify.Parse.State

/-!
# The openings' blocks run by the executor (`b0 .. b4`, x86-64)

`b0`: prologue, stores `msgPtr` at `8`, copies 32-byte `pk` to `112`, sets up the FORS openings
loop registers. `b1 .. b4`: one turn of the 24-opening loop.
-/

namespace NativeRustcX64.SphincsVerifyProof.Parse

open NativeRustcX64.Sym NativeRustcX64.Sphincs.SphincsVerify

set_option Elab.async false

sym_block run_b0 := exec b0 entryS
sym_block run_b1 := exec b1 openS
sym_block run_b2 := exec b2 (fS [(.r13, .ptr 0 560), (.r14, .ptr 0 12780), (.rbp, .label "memcpy")])
sym_block run_b3 := exec b3 (fS [(.r13, .ptr 0 560), (.rbp, .label "memcpy")])
sym_block run_b4 := exec b4 (init [])

end NativeRustcX64.SphincsVerifyProof.Parse
