module

public import NativeRustcX64.SphincsVerify.Parse.Env
public meta import NativeRustcX64.Code.Sphincs.SphincsVerify
public meta import NativeRustcX64.SphincsVerify.Parse.State

/-!
# The words' blocks run by the executor (`b2 .. b8`, x86-64)

A turn of a word loop runs with region 0 the turn's input words and region 1 the frame's bytes it
writes (`turnS`: the source and destination addresses aliased); `b3`, `b5`, `b7` run in the frame
with the input as region 2 (`fS3`, RBX the context).
-/

namespace NativeRustcX64.SphincsVerifyProof.Parse

open NativeRustcX64.Sym NativeRustcX64.Sphincs.SphincsVerify

set_option Elab.async false

sym_block run_b2 := exec b2 (turnS .r15 40 (-1088) (-11404))
sym_block run_b3 := exec b3 ctxS
sym_block run_b4 := exec b4 (turnS .rax 32 24 (-10288))
sym_block run_b5 := exec b5 ctxS
sym_block run_b6 := exec b6 (turnS .rax 32 24 (-10284))
sym_block run_b7 := exec b7 ctxS
sym_block run_b8 := exec b8 (turnS .rax 32 24 (-10280))

end NativeRustcX64.SphincsVerifyProof.Parse
