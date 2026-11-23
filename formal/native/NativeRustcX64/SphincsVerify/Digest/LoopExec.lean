module

public import NativeRustcX64.SphincsVerify.Digest.LoopState
public import NativeRustcX64.Sym
public import NativeRustcX64.Code.Sphincs.SphincsVerify
public meta import NativeRustcX64.SphincsVerify.Digest.LoopState
public meta import NativeRustcX64.Code.Sphincs.SphincsVerify

/-!
# The digest's bit loop `b55`, run by the symbolic executor (x86-64)

`run_b55`: one turn from `s55`; `leafSym`, the leaf's value it stores at R13.
-/

namespace NativeRustcX64.SphincsVerifyProof.Digest

open NativeRustcX64.Sym NativeRustcX64.Sphincs.SphincsVerify

set_option Elab.async false

sym_block run_b55 := exec b55 s55

@[expose] public section

/-- The leaf's value a turn stores (the newest write of `run_b55`'s state). -/
def leafSym : Sym := match exec b55 s55 with
  | some (S, _) => (S.mem.headD ⟨0, 0, 0, .lit 0⟩).v
  | none => .lit 0

end

end NativeRustcX64.SphincsVerifyProof.Digest
