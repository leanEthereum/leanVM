module

public import NativeRustcX64.SphincsVerify.Frame

/-!
# The frame's symbolic state (x86-64)

`frameS k`: region 0 the frame with the return address (29408 bytes, RSP its base), region 1 the
16 bytes below it where `call` and `push` write (`ptr 0 (-8)`, `ptr 0 (-16)`, as
`Run.frameAliases`), regions 2 and 3 the seeded memcpy and memset GOT slots, the registers `k` known.
-/

namespace NativeRustcX64.SphincsVerifyProof.Digest

open NativeRustcX64.Sym

@[expose] public section

/-- The frame's symbolic state: RSP its base, the registers `k`. -/
def frameS (k : List (Reg64 × Sym)) : SState :=
  Run.frameState k

end

end NativeRustcX64.SphincsVerifyProof.Digest
