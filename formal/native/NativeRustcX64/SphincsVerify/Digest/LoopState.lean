module

public import NativeRustcX64.Sym.Basic

/-!
# The digest's bit loop `b55`: its symbolic state (x86-64)

Turn `c` of `.LSphincsVerify_17` (R13 the bit index `10 c`, RBP the leaf's word): region 0
`h_msg`'s 64 bytes (RSP `ptr 0 (-2048)`, so `2048(%rsp,%rax)` is region 0's byte `%rax`), region 1
the leaf's 8 bytes, region 2 the spill `8(%rsp)`, region 3 the 16 bytes below the frame (the
`push`es of the rewritten `bt`); each byte index `(R13 + j) >> 3` bounded by `30` (`s55`).
-/

namespace NativeRustcX64.SphincsVerifyProof.Digest

open NativeRustcX64.Sym

@[expose] public section

/-- The byte index of bit `R13 + j` of `h_msg`, as the loop computes it (`shr $3`). -/
def bix (j : Nat) : Sym :=
  .bin .shr .W64 (if j = 0 then .reg .r13 else .bin .add .W64 (.reg .r13) (.lit j)) (.lit 3)

/-- At `b55`: `h_msg` (region 0), the leaf's word (region 1, RBP), the spill (region 2), the
pushes' slots (region 3); the byte indices below `30`. -/
def s55 : SState :=
  init [64, 8, 8, 16] [(.rsp, .ptr 0 (-2048)), (.rbp, .ptr 1 0)] []
    ([0, 2, 3, 4, 5, 6, 7, 8, 9].map fun j ↦ (bix j, 30))
    [(.ptr 0 (-2040), 2, 0), (.ptr 0 (-2056), 3, 8), (.ptr 0 (-2064), 3, 0)]

end

end NativeRustcX64.SphincsVerifyProof.Digest
