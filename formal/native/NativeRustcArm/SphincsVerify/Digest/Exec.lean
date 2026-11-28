module

public import NativeRustcArm.Sym
public import NativeRustcArm.Code.Sphincs.SphincsVerify
public meta import NativeRustcArm.Code.Sphincs.SphincsVerify

/-!
# The digest's and the FORS key's blocks, run by the symbolic executor

The blocks `b36 .. b47`, `b49` (the digest, before and after its bit loop) and `b85 .. b91` (the
FORS key) run in the frame (region 0, SP its base, X29 the saved registers, `frameS`), from the
registers each reads (`run_b<k>`). The bit loop `b48` (`.LSphincsVerify_11`) runs in its own
regions (`s48`): region 0 the 64 bytes of `h_msg` it reads at X19 (by the bit index X8, each of
its nine byte indices bounded by `30`), region 1 the leaf's 8 bytes it stores at X9.
-/

namespace NativeRustcArm.SphincsVerifyProof.Digest

open NativeRustcArm.Sym NativeRustcArm.Sphincs.SphincsVerify

@[expose] public section

/-- The frame (region 0), SP its base, X29 the saved registers, the registers `k`. -/
def frameS (k : List (XReg × Sym)) : SState :=
  init [(21616, true)] (.ptr 0 0) ((.X29, .ptr 0 21520) :: k)

/-- The byte index of bit `X8 + j` of `h_msg`, as the loop computes it (`lsr`). -/
def bix (j : Nat) : Sym :=
  .un (.ubfm 3 63) .W64 (if j = 0 then .reg .X8 else .bin .add .W64 (.reg .X8) (.lit j))

/-- At `b48`: `h_msg` (region 0, X19), the leaf's word (region 1, X9), X10 `6`; the byte indices
below `30`. -/
def s48 : SState :=
  init [(64, false), (8, false)] .sp [(.X19, .ptr 0 0), (.X9, .ptr 1 0), (.X10, .lit 6)] []
    ([0, 2, 3, 4, 5, 6, 7, 8, 9].map fun j ↦ (bix j, 30))

end

set_option Elab.async false

sym_block run_b36 := exec b36 (frameS [])
sym_block run_b37 := exec b37 (frameS [(.X25, .ptr 0 484), (.X26, .lit 4640)])
sym_block run_b38 := exec b38 (frameS [])
sym_block run_b39 := exec b39 (frameS [(.X20, .ptr 0 448)])
sym_block run_b40 := exec b40 (frameS [])
sym_block run_b41 := exec b41 (frameS [])
sym_block run_b42 := exec b42 (frameS [])
sym_block run_b43 := exec b43 (frameS [])
sym_block run_b44 := exec b44 (frameS [])
sym_block run_b45 := exec b45 (frameS [])
sym_block run_b46 := exec b46 (frameS [])
sym_block run_b47 := exec b47 (frameS [])
sym_block run_b48 := exec b48 s48
sym_block run_b49 := exec b49 (frameS [])

sym_block run_b85 := exec b85 (frameS [(.X23, .ptr 0 15936)])
sym_block run_b86 := exec b86 (frameS [])
sym_block run_b87 := exec b87 (frameS [])
sym_block run_b88 := exec b88 (frameS [])
sym_block run_b89 := exec b89 (frameS [])
sym_block run_b90 := exec b90 (frameS [])
sym_block run_b91 := exec b91 (frameS [(.X19, .ptr 0 19008), (.X20, .ptr 0 8640)])

end NativeRustcArm.SphincsVerifyProof.Digest
