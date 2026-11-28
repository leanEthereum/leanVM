module

public import NativeRustcArm.Sym
public import NativeRustcArm.Code.Sphincs.SphincsVerify
public meta import NativeRustcArm.Code.Sphincs.SphincsVerify

/-!
# The digest's and the FORS key's blocks, run by the symbolic executor

The blocks `b45 .. b56`, `b58` (the digest, before and after its bit loop) and `b94 .. b100` (the
FORS key) run in the frame (region 0, SP its base, X29 the saved registers, `frameS`), from the
registers each reads (`run_b<k>`). The bit loop `b57` (`.LSphincsVerify_19`) runs in its own
regions (`s57`): region 0 the 64 bytes of `h_msg` it reads at X21 (by the bit index X8, each of
its nine byte indices bounded by `30`), region 1 the leaf's 8 bytes it stores at X9.
-/

namespace NativeRustcArm.SphincsVerifyProof.Digest

open NativeRustcArm.Sym NativeRustcArm.Sphincs.SphincsVerify

@[expose] public section

/-- The frame (region 0), SP its base, X29 the saved registers, the registers `k`. -/
def frameS (k : List (XReg × Sym)) : SState :=
  init [(29376, true)] (.ptr 0 0) ((.X29, .ptr 0 29280) :: k)

/-- The byte index of bit `X8 + j` of `h_msg`, as the loop computes it (`lsr`). -/
def bix (j : Nat) : Sym :=
  .un (.ubfm 3 63) .W64 (if j = 0 then .reg .X8 else .bin .add .W64 (.reg .X8) (.lit j))

/-- At `b57`: `h_msg` (region 0, X21), the leaf's word (region 1, X9), X10 `6`; the byte indices
below `30`. -/
def s57 : SState :=
  init [(64, false), (8, false)] .sp [(.X21, .ptr 0 0), (.X9, .ptr 1 0), (.X10, .lit 6)] []
    ([0, 2, 3, 4, 5, 6, 7, 8, 9].map fun j ↦ (bix j, 30))

end

set_option Elab.async false

sym_block run_b45 := exec b45 (frameS [])
sym_block run_b46 := exec b46 (frameS [(.X23, .ptr 0 8244), (.X24, .lit 4640)])
sym_block run_b47 := exec b47 (frameS [])
sym_block run_b48 := exec b48 (frameS [(.X19, .ptr 0 8208)])
sym_block run_b49 := exec b49 (frameS [])
sym_block run_b50 := exec b50 (frameS [])
sym_block run_b51 := exec b51 (frameS [])
sym_block run_b52 := exec b52 (frameS [])
sym_block run_b53 := exec b53 (frameS [])
sym_block run_b54 := exec b54 (frameS [(.X23, .ptr 0 21648)])
sym_block run_b55 := exec b55 (frameS [])
sym_block run_b56 := exec b56 (frameS [])
sym_block run_b57 := exec b57 s57
sym_block run_b58 := exec b58 (frameS [(.X23, .ptr 0 21648)])

sym_block run_b94 := exec b94 (frameS [(.X23, .ptr 0 21648)])
sym_block run_b95 := exec b95 (frameS [])
sym_block run_b96 := exec b96 (frameS [])
sym_block run_b97 := exec b97 (frameS [])
sym_block run_b98 := exec b98 (frameS [])
sym_block run_b99 := exec b99 (frameS [])
sym_block run_b100 := exec b100 (frameS [(.X19, .ptr 0 26768), (.X20, .ptr 0 16400)])

end NativeRustcArm.SphincsVerifyProof.Digest
