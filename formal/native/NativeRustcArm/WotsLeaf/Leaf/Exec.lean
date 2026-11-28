module

public import NativeRustcArm.Code.Xmss.WotsLeaf.Names

public import NativeRustcArm.WotsLeaf.Steps
public import NativeRustcArm.SphincsVerify.InlineTh.ByteNF
public import NativeRustcArm.Code.Xmss.WotsLeaf
public meta import NativeRustcArm.Code.Xmss.WotsLeaf
public meta import NativeRustcArm.WotsLeaf.FrameS

/-!
# The leaf's blocks, run by the symbolic executor

`b44 .. b48` in the frame (`frameS []`); `b49` (the result written to `out`) with `out` as region
1, reached by the address loaded from the frame's byte 0 (`s49`, an alias). `outOK` checks on
`b49`'s literal post-state that `out`'s 75 bytes are the tag `1`, the codeword's 58 bytes at 380
and the leaf's 16 at 2128 (`outByte`), its other writes in the frame below the saved registers
(`frameOrOut`); `outOK_b49` by the kernel.
-/

namespace NativeRustcArm.WotsLeafProof.Leaf

open NativeRustcArm.Sym NativeRustcArm.Xmss.WotsLeaf NativeRustcArm.SphincsVerifyProof.InlineTh

@[expose] public section

/-- At `b49`: the frame, `out` (region 1) at the address the frame's byte 0 holds. -/
def s49 : SState := init [(2752, true), (75, false)] (.ptr 0 0) [] [] [] [(.load 0 0 8, 1, 0)]

/-- `out`'s byte `i`: the tag `1`, codeword byte `i - 1`, leaf byte `i - 59`. -/
def outByte (i : Nat) : XB :=
  if i = 0 then ⟨1, []⟩ else if i < 59 then ⟨0, [(0, 380 + (i - 1))]⟩ else ⟨0, [(0, 2128 + (i - 59))]⟩

/-- The writes in the frame below the saved registers or in `out`. -/
def frameOrOut (S : SState) : Bool :=
  S.mem.all fun w ↦ (w.r == 0 && decide (w.off + w.n ≤ 2656)) || (w.r == 1 && decide (w.off + w.n ≤ 75))

/-- What `b49` does (decided on the literal state). -/
def outOK : Bool :=
  match exec b49 s49 with
  | some (S, x) =>
    (List.range 75).all (fun i ↦ match findWrite 1 i S.mem with
      | some (v, t) => symByte 64 v t == some (outByte i)
      | none => false) &&
    frameOrOut S && Run.inRegions S && Run.noWriteIn S 2656 96 && S.sp == .ptr 0 0 &&
    x == .jump NativeRustcArm.Xmss.WotsLeaf.label_6
  | none => false

end

set_option Elab.async false

sym_block run_b44 := exec b44 (frameS [])
sym_block run_b45 := exec b45 (frameS [])
sym_block run_b46 := exec b46 (frameS [])
sym_block run_b47 := exec b47 (frameS [])
sym_block run_b48 := exec b48 (frameS [])

public theorem outOK_b49 : outOK = true := by decide +kernel

end NativeRustcArm.WotsLeafProof.Leaf
