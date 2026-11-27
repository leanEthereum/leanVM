/-
  LeanVM.Guest.B1.Da.LoopsCChk

  The bodies of the DA loops, as blocks then the closing tail call, by kernel evaluation: the blob
  loop `da_verify_loop0`, the padding loop `da_pad_loop0` and a blob's cell loop
  `da_verify_blob_loop0`.
-/

module

public import LeanVM.Guest.B1.Da.VerifyDefs
public import LeanVM.Guest.Data.NameStrings
import LeanVM.Guest.ValRef
import LeanVM.Guest.Data.ValNames.«da_pad_loop0»
import LeanVM.Guest.Data.ValNames.«da_verify_blob_loop0»
import LeanVM.Guest.Data.ValNames.«da_verify_loop0»
import LeanVM.Guest.StmtsAppend

namespace LeanVM.Guest.B1.Da

open LeanVM.Guest.Core LeanVM.Guest.B1.Digest

@[expose] public section

/-- A loop's step: the next counter `x·g` and the test `x·g + N`, from cell `c` on. -/
def stepAtC (c : ℕ) : List Stmt :=
  [.atom (.const (.n c) (word 2 0)), .atom (.mul (.n (c + 1)) (.n 0) (.n c)),
    .atom (.add (.n (c + 2)) (.n (c + 1)) (.n 1)), .atom (.const (.n (c + 3)) (word 2 0)),
    .atom (.mul (.n (c + 4)) (.n 0) (.n (c + 3)))]

/-- A loop's closing tail call from its step at cell `c`. -/
def tailAt (f : String) (c n : ℕ) : List Stmt :=
  [.callIf (.n (c + 2)) f (.n (c + 4) :: (List.range n).map fun k => V.n (k + 1)), .ret []]

/-- `da_verify_loop0`'s block: blob `x`'s check on the weights, its root at `roots·x²`. -/
def blobLPre : List Stmt :=
  [.call "da_verify_blob" [.n (val% «da_verify_loop0» "weights")] [.n (val% «da_verify_loop0» "b0"), .n (val% «da_verify_loop0» "b1")], .atom (.mul (.n (val% «da_verify_loop0» "slot~0")) (.n (val% «da_verify_loop0» "xi")) (.n (val% «da_verify_loop0» "xi"))),
    .atom (.mul (.n (val% «da_verify_loop0» "slot")) (.n (val% «da_verify_loop0» "roots")) (.n (val% «da_verify_loop0» "slot~0"))), .atom (.load (.n (val% «da_verify_loop0» "b0")) (.n (val% «da_verify_loop0» "slot")) 0),
    .atom (.load (.n (val% «da_verify_loop0» "b1")) (.n (val% «da_verify_loop0» "slot")) 1)] ⧺ stepAtC 8

/-- `da_pad_loop0`'s block: the padding blob's root at `roots·n_blob²·x²`. -/
def padLPre : List Stmt :=
  [.atom (.mul (.n (val% «da_pad_loop0» "pad~0")) (.n (val% «da_pad_loop0» "n_blob_g")) (.n (val% «da_pad_loop0» "n_blob_g"))), .atom (.mul (.n (val% «da_pad_loop0» "pad~1")) (.n (val% «da_pad_loop0» "roots")) (.n (val% «da_pad_loop0» "pad~0"))),
    .atom (.mul (.n (val% «da_pad_loop0» "pad~2")) (.n (val% «da_pad_loop0» "xd")) (.n (val% «da_pad_loop0» "xd"))), .atom (.mul (.n (val% «da_pad_loop0» "pad")) (.n (val% «da_pad_loop0» "pad~1")) (.n (val% «da_pad_loop0» "pad~2"))),
    .atom (.const (.n (val% «da_pad_loop0» "s1#0")) (word 8002054802297438051 4108169256045952147)),
    .atom (.load (.n (val% «da_pad_loop0» "s1#0")) (.n (val% «da_pad_loop0» "pad")) 0),
    .atom (.const (.n (val% «da_pad_loop0» "s2#0")) (word 12830724869163462953 1721925254677230945)),
    .atom (.load (.n (val% «da_pad_loop0» "s2#0")) (.n (val% «da_pad_loop0» "pad")) 1)] ⧺ stepAtC 10

/-- `da_verify_blob_loop0(xb, weights, base)`'s block: cell `xb`'s check on `weights[xb]`, the
running sum's step from word `512` to `513` at `base·xb`, the digest at the leaf `base·xb²`, then
the step to `xb·g` and its test `xb·g + g^128`. -/
def cellLPre : List Stmt :=
  [.atom (.mul (.n (val% «da_verify_blob_loop0» "d0~3")) (.n (val% «da_verify_blob_loop0» "weights")) (.n (val% «da_verify_blob_loop0» "xb"))), .atom (.load (.n (val% «da_verify_blob_loop0» "d0~4")) (.n (val% «da_verify_blob_loop0» "d0~3")) 0),
    .call "da_verify_cell" [.n (val% «da_verify_blob_loop0» "d0~4")] [.n (val% «da_verify_blob_loop0» "d0"), .n (val% «da_verify_blob_loop0» "d1"), .n (val% «da_verify_blob_loop0» "s")], .atom (.mul (.n (val% «da_verify_blob_loop0» "chain")) (.n (val% «da_verify_blob_loop0» "base")) (.n (val% «da_verify_blob_loop0» "xb"))),
    .atom (.load (.n (val% «da_verify_blob_loop0» "s2#0")) (.n (val% «da_verify_blob_loop0» "chain")) 512), .atom (.add (.n (val% «da_verify_blob_loop0» "s2#1")) (.n (val% «da_verify_blob_loop0» "s2#0")) (.n (val% «da_verify_blob_loop0» "s"))),
    .atom (.load (.n (val% «da_verify_blob_loop0» "s2#1")) (.n (val% «da_verify_blob_loop0» "chain")) 513), .atom (.mul (.n (val% «da_verify_blob_loop0» "leaf~0")) (.n (val% «da_verify_blob_loop0» "xb")) (.n (val% «da_verify_blob_loop0» "xb"))),
    .atom (.mul (.n (val% «da_verify_blob_loop0» "leaf")) (.n (val% «da_verify_blob_loop0» "base")) (.n (val% «da_verify_blob_loop0» "leaf~0"))), .atom (.load (.n (val% «da_verify_blob_loop0» "d0")) (.n (val% «da_verify_blob_loop0» "leaf")) 0),
    .atom (.load (.n (val% «da_verify_blob_loop0» "d1")) (.n (val% «da_verify_blob_loop0» "leaf")) 1), .atom (.const (.n (val% «da_verify_blob_loop0» "s7#0")) (word 2 0)),
    .atom (.mul (.n (val% «da_verify_blob_loop0» "s7#1")) (.n (val% «da_verify_blob_loop0» "xb")) (.n (val% «da_verify_blob_loop0» "s7#0"))), .atom (.const (.n (val% «da_verify_blob_loop0» "s7#2")) (word 325 0)),
    .atom (.add (.n (val% «da_verify_blob_loop0» "s7#3")) (.n (val% «da_verify_blob_loop0» "s7#1")) (.n (val% «da_verify_blob_loop0» "s7#2"))), .atom (.const (.n (val% «da_verify_blob_loop0» "s7#4")) (word 2 0)),
    .atom (.mul (.n (val% «da_verify_blob_loop0» "s7#5")) (.n (val% «da_verify_blob_loop0» "xb")) (.n (val% «da_verify_blob_loop0» "s7#4")))]

/-- `da_verify_blob_loop0`'s body: its block and the tail call. -/
def cellLBody : List Stmt :=
  cellLPre ⧺ [.callIf (.n (val% «da_verify_blob_loop0» "s7#3")) name% «da_verify_blob_loop0» [.n (val% «da_verify_blob_loop0» "s7#5"), .n (val% «da_verify_blob_loop0» "weights"), .n (val% «da_verify_blob_loop0» "base")], .ret []]

set_option maxRecDepth 100000 in
theorem dv_loops_body : Fn.body (coreProgram.getD idx% «da_verify_loop0» default) = blobLPre ++
    tailAt name% «da_verify_loop0» 8 3 ∧
    Fn.body (coreProgram.getD idx% «da_pad_loop0» default) = padLPre ++
      tailAt name% «da_pad_loop0» 10 3 ∧
    Fn.body (coreProgram.getD idx% «da_verify_blob_loop0» default) = cellLBody := by
  refine ⟨stmtsEqb_sound ?_, stmtsEqb_sound ?_, stmtsEqb_sound ?_⟩ <;> decide +kernel

set_option maxRecDepth 100000 in
theorem dv_loops_shape :
    (loopShapeF (coreProgram.getD idx% «da_verify_loop0» default) name% «da_verify_loop0» = true ∧
      (coreProgram.getD idx% «da_verify_loop0» default).params.length = 4) ∧
    (loopShapeF (coreProgram.getD idx% «da_pad_loop0» default) name% «da_pad_loop0» = true ∧
      (coreProgram.getD idx% «da_pad_loop0» default).params.length = 4) ∧
    (coreProgram.getD idx% «da_verify_blob_loop0» default).params = [.n (val% «da_verify_blob_loop0» "xb"), .n (val% «da_verify_blob_loop0» "weights"), .n (val% «da_verify_blob_loop0» "base")] := by
  decide +kernel

end
end LeanVM.Guest.B1.Da
