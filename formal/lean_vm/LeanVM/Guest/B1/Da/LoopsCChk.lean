/-
  LeanVM.Guest.B1.Da.LoopsCChk

  The bodies of the DA loops, as blocks then the closing tail call, by kernel evaluation: the blob
  loop `da_verify_loop0`, the padding loop `da_pad_loop0` and a blob's cell loop
  `da_verify_blob_loop0`.
-/

module

public import LeanVM.Guest.B1.Da.VerifyDefs
public import LeanVM.Guest.Data.NameStrings

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
  [.call "da_verify_blob" [.n 2] [.n 4, .n 5], .atom (.mul (.n 6) (.n 0) (.n 0)),
    .atom (.mul (.n 7) (.n 3) (.n 6)), .atom (.load (.n 4) (.n 7) 0),
    .atom (.load (.n 5) (.n 7) 1)] ++ stepAtC 8

/-- `da_pad_loop0`'s block: the padding blob's root at `roots·n_blob²·x²`. -/
def padLPre : List Stmt :=
  [.atom (.mul (.n 4) (.n 3) (.n 3)), .atom (.mul (.n 5) (.n 2) (.n 4)),
    .atom (.mul (.n 6) (.n 0) (.n 0)), .atom (.mul (.n 7) (.n 5) (.n 6)),
    .atom (.const (.n 8) (word 8002054802297438051 4108169256045952147)),
    .atom (.load (.n 8) (.n 7) 0),
    .atom (.const (.n 9) (word 12830724869163462953 1721925254677230945)),
    .atom (.load (.n 9) (.n 7) 1)] ++ stepAtC 10

/-- `da_verify_blob_loop0(xb, weights, base)`'s block: cell `xb`'s check on `weights[xb]`, the
running sum's step from word `512` to `513` at `base·xb`, the digest at the leaf `base·xb²`, then
the step to `xb·g` and its test `xb·g + g^128`. -/
def cellLPre : List Stmt :=
  [.atom (.mul (.n 3) (.n 1) (.n 0)), .atom (.load (.n 4) (.n 3) 0),
    .call "da_verify_cell" [.n 4] [.n 5, .n 6, .n 7], .atom (.mul (.n 8) (.n 2) (.n 0)),
    .atom (.load (.n 9) (.n 8) 512), .atom (.add (.n 10) (.n 9) (.n 7)),
    .atom (.load (.n 10) (.n 8) 513), .atom (.mul (.n 11) (.n 0) (.n 0)),
    .atom (.mul (.n 12) (.n 2) (.n 11)), .atom (.load (.n 5) (.n 12) 0),
    .atom (.load (.n 6) (.n 12) 1), .atom (.const (.n 13) (word 2 0)),
    .atom (.mul (.n 14) (.n 0) (.n 13)), .atom (.const (.n 15) (word 325 0)),
    .atom (.add (.n 16) (.n 14) (.n 15)), .atom (.const (.n 17) (word 2 0)),
    .atom (.mul (.n 18) (.n 0) (.n 17))]

/-- `da_verify_blob_loop0`'s body: its block and the tail call. -/
def cellLBody : List Stmt :=
  cellLPre ++ [.callIf (.n 16) name% «da_verify_blob_loop0» [.n 18, .n 1, .n 2], .ret []]

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
    (coreProgram.getD idx% «da_verify_blob_loop0» default).params = [.n 0, .n 1, .n 2] := by
  decide +kernel

end
end LeanVM.Guest.B1.Da
