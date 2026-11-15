/-
  LeanVM.Guest.B1.Da.LoopsCChk

  The bodies of `da_verify`'s loops and of its columns' row loop, as blocks then the closing
  tail call, by kernel evaluation.
-/

module

public import LeanVM.Guest.B1.Da.VerifyDefs
public import LeanVM.Guest.Data.NameStrings

namespace LeanVM.Guest.B1.Da

open LeanVM.Guest.Core LeanVM.Guest.B1.Digest

@[expose] public section

/-- `x^641` by squarings: `x^2, x^4, x^5, x^10, …, x^640, x^641` into cells `4 … 14`. -/
def l17Pows : List Stmt :=
  [.atom (.mul (.n 4) (.n 0) (.n 0)), .atom (.mul (.n 5) (.n 4) (.n 4)),
    .atom (.mul (.n 6) (.n 5) (.n 0)), .atom (.mul (.n 7) (.n 6) (.n 6)),
    .atom (.mul (.n 8) (.n 7) (.n 7)), .atom (.mul (.n 9) (.n 8) (.n 8)),
    .atom (.mul (.n 10) (.n 9) (.n 9)), .atom (.mul (.n 11) (.n 10) (.n 10)),
    .atom (.mul (.n 12) (.n 11) (.n 11)), .atom (.mul (.n 13) (.n 12) (.n 12)),
    .atom (.mul (.n 14) (.n 13) (.n 0))]

/-- A loop's step: the next counter `x·g` and the test `x·g + N`, from cell `c` on. -/
def stepAtC (c : ℕ) : List Stmt :=
  [.atom (.const (.n c) (word 2 0)), .atom (.mul (.n (c + 1)) (.n 0) (.n c)),
    .atom (.add (.n (c + 2)) (.n (c + 1)) (.n 1)), .atom (.const (.n (c + 3)) (word 2 0)),
    .atom (.mul (.n (c + 4)) (.n 0) (.n (c + 3)))]

/-- `da_verify_loop0`'s block: `rowbase[x] = blobs·x^641`, the region's word `512` zero. -/
def l17Pre : List Stmt :=
  l17Pows ++ [.atom (.mul (.n 15) (.n 2) (.n 14)), .atom (.mul (.n 16) (.n 3) (.n 0)),
    .atom (.load (.n 15) (.n 16) 0), .atom (.const (.n 17) (word 0 0)),
    .atom (.load (.n 17) (.n 15) 512)] ++ stepAtC 18

/-- `da_verify_loop2`'s block: the region's sum zero at word `640`, its tree's root at `roots·x²`.
-/
def l19Pre : List Stmt :=
  [.atom (.mul (.n 4) (.n 2) (.n 0)), .atom (.load (.n 5) (.n 4) 0),
    .atom (.load (.n 6) (.n 5) 640), .atom (.const (.n 7) (word 0 0)),
    .atom (.assertEq (.n 6) (.n 7)), .call "da_levels__L128_L7" [.n 5] [.n 8, .n 9],
    .atom (.mul (.n 10) (.n 0) (.n 0)), .atom (.mul (.n 11) (.n 3) (.n 10)),
    .atom (.load (.n 8) (.n 11) 0), .atom (.load (.n 9) (.n 11) 1)] ++ stepAtC 12

/-- `da_verify_loop3`'s block: the padding blob's root at `roots·n_blob²·x²`. -/
def l20Pre : List Stmt :=
  [.atom (.mul (.n 4) (.n 3) (.n 3)), .atom (.mul (.n 5) (.n 2) (.n 4)),
    .atom (.mul (.n 6) (.n 0) (.n 0)), .atom (.mul (.n 7) (.n 5) (.n 6)),
    .atom (.const (.n 8) (word 8002054802297438051 4108169256045952147)),
    .atom (.load (.n 8) (.n 7) 0),
    .atom (.const (.n 9) (word 12830724869163462953 1721925254677230945)),
    .atom (.load (.n 9) (.n 7) 1)] ++ stepAtC 10

/-- `da_verify_column_loop0`'s block: a blob's cell in column `xb`, its running sum's step and its
digest at the
blob tree's leaf. -/
def l21Pre : List Stmt :=
  [.call "da_verify_cell" [.n 2] [.n 6, .n 7, .n 8], .atom (.mul (.n 9) (.n 3) (.n 0)),
    .atom (.load (.n 10) (.n 9) 0), .atom (.mul (.n 11) (.n 10) (.n 4)),
    .atom (.load (.n 12) (.n 11) 512), .atom (.add (.n 13) (.n 12) (.n 8)),
    .atom (.load (.n 13) (.n 11) 513), .atom (.mul (.n 14) (.n 10) (.n 5)),
    .atom (.load (.n 6) (.n 14) 0), .atom (.load (.n 7) (.n 14) 1)] ++ stepAtC 15

/-- A loop's closing tail call from its step at cell `c`. -/
def tailAt (f : String) (c n : ℕ) : List Stmt :=
  [.callIf (.n (c + 2)) f (.n (c + 4) :: (List.range n).map fun k => V.n (k + 1)), .ret []]

set_option maxRecDepth 100000 in
theorem dv_loops_body : Fn.body (coreProgram.getD idx% «da_verify_loop0» default) = l17Pre ++
    tailAt name% «da_verify_loop0» 18 3 ∧
    Fn.body (coreProgram.getD idx% «da_verify_loop2» default) = l19Pre ++ tailAt
        name% «da_verify_loop2» 12 3 ∧
    Fn.body (coreProgram.getD idx% «da_verify_loop3» default) = l20Pre ++ tailAt
        name% «da_verify_loop3» 10 3 ∧
    Fn.body (coreProgram.getD idx% «da_verify_column_loop0» default) = l21Pre ++ tailAt
        name% «da_verify_column_loop0» 15 5 := by
  refine ⟨stmtsEqb_sound ?_, stmtsEqb_sound ?_, stmtsEqb_sound ?_, stmtsEqb_sound ?_⟩ <;>
    decide +kernel

set_option maxRecDepth 100000 in
theorem dv_loops_shape :
    (loopShapeF (coreProgram.getD idx% «da_verify_loop0» default) name% «da_verify_loop0» = true ∧
      (coreProgram.getD idx% «da_verify_loop0» default).params.length = 4) ∧
    (loopShapeF (coreProgram.getD idx% «da_verify_loop2» default) name% «da_verify_loop2» = true ∧
      (coreProgram.getD idx% «da_verify_loop2» default).params.length = 4) ∧
    (loopShapeF (coreProgram.getD idx% «da_verify_loop3» default) name% «da_verify_loop3» = true ∧
      (coreProgram.getD idx% «da_verify_loop3» default).params.length = 4) ∧
    (loopShapeF (coreProgram.getD idx% «da_verify_column_loop0» default)
        name% «da_verify_column_loop0» = true ∧
      (coreProgram.getD idx% «da_verify_column_loop0» default).params.length = 6) := by
  decide +kernel

end
end LeanVM.Guest.B1.Da
