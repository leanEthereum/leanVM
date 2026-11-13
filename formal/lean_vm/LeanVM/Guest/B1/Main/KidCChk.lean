/-
  LeanVM.Guest.B1.Main.KidCChk

  `main_loop4`'s block (a child), evaluated (by kernel evaluation), for its placed completeness.
-/

module

public import LeanVM.Guest.B1.Main.Loops
public import LeanVM.Guest.B1.Fwd.Canon
public import LeanVM.Guest.Memory.Uniform
public import LeanVM.Guest.Data.NameStrings

/-!
# A child's block, evaluated

`l5Pre`: `main_loop4`'s statements before its tail call (`l5_body`). `l5COk`: the evaluator's
pattern (`chk`), the stores (`l5S`: the statement's digest's two cells into `child_pi_table`, the
next running count), every side condition a load of `written[x]` or of the
child's DA digest's two hinted cells, a store, or a load through one of the child's two counts
(`assert_gpow`).
-/

namespace LeanVM.Guest.B1.Main

open LeanVM.Guest.Core LeanVM.Guest.B1.Fwd LeanVM.Guest.B1.Digest

@[expose] public section

/-- `main_loop4`'s statements before its tail call. -/
def l5Pre : List Stmt := [
    .atom (.mul (.n 16) (.n 2) (.n 0)),
    .atom (.load (.n 17) (.n 16) 0),
    .atom (.hint (.witness "child_meta" (.stack [.n 18, .n 19]))),
    .atom (.touch (.n 20) (.n 18)),
    .atom (.touch (.n 21) (.n 19)),
    .atom (.mul (.n 22) (.n 18) (.n 19)),
    .call "child_claim_list_digest" [.n 3, .n 4, .n 17, .n 5, .n 18] [.n 23, .n 24],
    .atom (.mul (.n 25) (.n 17) (.n 18)),
    .call "child_claim_list_digest" [.n 6, .n 7, .n 25, .n 8, .n 19] [.n 26, .n 27],
    .atom (.mul (.n 28) (.n 0) (.n 0)),
    .atom (.mul (.n 29) (.n 28) (.n 0)),
    .atom (.mul (.n 30) (.n 29) (.n 29)),
    .atom (.mul (.n 31) (.n 30) (.n 30)),
    .atom (.mul (.n 32) (.n 31) (.n 31)),
    .atom (.mul (.n 33) (.n 9) (.n 32)),
    .atom (.hint (.witness "child_defer" (.heap (.n 33) 0 24))),
    .atom (.mul (.n 34) (.n 0) (.n 0)),
    .atom (.mul (.n 35) (.n 10) (.n 34)),
    .atom (.hint (.witness "child_da" (.heap (.n 35) 0 2))),
    .atom (.load (.n 36) (.n 35) 0),
    .atom (.load (.n 37) (.n 35) 1),
    .call "statement_digest" [.n 11, .n 12, .n 23, .n 24, .n 26, .n 27, .n 36, .n 37, .n 33]
      [.n 38, .n 39],
    .atom (.mul (.n 40) (.n 0) (.n 0)),
    .atom (.mul (.n 41) (.n 13) (.n 40)),
    .atom (.load (.n 38) (.n 41) 0),
    .atom (.mul (.n 42) (.n 13) (.n 40)),
    .atom (.load (.n 39) (.n 42) 1),
    .atom (.mul (.n 43) (.n 0) (.n 0)),
    .atom (.mul (.n 44) (.n 43) (.n 0)),
    .atom (.mul (.n 45) (.n 44) (.n 44)),
    .atom (.mul (.n 46) (.n 45) (.n 45)),
    .atom (.mul (.n 47) (.n 46) (.n 46)),
    .atom (.mul (.n 48) (.n 15) (.n 47)),
    .call "verify_sub" [.n 38, .n 39, .n 11, .n 12, .n 14, .n 48] [],
    .atom (.mul (.n 49) (.n 17) (.n 22)),
    .atom (.mul (.n 50) (.n 2) (.n 0)),
    .atom (.load (.n 49) (.n 50) 1),
    .atom (.const (.n 51) (word 2 0)),
    .atom (.mul (.n 52) (.n 0) (.n 51)),
    .atom (.add (.n 53) (.n 52) (.n 1)),
    .atom (.const (.n 54) (word 2 0)),
    .atom (.mul (.n 55) (.n 0) (.n 54))]

/-- `main_loop4`'s tail call. -/
def l5Tail : Stmt :=
  .callIf (.n 53) name% «main_loop4» [.n 55, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6, .n 7, .n 8, .n 9,
      .n 10, .n
    11, .n 12, .n 13, .n 14, .n 15]

set_option maxRecDepth 100000 in
theorem l5_body : Fn.body (coreProgram.getD idx% «main_loop4» default) = l5Pre ++ [l5Tail,
    .ret []] :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem l5_params : (coreProgram.getD idx% «main_loop4» default).params = (List.range 16).map V.n
    := by
  decide +kernel

/-- `main_loop4`'s stores. -/
def l5S : List Atom :=
  [.load (.n 38) (.n 41) 0, .load (.n 39) (.n 42) 1, .load (.n 49) (.n 50) 1]

/-- The block's atoms but the stores. -/
def l5A' : List Atom := (atomsIn l5Pre).filter fun a => decide (a ∉ l5S)

/-- The calls of the block. -/
def l5Calls : List Stmt :=
  [.call "child_claim_list_digest" [.n 3, .n 4, .n 17, .n 5, .n 18] [.n 23, .n 24],
    .call "child_claim_list_digest" [.n 6, .n 7, .n 25, .n 8, .n 19] [.n 26, .n 27],
    .call "statement_digest" [.n 11, .n 12, .n 23, .n 24, .n 26, .n 27, .n 36, .n 37, .n 33]
      [.n 38, .n 39]]

/-- **`main_loop4`'s block, evaluated.** -/
def l5COk : Bool :=
  (chk 16 (l5Pre ++ [l5Tail, .ret []])).isSome &&
  decide (storesOf 16 (l5Pre ++ [l5Tail, .ret []]) = l5S) &&
  (atomsIn l5Pre).all (fun a => !needsSide a || decide (a ∈ l5S) ||
    decide (a = .load (.n 17) (.n 16) 0) || decide (a = .load (.n 36) (.n 35) 0) ||
    decide (a = .load (.n 37) (.n 35) 1) || decide (a = .touch (.n 20) (.n 18)) ||
    decide (a = .touch (.n 21) (.n 19))) &&
  l5Calls.all (fun c => l5Pre.any (stmtEqb · c))

set_option maxRecDepth 100000 in
theorem l5c_ok : l5COk = true := by decide +kernel

end
end LeanVM.Guest.B1.Main
