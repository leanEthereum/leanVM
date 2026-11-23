/-
  LeanVM.Guest.B1.Main.KidCChk

  `main_loop4`'s block (a child), evaluated (by kernel evaluation), for its placed completeness.
-/

module

public import LeanVM.Guest.B1.Main.Loops
public import LeanVM.Guest.B1.Fwd.Canon
public import LeanVM.Guest.Memory.Uniform
public import LeanVM.Guest.Data.NameStrings
import LeanVM.Guest.ValRef
import LeanVM.Guest.Data.ValNames.«main_loop4»

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
    .atom (.mul (.n (val% «main_loop4» "base~0")) (.n (val% «main_loop4» "written")) (.n (val% «main_loop4» "xc"))),
    .atom (.load (.n (val% «main_loop4» "base")) (.n (val% «main_loop4» "base~0")) 0),
    .atom (.hint (.witness "child_meta" (.stack [.n (val% «main_loop4» "child_meta[0]"), .n (val% «main_loop4» "child_meta[1]")]))),
    .atom (.touch (.n (val% «main_loop4» "s5#0")) (.n (val% «main_loop4» "child_meta[0]"))),
    .atom (.touch (.n (val% «main_loop4» "s6#0")) (.n (val% «main_loop4» "child_meta[1]"))),
    .atom (.mul (.n (val% «main_loop4» "nsub_g")) (.n (val% «main_loop4» "child_meta[0]")) (.n (val% «main_loop4» "child_meta[1]"))),
    .call "child_claim_list_digest" [.n (val% «main_loop4» "lx_table"), .n (val% «main_loop4» "cover"), .n (val% «main_loop4» "base"), .n (val% «main_loop4» "lx_slots_g"), .n (val% «main_loop4» "child_meta[0]")] [.n (val% «main_loop4» "cx_0"), .n (val% «main_loop4» "cx_1")],
    .atom (.mul (.n (val% «main_loop4» "cs_0~2")) (.n (val% «main_loop4» "base")) (.n (val% «main_loop4» "child_meta[0]"))),
    .call "child_claim_list_digest" [.n (val% «main_loop4» "lean_sphincs_table"), .n (val% «main_loop4» "sp_cover"), .n (val% «main_loop4» "cs_0~2"), .n (val% «main_loop4» "lean_sphincs_slots_g"), .n (val% «main_loop4» "child_meta[1]")] [.n (val% «main_loop4» "cs_0"), .n (val% «main_loop4» "cs_1")],
    .atom (.mul (.n (val% «main_loop4» "carried~0")) (.n (val% «main_loop4» "xc")) (.n (val% «main_loop4» "xc"))),
    .atom (.mul (.n (val% «main_loop4» "carried~1")) (.n (val% «main_loop4» "carried~0")) (.n (val% «main_loop4» "xc"))),
    .atom (.mul (.n (val% «main_loop4» "carried~2")) (.n (val% «main_loop4» "carried~1")) (.n (val% «main_loop4» "carried~1"))),
    .atom (.mul (.n (val% «main_loop4» "carried~3")) (.n (val% «main_loop4» "carried~2")) (.n (val% «main_loop4» "carried~2"))),
    .atom (.mul (.n (val% «main_loop4» "carried~4")) (.n (val% «main_loop4» "carried~3")) (.n (val% «main_loop4» "carried~3"))),
    .atom (.mul (.n (val% «main_loop4» "carried")) (.n (val% «main_loop4» "child_carried")) (.n (val% «main_loop4» "carried~4"))),
    .atom (.hint (.witness "child_defer" (.heap (.n (val% «main_loop4» "carried")) 0 24))),
    .atom (.mul (.n (val% «main_loop4» "child_da~0")) (.n (val% «main_loop4» "xc")) (.n (val% «main_loop4» "xc"))),
    .atom (.mul (.n (val% «main_loop4» "child_da")) (.n (val% «main_loop4» "da_digests")) (.n (val% «main_loop4» "child_da~0"))),
    .atom (.hint (.witness "child_da" (.heap (.n (val% «main_loop4» "child_da")) 0 2))),
    .atom (.load (.n (val% «main_loop4» "pi_0~2")) (.n (val% «main_loop4» "child_da")) 0),
    .atom (.load (.n (val% «main_loop4» "pi_0~3")) (.n (val% «main_loop4» "child_da")) 1),
    .call "statement_digest" [.n (val% «main_loop4» "seed_0"), .n (val% «main_loop4» "seed_1"), .n (val% «main_loop4» "cx_0"), .n (val% «main_loop4» "cx_1"), .n (val% «main_loop4» "cs_0"), .n (val% «main_loop4» "cs_1"), .n (val% «main_loop4» "pi_0~2"), .n (val% «main_loop4» "pi_0~3"), .n (val% «main_loop4» "carried")]
      [.n (val% «main_loop4» "pi_0"), .n (val% «main_loop4» "pi_1")],
    .atom (.mul (.n (val% «main_loop4» "pi")) (.n (val% «main_loop4» "xc")) (.n (val% «main_loop4» "xc"))),
    .atom (.mul (.n (val% «main_loop4» "s16#0")) (.n (val% «main_loop4» "child_pi")) (.n (val% «main_loop4» "pi"))),
    .atom (.load (.n (val% «main_loop4» "pi_0")) (.n (val% «main_loop4» "s16#0")) 0),
    .atom (.mul (.n (val% «main_loop4» "s17#0")) (.n (val% «main_loop4» "child_pi")) (.n (val% «main_loop4» "pi"))),
    .atom (.load (.n (val% «main_loop4» "pi_1")) (.n (val% «main_loop4» "s17#0")) 1),
    .atom (.mul (.n (val% «main_loop4» "s18#0")) (.n (val% «main_loop4» "xc")) (.n (val% «main_loop4» "xc"))),
    .atom (.mul (.n (val% «main_loop4» "s18#1")) (.n (val% «main_loop4» "s18#0")) (.n (val% «main_loop4» "xc"))),
    .atom (.mul (.n (val% «main_loop4» "s18#2")) (.n (val% «main_loop4» "s18#1")) (.n (val% «main_loop4» "s18#1"))),
    .atom (.mul (.n (val% «main_loop4» "s18#3")) (.n (val% «main_loop4» "s18#2")) (.n (val% «main_loop4» "s18#2"))),
    .atom (.mul (.n (val% «main_loop4» "s18#4")) (.n (val% «main_loop4» "s18#3")) (.n (val% «main_loop4» "s18#3"))),
    .atom (.mul (.n (val% «main_loop4» "s18#5")) (.n (val% «main_loop4» "child_fresh")) (.n (val% «main_loop4» "s18#4"))),
    .call "verify_sub" [.n (val% «main_loop4» "pi_0"), .n (val% «main_loop4» "pi_1"), .n (val% «main_loop4» "seed_0"), .n (val% «main_loop4» "seed_1"), .n (val% «main_loop4» "g_squares"), .n (val% «main_loop4» "s18#5")] [],
    .atom (.mul (.n (val% «main_loop4» "s19#0")) (.n (val% «main_loop4» "base")) (.n (val% «main_loop4» "nsub_g"))),
    .atom (.mul (.n (val% «main_loop4» "s19#1")) (.n (val% «main_loop4» "written")) (.n (val% «main_loop4» "xc"))),
    .atom (.load (.n (val% «main_loop4» "s19#0")) (.n (val% «main_loop4» "s19#1")) 1),
    .atom (.const (.n (val% «main_loop4» "s21#0")) (word 2 0)),
    .atom (.mul (.n (val% «main_loop4» "s21#1")) (.n (val% «main_loop4» "xc")) (.n (val% «main_loop4» "s21#0"))),
    .atom (.add (.n (val% «main_loop4» "s21#2")) (.n (val% «main_loop4» "s21#1")) (.n (val% «main_loop4» "bound"))),
    .atom (.const (.n (val% «main_loop4» "s21#3")) (word 2 0)),
    .atom (.mul (.n (val% «main_loop4» "s21#4")) (.n (val% «main_loop4» "xc")) (.n (val% «main_loop4» "s21#3")))]

/-- `main_loop4`'s tail call. -/
def l5Tail : Stmt :=
  .callIf (.n (val% «main_loop4» "s21#2")) name% «main_loop4» [.n (val% «main_loop4» "s21#4"), .n (val% «main_loop4» "bound"), .n (val% «main_loop4» "written"), .n (val% «main_loop4» "lx_table"), .n (val% «main_loop4» "cover"), .n (val% «main_loop4» "lx_slots_g"), .n (val% «main_loop4» "lean_sphincs_table"), .n (val% «main_loop4» "sp_cover"), .n (val% «main_loop4» "lean_sphincs_slots_g"), .n (val% «main_loop4» "child_carried"),
      .n (val% «main_loop4» "da_digests"), .n
    (val% «main_loop4» "seed_0"), .n (val% «main_loop4» "seed_1"), .n (val% «main_loop4» "child_pi"), .n (val% «main_loop4» "g_squares"), .n (val% «main_loop4» "child_fresh")]

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
  [.load (.n (val% «main_loop4» "pi_0")) (.n (val% «main_loop4» "s16#0")) 0, .load (.n (val% «main_loop4» "pi_1")) (.n (val% «main_loop4» "s17#0")) 1, .load (.n (val% «main_loop4» "s19#0")) (.n (val% «main_loop4» "s19#1")) 1]

/-- The block's atoms but the stores. -/
def l5A' : List Atom := (atomsIn l5Pre).filter fun a => decide (a ∉ l5S)

/-- The calls of the block. -/
def l5Calls : List Stmt :=
  [.call "child_claim_list_digest" [.n (val% «main_loop4» "lx_table"), .n (val% «main_loop4» "cover"), .n (val% «main_loop4» "base"), .n (val% «main_loop4» "lx_slots_g"), .n (val% «main_loop4» "child_meta[0]")] [.n (val% «main_loop4» "cx_0"), .n (val% «main_loop4» "cx_1")],
    .call "child_claim_list_digest" [.n (val% «main_loop4» "lean_sphincs_table"), .n (val% «main_loop4» "sp_cover"), .n (val% «main_loop4» "cs_0~2"), .n (val% «main_loop4» "lean_sphincs_slots_g"), .n (val% «main_loop4» "child_meta[1]")] [.n (val% «main_loop4» "cs_0"), .n (val% «main_loop4» "cs_1")],
    .call "statement_digest" [.n (val% «main_loop4» "seed_0"), .n (val% «main_loop4» "seed_1"), .n (val% «main_loop4» "cx_0"), .n (val% «main_loop4» "cx_1"), .n (val% «main_loop4» "cs_0"), .n (val% «main_loop4» "cs_1"), .n (val% «main_loop4» "pi_0~2"), .n (val% «main_loop4» "pi_0~3"), .n (val% «main_loop4» "carried")]
      [.n (val% «main_loop4» "pi_0"), .n (val% «main_loop4» "pi_1")]]

/-- **`main_loop4`'s block, evaluated.** -/
def l5COk : Bool :=
  (chk 16 (l5Pre ++ [l5Tail, .ret []])).isSome &&
  decide (storesOf 16 (l5Pre ++ [l5Tail, .ret []]) = l5S) &&
  (atomsIn l5Pre).all (fun a => !needsSide a || decide (a ∈ l5S) ||
    decide (a = .load (.n (val% «main_loop4» "base")) (.n (val% «main_loop4» "base~0")) 0) || decide (a = .load (.n (val% «main_loop4» "pi_0~2")) (.n (val% «main_loop4» "child_da")) 0) ||
    decide (a = .load (.n (val% «main_loop4» "pi_0~3")) (.n (val% «main_loop4» "child_da")) 1) || decide (a = .touch (.n (val% «main_loop4» "s5#0")) (.n (val% «main_loop4» "child_meta[0]"))) ||
    decide (a = .touch (.n (val% «main_loop4» "s6#0")) (.n (val% «main_loop4» "child_meta[1]")))) &&
  l5Calls.all (fun c => l5Pre.any (stmtEqb · c))

set_option maxRecDepth 100000 in
theorem l5c_ok : l5COk = true := by decide +kernel

end
end LeanVM.Guest.B1.Main
