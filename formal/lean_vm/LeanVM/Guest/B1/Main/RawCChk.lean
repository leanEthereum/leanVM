/-
  LeanVM.Guest.B1.Main.RawCChk

  `main`'s raw-signature loop `main_loop3` as a statement list (by kernel evaluation), and the pure
  set it calls into, for its placed completeness (`main_loop2`'s, its check inline, is `RawAt`'s).
-/

module

public import LeanVM.Guest.B1.Main.Loops
public import LeanVM.Guest.Memory.LiftPure
public import LeanVM.Guest.B1.Sig.Interface
public import LeanVM.Guest.Data.NameStrings

/-!
# `main_loop3`'s body

`l4Pre`: `main_loop3`'s statements before its `ret []` (`l4_body`), its parameters `.n 0 …`
(`l4_params`); `l4_find`; `raw4_pure`: the loop with its signature verifier and `sp_wots`, which it
calls, places nothing (kernel evaluation). `pureOk`, `pureIn_of_ok`: a pure set by evaluation.
-/

namespace LeanVM.Guest.B1.Main

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Guest.B1.Digest

@[expose] public section

/-- `main_loop3`'s statements before its `ret []`. -/
def l4Pre : List Stmt :=
  [.atom (.hint (.witness "sp_raw_index" (.stack [.n 7]))),
    .atom (.const (.n 8) (word 9223372036854775821 0)), .atom (.mul (.n 9) (.n 2) (.n 8)),
    .atom (.rangeCheck (.n 7) (.n 10) (.n 11) (.n 12) (.n 9)), .atom (.mul (.n 13) (.n 4) (.n 0)),
    .atom (.mul (.n 14) (.n 3) (.n 7)), .atom (.load (.n 13) (.n 14) 0),
    .atom (.mul (.n 15) (.n 7) (.n 7)), .atom (.mul (.n 16) (.n 15) (.n 15)),
    .atom (.mul (.n 17) (.n 5) (.n 16)),
    .call "verify_sig_lean_sphincs" [.n 17, .n 6] [], .atom (.const (.n 18) (word 2 0)),
    .atom (.mul (.n 19) (.n 0) (.n 18)), .atom (.add (.n 20) (.n 19) (.n 1)),
    .atom (.const (.n 21) (word 2 0)), .atom (.mul (.n 22) (.n 0) (.n 21)),
    .callIf (.n 20) name% «main_loop3» [.n 22, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6]]

set_option maxRecDepth 100000 in
theorem l4_body : Fn.body (coreProgram.getD idx% «main_loop3» default) = l4Pre ++ [.ret []] :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem l4_params : (coreProgram.getD idx% «main_loop3» default).params =
    [.n 0, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6] := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem l4_idx' : coreProgram.indexOf? name% «main_loop3» = some idx% «main_loop3» :=
  coreProgram_indexOf?_at (j := idx% «main_loop3») rfl

theorem l4_find : coreProgram.find? name% «main_loop3» = some (coreProgram.getD idx% «main_loop3» default) :=
  find_of_idx l4_idx'

/-- Every member's body places nothing and calls members only. -/
noncomputable def pureOk (S : List String) : Bool :=
  S.all fun g => match coreProgram.find? g with
    | some fn => Stmt.pureList S fn.body
    | none => true

theorem pureIn_of_ok {S : List String} (h : pureOk S = true) : coreProgram.PureIn S := by
  intro g hg fn hf
  have h := List.all_eq_true.mp h g hg
  rw [hf] at h
  exact h

set_option maxRecDepth 100000 in
theorem raw4_pure : coreProgram.PureIn [name% «main_loop3», "verify_sig_lean_sphincs", "sp_wots"] :=
  pureIn_of_ok (by decide +kernel)

end
end LeanVM.Guest.B1.Main
