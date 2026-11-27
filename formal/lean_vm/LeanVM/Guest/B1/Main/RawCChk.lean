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
import LeanVM.Guest.ValRef
import LeanVM.Guest.Data.ValNames.«main_loop3»
import LeanVM.Guest.KernelLit
import LeanVM.Guest.StmtsAppend

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
  [.atom (.hint (.witness "sp_raw_index" (.stack [.n (val% «main_loop3» "off_hint")]))),
    .atom (.const (.n (val% «main_loop3» "s1#0")) (word 9223372036854775821 0)), .atom (.mul (.n (val% «main_loop3» "s1#1")) (.n (val% «main_loop3» "lean_sphincs_slots_g")) (.n (val% «main_loop3» "s1#0"))),
    .atom (.rangeCheck (.n (val% «main_loop3» "off_hint")) (.n (val% «main_loop3» "s1#2")) (.n (val% «main_loop3» "s1#3")) (.n (val% «main_loop3» "s1#4")) (.n (val% «main_loop3» "s1#1"))), .atom (.mul (.n (val% «main_loop3» "s2#0")) (.n (val% «main_loop3» "n_raw_x_g")) (.n (val% «main_loop3» "xj"))),
    .atom (.mul (.n (val% «main_loop3» "s2#1")) (.n (val% «main_loop3» "sp_cover")) (.n (val% «main_loop3» "off_hint"))), .atom (.load (.n (val% «main_loop3» "s2#0")) (.n (val% «main_loop3» "s2#1")) 0),
    .atom (.mul (.n (val% «main_loop3» "s3#0")) (.n (val% «main_loop3» "off_hint")) (.n (val% «main_loop3» "off_hint"))), .atom (.mul (.n (val% «main_loop3» "s3#1")) (.n (val% «main_loop3» "s3#0")) (.n (val% «main_loop3» "s3#0"))),
    .atom (.mul (.n (val% «main_loop3» "s3#2")) (.n (val% «main_loop3» "lean_sphincs_table")) (.n (val% «main_loop3» "s3#1"))),
    .call "verify_sig_lean_sphincs" [.n (val% «main_loop3» "s3#2"), .n (val% «main_loop3» "byte_bits")] [], .atom (.const (.n (val% «main_loop3» "s5#0")) (word 2 0)),
    .atom (.mul (.n (val% «main_loop3» "s5#1")) (.n (val% «main_loop3» "xj")) (.n (val% «main_loop3» "s5#0"))), .atom (.add (.n (val% «main_loop3» "s5#2")) (.n (val% «main_loop3» "s5#1")) (.n (val% «main_loop3» "bound"))),
    .atom (.const (.n (val% «main_loop3» "s5#3")) (word 2 0)), .atom (.mul (.n (val% «main_loop3» "s5#4")) (.n (val% «main_loop3» "xj")) (.n (val% «main_loop3» "s5#3"))),
    .callIf (.n (val% «main_loop3» "s5#2")) name% «main_loop3» [.n (val% «main_loop3» "s5#4"), .n (val% «main_loop3» "bound"), .n (val% «main_loop3» "lean_sphincs_slots_g"), .n (val% «main_loop3» "sp_cover"), .n (val% «main_loop3» "n_raw_x_g"), .n (val% «main_loop3» "lean_sphincs_table"), .n (val% «main_loop3» "byte_bits")]]

kernel_rfl l4_body : Fn.body (coreProgram.getD idx% «main_loop3» default) = l4Pre ⧺ [.ret []]

set_option maxRecDepth 100000 in
theorem l4_params : (coreProgram.getD idx% «main_loop3» default).params =
    [.n (val% «main_loop3» "xj"), .n (val% «main_loop3» "bound"), .n (val% «main_loop3» "lean_sphincs_slots_g"), .n (val% «main_loop3» "sp_cover"), .n (val% «main_loop3» "n_raw_x_g"), .n (val% «main_loop3» "lean_sphincs_table"), .n (val% «main_loop3» "byte_bits")] := by
  decide +kernel

set_option maxRecDepth 100000 in

theorem l4_find : coreProgram.find? name% «main_loop3» = some (coreProgram.getD idx% «main_loop3»
    default) :=
  find_of_idx l4_idx

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
