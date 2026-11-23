/-
  LeanVM.Guest.B1.Tables.VtC.Calls

  `verify_tables`' calls: their kinds, their count, and the bounds the budget charges them.
-/

module

public import LeanVM.Guest.B1.Tables.Vt.Base
public import LeanVM.Guest.Data.NameStrings
import LeanVM.Guest.ValRef
import LeanVM.Guest.Data.ValNames.«verify_tables»

/-!
# `verify_tables`' calls

`vtCallKindB`: a call is neither loop, the shared tables' calls are of six arguments and no
return, a dispatch's arms are neither, and the one conditional call is the rounds loop's
(`vt_callKinds`); there are `119` calls (`vt_ncalls`). `vtBs`: each call's
bound, by its kind (`vtCallBnd`), what `vtWB` sums. Kept apart from the completeness proofs so
that the budget reads them alone.
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value

@[expose] public section

/-- A call, conditional call or dispatch. -/
def callB : Stmt → Bool
  | .call .. | .callIf .. | .dispatch .. => true
  | _ => false

/-- What a call statement's callee is bounded by: the rounds loop's run by `K10n`. -/
def vtCallBnd (Kf : String → ℕ) (Ksh K10n : ℕ) : Stmt → ℕ
  | .call f _ _ => if f = "shared_selector_tables" then Ksh else Kf f
  | .dispatch _ fs' _ _ => (fs'.map Kf).foldr max 0
  | .callIf _ _ _ => K10n
  | _ => 0

theorem vtCallBnd_callIf (Kf : String → ℕ) (Ksh K10n : ℕ) (c : V) (f : String) (a : List V) :
    vtCallBnd Kf Ksh K10n (.callIf c f a) = K10n := rfl

/-- `verify_tables_loop0`'s run at `n` rounds: `n · K10` words and, when it runs, its one phantom
frame. -/
def vtRunB (fs : String → ℕ) (K10 n : ℕ) : ℕ := n * K10 + if n = 0 then 0 else fs
    name% «verify_tables_loop0»

/-- The calls' bounds, in order. -/
noncomputable def vtBs (Kf : String → ℕ) (Ksh K10n : ℕ) : List ℕ :=
  (vtPre.filter callB).map (vtCallBnd Kf Ksh K10n)

/-- The calls' kinds: a call is neither loop, the shared tables' are of six arguments and no
return, a dispatch's arms neither, the one conditional call the rounds loop's. -/
def vtCallKindB : Stmt → Bool
  | .call f a r => f != name% «verify_tables_loop0» &&
      f != name% «shared_selector_tables_loop0» &&
      (f != "shared_selector_tables" || (a.length == 6 && r.isEmpty))
  | .dispatch _ fs' _ _ => fs'.all fun g ↦ g != name% «verify_tables_loop0» &&
      g != name% «shared_selector_tables_loop0» && g != "shared_selector_tables"
  | .callIf c f a => f == name% «verify_tables_loop0» && c == .n (val% «verify_tables» "s72#1") &&
      a == [.n (val% «verify_tables» "s72#2"), .n (val% «verify_tables» "g_zc_n"), .n (val% «verify_tables» "zc_rounds"), .n (val% «verify_tables» "tabs"), .n (val% «verify_tables» "zc_rk"), .n (val% «verify_tables» "zc_cprod")]
  | _ => true

theorem vt_callKinds : vtPre.all vtCallKindB = true := by decide +kernel

theorem vt_ncalls : (vtPre.filter callB).length = 119 := by decide +kernel

end
end LeanVM.Guest.B1.Tables
