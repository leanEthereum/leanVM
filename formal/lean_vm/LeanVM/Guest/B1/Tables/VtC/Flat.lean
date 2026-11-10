/-
  LeanVM.Guest.B1.Tables.VtC.Flat

  `verify_tables`' body as the forward evaluator walks it: each top-level `ite`'s two branches in
  order, and each `assertNe` whose inverse a hint defined as the product it checks.
-/

module

public import LeanVM.Guest.B1.Tables.Vt.Base
public import LeanVM.Guest.B1.Fwd.Canon
public import LeanVM.Guest.B1.Fwd.FlatIte

/-!
# The evaluation list

`flatIte`: a block with each top-level `ite`'s branches in order (both are numbered in order, so
the evaluator defines each branch's values; only the taken branch must hold). `fixNe`: an
`assertNe x i p` after a hint `i = 1/x` defines `p` as `x·i`, the product it checks (the evaluator
defines `i` and `p` together otherwise). `vtEvL`: `verify_tables`' body so; `vt_chk`: the checker
accepts it from its `20` parameters.
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Guest.B1.Fwd

@[expose] public section

/-- **`verify_tables`' evaluation list.** -/
noncomputable def vtEvL : List Stmt := (flatIte vtPre).map fixNe

theorem vt_chk : chk 20 vtEvL = some 5990 := by decide +kernel

end
end LeanVM.Guest.B1.Tables
