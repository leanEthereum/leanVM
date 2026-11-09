/-
  LeanVM.Guest.B1.Tables.VtC.Glue

  `verify_tables`' relation from its statements one by one: each atom, call and dispatch, and
  each `ite` by its taken branch.
-/

module

public import LeanVM.Guest.B1.Tables.VtC.Flat

/-!
# From statements to the relation

`VSH C rd σ s`: the statement holds, its continuation aside; an `ite` by its taken branch, every
statement of which is straight (`iteOk`, checked of `vtPre` by the kernel). `vt_rel_of`: when every
statement of `vtPre` does, the parameters are the arguments and `vtRets` the returns, the relation
holds.
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Guest.B1.Fwd

@[expose] public section

theorem vt_iteOk : vtPre.all iteOk = true := by decide +kernel

end
end LeanVM.Guest.B1.Tables
