/-
  LeanVM.Guest.B1.Main.MainNoWit

  `main`'s callees with no witness hint in their subtree, `exponent_tables` and `statement_digest`, by the kernel.
-/

module

public import LeanVM.Guest.B1.Common.NoWitMute
public import LeanVM.Guest.CoreRef

/-!
# `main`'s callees without witness hints

`exponent_tables_noWit`, `statement_digest_noWit`: `NoWitG` of each, so each valid tree of them pops `[]`.
-/

namespace LeanVM.Guest.B1.Main

open LeanVM.Guest.Memory

@[expose] public section

theorem exponent_tables_noWit : NoWitG "exponent_tables" :=
  noWitG_of_callee (j := idx% «main») (by decide +kernel)

theorem statement_digest_noWit : NoWitG "statement_digest" :=
  noWitG_of_callee (j := idx% «main») (by decide +kernel)

end
end LeanVM.Guest.B1.Main
