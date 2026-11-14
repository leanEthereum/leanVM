/-
  LeanVM.Guest.Exact.FreeMain

  `main`'s callees without computed hints in their subtrees, and `main`'s own body, by the kernel.
-/

module

public import LeanVM.Guest.Exact.Free
public import LeanVM.Guest.CoreRef
public import LeanVM.Guest.CoreNames

/-!
# `main`'s free callees

`exponent_tables`, `statement_digest`, `claim_list_digest`, `da_verify`, `main_loop0` and `main_loop1` pass
`exactFree`, so every valid tree of one is exact on every reader; `main`'s own body has no computed hint
(`main_pinned`).
-/

namespace LeanVM.Guest.Memory

open LeanVM.Guest.Core

@[expose] public section

theorem exponent_tables_exactFree : ExactFreeG "exponent_tables" :=
  exactFreeG_of (j := idx% «exponent_tables») (by decide +kernel)

theorem statement_digest_exactFree : ExactFreeG "statement_digest" :=
  exactFreeG_of (j := idx% «statement_digest») (by decide +kernel)

theorem claim_list_digest_exactFree : ExactFreeG "claim_list_digest" :=
  exactFreeG_of (j := idx% «claim_list_digest») (by decide +kernel)

theorem da_verify_exactFree : ExactFreeG "da_verify" :=
  exactFreeG_of (j := idx% «da_verify») (by decide +kernel)

theorem main_loop0_exactFree : ExactFreeG name% «main_loop0» :=
  exactFreeG_of (j := idx% «main_loop0») (by decide +kernel)

theorem main_loop1_exactFree : ExactFreeG name% «main_loop1» :=
  exactFreeG_of (j := idx% «main_loop1») (by decide +kernel)

/-- `main`'s own computed hints are pinned by the next atom: it has none. -/
theorem main_pinned : Stmt.blockNextOk isComputed pinsInverse (fn% «main»).body = true := by
  decide +kernel

end
end LeanVM.Guest.Memory
