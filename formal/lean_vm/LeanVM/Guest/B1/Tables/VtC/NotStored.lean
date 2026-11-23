/-
  LeanVM.Guest.B1.Tables.VtC.NotStored

  Whether a read is one of `verify_tables`' stores, decided fast: by its numbers (`Fwd.notStoredB`).
-/

module

public import LeanVM.Guest.B1.Tables.VtC.Stores
public import LeanVM.Guest.B1.Fwd.NotStored

/-!
# A read that is not a store

`a ∉ vtSL` by the read's numbers, its pointer first (`Fwd.notStoredB`, `vtStorePtrs`): every
`decide` of it uses `instDecidableNotMemVtSL`.
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Guest.Core LeanVM.Guest.B1.Fwd

@[expose] public section

/-- The pointers of `verify_tables`' stores (`vtSL_ptrs`). -/
def vtStorePtrs : List ℕ :=
  [15, 19, 34, 35, 118, 122, 131, 141, 151, 161, 171, 181, 191, 201, 211, 221, 231, 241, 251, 261,
    271, 281, 415, 419, 428, 438, 448, 458, 468, 478, 488, 498, 508, 518, 767, 822, 2316, 2317]

theorem vtSL_ptrs : vtSL.all (ptrInB vtStorePtrs) = true := by decide +kernel

instance (priority := high) instDecidableNotMemVtSL (a : Atom) : Decidable (a ∉ vtSL) :=
  decidable_of_iff _ (notStoredB_iff vtSL_ptrs a)

end
end LeanVM.Guest.B1.Tables
