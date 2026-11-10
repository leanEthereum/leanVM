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
  [15, 19, 33, 34, 117, 121, 130, 140, 150, 160, 170, 180, 190, 200, 210, 220, 230, 240, 250, 260,
    270, 280, 414, 418, 427, 437, 447, 457, 467, 477, 487, 497, 507, 517, 664, 777, 2627, 2630]

theorem vtSL_ptrs : vtSL.all (ptrInB vtStorePtrs) = true := by decide +kernel

instance (priority := high) instDecidableNotMemVtSL (a : Atom) : Decidable (a ∉ vtSL) :=
  decidable_of_iff _ (notStoredB_iff vtSL_ptrs a)

end
end LeanVM.Guest.B1.Tables
