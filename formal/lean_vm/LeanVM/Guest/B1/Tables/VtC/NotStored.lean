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
  [15, 36, 37, 120, 124, 133, 143, 153, 163, 173, 183, 193, 203, 213, 223, 233, 243, 253, 263, 273,
    283, 417, 421, 430, 440, 450, 460, 470, 480, 490, 500, 510, 520, 668, 781, 2605, 2608]

theorem vtSL_ptrs : vtSL.all (ptrInB vtStorePtrs) = true := by decide +kernel

instance (priority := high) instDecidableNotMemVtSL (a : Atom) : Decidable (a ∉ vtSL) :=
  decidable_of_iff _ (notStoredB_iff vtSL_ptrs a)

end
end LeanVM.Guest.B1.Tables
