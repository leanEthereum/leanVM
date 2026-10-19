/-
  LeanVM.Guest.Data.CplArms

  The per-arm instruction counts of the `match`es whose arms the completeness walk counts
  separately.
-/

module

public import LeanVM.Guest.Code

/-!
Function `j`'s entry is a list of `(x, costs)`: the `match` on the renumbered value `x` has its
arms counted separately, arm `k` at most `costs[k]` instructions of each opcode (in `Opcode`'s
order) from its segment to the join, the callees' apart. Every other `match` counts its arms by
their maximum. Checked by `B2C.cplWin`.
-/

namespace LeanVM.Guest.Data

@[expose] public section

/-- The per-arm counts, by function. -/
def cplArms : List (List (ℕ × List (List ℕ))) := []

end
end LeanVM.Guest.Data
