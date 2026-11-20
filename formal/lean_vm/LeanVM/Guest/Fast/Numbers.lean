module

/-!
# Template positions, as numbers

The tables of `Fast/*Tables.lean` are read by `offAt` (row `r`, entry `k`). The checks import this
and the templates alone (`Fast/Firewall.lean`).
-/

namespace LeanVM.Guest.Fast

@[expose] public section

/-- Entry `k` of row `r`. -/
def offAt (tab : List (List Nat)) (r k : Nat) : Nat := (tab.getD r []).getD k 0

end
end LeanVM.Guest.Fast
