module

public import LeanVM.Guest.B1.Sig.WotsT

/-!
# Template positions, as numbers

The definitions the literal tables of `Fast/*Tables.lean` are checked against, arithmetic in the
template's parameters, with no statement built: a codeword's arms, selectors and chain starts
(`walkBaseN`, proved equal to the generators in `Fast/Wots.lean`). The checks import these and the templates alone (`Fast/Firewall.lean`).
-/

namespace LeanVM.Guest.Fast

open LeanVM.Guest.B1.Sig

@[expose] public section

/-! ## A codeword -/

/-- The base of walk `r + j` of arm `k` from walk `r` at `b` (`walkBase`). -/
def walkBaseN (stride k : ℕ) : ℕ → ℕ → ℕ → ℕ
  | _, 0, b => b
  | r, j + 1, b => walkBaseN stride k (r + 1) j (b + walkSize stride (k / 4 ^ r % 4))

/-! ## Tables -/

/-- Entry `k` of row `r`. -/
def offAt (tab : List (List ℕ)) (r k : ℕ) : ℕ := (tab.getD r []).getD k 0

end
end LeanVM.Guest.Fast
