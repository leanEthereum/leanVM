module

public import LeanVM.Guest.B1.Sig.WotsT

/-!
# Template positions, as numbers

The definitions the literal tables of `Fast/*Tables.lean` are checked against, arithmetic in the
template's parameters, with no statement built: a codeword's arms, selectors and chain starts
(`walkBaseN` … `startN`, `offTab`, proved equal to the generators in `Fast/Wots.lean`). The checks import these and the templates alone (`Fast/Firewall.lean`).
-/

namespace LeanVM.Guest.Fast

open LeanVM.Guest.B1.Sig

@[expose] public section

/-! ## A codeword -/

/-- The base of walk `r + j` of arm `k` from walk `r` at `b` (`walkBase`). -/
def walkBaseN (stride k : ℕ) : ℕ → ℕ → ℕ → ℕ
  | _, 0, b => b
  | r, j + 1, b => walkBaseN stride k (r + 1) j (b + walkSize stride (k / 4 ^ r % 4))

/-- The base after arm `k` from `a`, of a step of size `sz` (`armNext`). -/
def armNextN (sz n : ℕ) (fold : Bool) (k a : ℕ) : ℕ :=
  if k = 0 then walkBaseN (sz + 1) k 0 n (if fold then a + 1 else a) + 2
  else walkBaseN sz k 0 n (if fold then a + 1 else a) + 1

/-- The base of arm `k + j` from arm `k` at `b` (`armBase`). -/
def armBaseN (sz n : ℕ) (fold : Bool) : ℕ → ℕ → ℕ → ℕ
  | _, 0, b => b
  | k, j + 1, b => armBaseN sz n fold (k + 1) j (armNextN sz n fold k b)

/-- The selector cell of group `p` of a codeword from `b` (`(cwState W b p).2.2`). -/
def selN (sz b : ℕ) : ℕ → ℕ
  | 0 => b
  | p + 1 => armBaseN sz 3 (p == 0) 0 64 (selN sz b p + 6)

/-- The slot of chain `r`'s step `s` in a group from `b` (`slotsT`). -/
def slotsN (sz : ℕ) (fold : Bool) (b r s : ℕ) : ℕ :=
  b + 6 + (if fold then 1 else 0) + (1 + 3 * (sz + 1)) * r + 1 + (sz + 1) * s + sz

/-- **Chain `r`'s start** in arm `k` of a group of `n` digits whose selector is `sel`. -/
def startN (sz n : ℕ) (fold : Bool) (sel k r : ℕ) : ℕ :=
  if k / 4 ^ r % 4 = 3 then slotsN sz fold sel r 2
  else walkBaseN (if k = 0 then sz + 1 else sz) k 0 r
    (if fold then armBaseN sz n fold 0 k (sel + 6) + 1 else armBaseN sz n fold 0 k (sel + 6))

/-! ## Tables -/

/-- Entry `k` of row `r`. -/
def offAt (tab : List (List ℕ)) (r k : ℕ) : ℕ := (tab.getD r []).getD k 0

/-- The table of a group of `n` digits: row `r`, entry `k`, the start of chain `r` in arm `k`
from selector `0`. -/
def offTab (sz n : ℕ) (fold : Bool) : List (List ℕ) :=
  (List.range n).map fun r ↦ (List.range (4 ^ n)).map fun k ↦ startN sz n fold 0 k r

/-- A scheme's three tables: the first group's, the other groups', the last chain's. -/
structure WotsTabs (sz : ℕ) (first rest last : List (List ℕ)) : Prop where
  first : first = offTab sz 3 true
  rest : rest = offTab sz 3 false
  last : last = offTab sz 1 false

end
end LeanVM.Guest.Fast
