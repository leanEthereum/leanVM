module

public import LeanVM.Guest.Fast.LogG
public import LeanVM.Guest.Fast.Numbers
public import LeanVM.Guest.Fast.Common
public import LeanVM.Guest.B1.Sig.CodewordComplete

/-!
# A codeword's chain starts, as numbers

The cell holding chain `i`'s hinted start is read
off the template generators (`armBase`, `armT`, a `WotsT` of functions). It is arithmetic in the
step's size `W.size`, the group's selector cell and the digit value its dispatch takes:

* `walkBaseN` (`Fast/Numbers.lean`): the walks' bases, in numbers (`walkBase_eq`);
* `cwCell`: the start's cell off the groups' selector cells, three small tables (one for
  the first group, one for the others, one for the last chain) and the exponent search `logGT`;
  `cwCellA`, its form over arrays (`cwCellA_eq`).
-/

namespace LeanVM.Guest.Fast

open LeanVM.Parameters LeanVM.Guest.Core LeanVM.Guest.B1.Sig

@[expose] public section

/-! ## Equal to the generators -/

theorem walkBase_eq (stride k : ℕ) :
    ∀ (r j b : ℕ), walkBase stride k r j b = walkBaseN stride k r j b
  | _, 0, _ => rfl
  | r, j + 1, _ => walkBase_eq stride k (r + 1) j _

/-! ## Off tables -/

/-- **Chain `i`'s start cell**, off the selector cells `sel` of the `G + 1` groups and the
tables. -/
def cwCell (G : ℕ) (sel : List ℕ) (first rest last : List (List ℕ)) (σ : Val) (i : ℕ) : ℕ :=
  let s := sel.getD (i / 3) 0
  if i / 3 < G then
    s + offAt (if i / 3 = 0 then first else rest) (i % 3) (logGT (σ (.n s)) 64)
  else s + offAt last (i % 3) (logGT (σ (.n s)) 4)

/-- **Chain `i`'s start cell, off arrays** (`cwCell`): the selectors `sel`, the tables `first`,
`rest`, `last` (`tabA`) and the lanes of `g^k` (`gLanes`), built once by the caller. -/
def cwCellA (lanes : List ℕ) (G : ℕ) (sel : Array ℕ) (first rest last : Array (Array ℕ))
    (σ : Val) (i : ℕ) : ℕ :=
  let s := sel.getD (i / 3) 0
  if i / 3 < G then
    s + offAtA (if i / 3 = 0 then first else rest) (i % 3) (logGTWith lanes (σ (.n s)) 64)
  else s + offAtA last (i % 3) (logGTWith lanes (σ (.n s)) 4)

theorem cwCellA_eq (G : ℕ) (sel : List ℕ) (first rest last : List (List ℕ)) (σ : Val) (i : ℕ) :
    cwCellA gLanes G sel.toArray (tabA first) (tabA rest) (tabA last) σ i =
      cwCell G sel first rest last σ i := by
  unfold cwCellA cwCell
  simp only [getD_toArray, logGTWith_gLanes]
  split_ifs <;> simp only [offAtA_tabA]

end
end LeanVM.Guest.Fast
