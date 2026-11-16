/-
  LeanVM.Guest.PlaceCode

  A place of the back end written as one natural, and the word it names in a frame: how the
  guest's decoder reads a value of a function from the table of its places.
-/

module

public import LeanVM.Guest.Core

/-!
# Place codes

The back end puts a value in a frame cell `c` (`Loc.cell c`) or, for a pointer into the frame, in
no cell: the word of cell `c` times `g^e` (`Loc.shifted c e`). A table of the guest's places
writes each as one natural, `c` and `c + 2^20 * (e + 1)` respectively, and `0` for a value of no
place (no place is cell `0`). `placeWith rd fp c` is the word code `c` names in the frame at `fp`,
read with `rd`; `placeVal rd fp row v` the word of value `v` of a function whose codes are `row`
(`0` for a value off the row or of a path or tag, which the back end's input never has).
-/

namespace LeanVM.Guest

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core

@[expose] public section

/-- **The word place code `c` names** in the frame at `fp`: none for `0`, the cell `c` below `2^20`,
else the cell `c % 2^20` times `g^(c / 2^20 - 1)`. -/
def placeWith (rd : Reader) (fp : K) (c : ℕ) : E :=
  if c = 0 then 0
  else if c < 2 ^ 20 then (rd (fp * addressOfIndex c)).getD 0
  else (rd (fp * addressOfIndex (c % 2 ^ 20))).getD 0 * ofK (addressOfIndex (c / 2 ^ 20 - 1))

/-- **The word of value `v`** of a function whose place codes are `row`. -/
def placeVal (rd : Reader) (fp : K) (row : Array ℕ) (v : V) : E :=
  if v.path.isEmpty && v.tag == 0 then placeWith rd fp (row.getD v.idx 0) else 0

end
end LeanVM.Guest
