module

public import LeanVM.Cost.Bounds.Decoder.PreTestDefs
public import LeanVM.Guest.Fast.PreTable

/-!
# Bound: the preconditions' table has the deployed shape, by evaluation

A module of its own, importing the table (`Guest.Fast.preTable`, `879` entries, `424` not
`none`) and the shape's definition alone: **`preTable_shape`**, every entry has at most one
check of each kind, at most `99` bounds and memory cells (the most an entry has), exponents below
`2^7` (the largest is `99`), logarithms' bounds at most `34` (they are `34`, `29` and `11`):
the decoder's precondition test reads them by the lanes' scan (`Guest.Fast.powBelow`), not a
logarithm.
-/

namespace LeanVM.Cost.Bounds

public section

/-- **The deployed table's shape** (`fnPreShape`), evaluated by the kernel. -/
theorem preTable_shape : tableShape LeanVM.Guest.Fast.preTable = true := by
  decide +kernel

end

end LeanVM.Cost.Bounds
