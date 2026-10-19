/-
  LeanVM.Guest.B2C.CntWeight

  The instruction counts as weights: `cnt T op` is `T`'s weight at `pathMax · op` and the jump
  table's `SET`s, the form `B1.Main.mainComplete_of` takes.
-/

module

public import LeanVM.Guest.B2C.Defs

/-!
# Counts as weights

`cnt_le_weight`: `cnt t op ≤ t.weight (pathMax · op) + jtSets op` (`mainComplete_of`'s and
`ea_mainComplete`'s `hcnt`, at `ω op := (pathMax · op)` and `jt := jtSets`).
-/

namespace LeanVM.Guest.B2C

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Memory

@[expose] public section

/-- **The counts within the weights**: by definition. -/
theorem cnt_le_weight (t : Tree) (op : Opcode) : cnt t op ≤ t.weight (pathMax · op) + jtSets op :=
  le_rfl

end
end LeanVM.Guest.B2C
