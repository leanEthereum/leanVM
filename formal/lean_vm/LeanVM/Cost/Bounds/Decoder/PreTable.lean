module

public import LeanVM.Cost.Decoder.PreTable

/-!
# Bound: the preconditions' table, built once

`preTableC` (`Cost/Decoder/PreTable.lean`): the literal table of the functions' preconditions
(`Guest.Fast.preTable`), a body of the table's constructors the decoder's top runs once.
**`preTable_cost`**: exactly `12762` (`Kpre`).
-/

namespace LeanVM.Cost.Bounds

open LeanVM.Cost LeanVM.Cost.Decoder

public section

/-- **The preconditions' table** (`preTableC`), built once: `12762`. -/
theorem preTable_cost (P : MachineProgram) (hP : Includes P preTableC.costDeps) :
    machineCost P preTableC.costIdx [] = 12762 :=
  preTableC.costEq P hP

end

end LeanVM.Cost.Bounds
