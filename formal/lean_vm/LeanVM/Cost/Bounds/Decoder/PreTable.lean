module

public import LeanVM.Cost.Decoder.PreTable

/-!
# Bound: the preconditions' table, built once

`preTableC` (`Cost/Decoder/PreTable.lean`): the literal table of the functions' preconditions
(`Guest.Fast.preTable`), a body of the table's constructors the decoder's top runs once.
**`preTable_cost`**: exactly `20785` (`Kpre`).
-/

namespace LeanVM.Cost.Bounds

open LeanVM.Cost LeanVM.Cost.Decoder

public section

/-- **The preconditions' table** (`preTableC`), built once: `20785`. -/
theorem preTable_cost (P : MachineProgram) (hP : Includes P preTableC.costDeps) :
    machineCost P preTableC.costIdx [] = 20785 :=
  preTableC.costEq P hP

end

end LeanVM.Cost.Bounds
