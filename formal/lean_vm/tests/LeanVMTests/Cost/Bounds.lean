import LeanVMTests.Cost.Samples
import LeanVM.Cost.Bounds.FieldLib

/-!
# Tests: the proved bounds against measured prices

A run on the fixtures of `Cost/Samples.lean`, its price next to the closed form the bound proves:
the bound holds, and how loose it is.
-/

namespace LeanVMTests.Cost

open LeanVM.Cost LeanVM.Cost.Library LeanVM.Parameters

/-- The price of function `i`'s run on `args` in the program of `deps`. -/
def price (deps : List (ℕ × Term)) (i : ℕ) (args : List MachineValue) : Option ℕ :=
  (evaluateFunctionBody (MachineProgram.ofList deps) 100000 i args).map (·.2)

/-! The field inverse (`invK_cost`, Itoh–Tsujii): `2823` on `7`, the bound `2823` (tight). -/
#guard price LeanVM.Cost.Auto.BF64.invItohTsujii.c10.costDeps LeanVM.Cost.Auto.BF64.invItohTsujii.c10.costIdx
    [MachineEncoding.encodeValue (K.ofBits 7)] == some 2823

end LeanVMTests.Cost
