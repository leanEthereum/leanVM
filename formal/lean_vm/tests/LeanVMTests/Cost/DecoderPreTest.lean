import LeanVM.Cost.Decoder.PreTable
import LeanVMTests.Runs

/-!
# Tests: the decoder's compiled precondition test on small inputs

`preTestAtC` run on a small memory (the word at `g^i` is `g^(i+1)`, `i < 64`), a small table of
preconditions and the logarithm's tables (`discreteLogTables`, passed in as a value), its output
the Lean function's value: an entry environment's check, a bound and a memory bound, each holding
or not, and the functions without a precondition (`none`) or outside `2 … 1803`. Runs, compiled
(`lake exe test-runs`): each pays seconds in the interpreter.
-/

namespace LeanVMTests.Cost.DecoderPreTest

open LeanVM.Cost LeanVM.Cost.Decoder LeanVM.Parameters LeanVM.Guest.Core LeanVM.Guest.Exec
open LeanVM.Guest.Fast LeanVM.Extraction.Fast

/-- A compiled function's value on `vs`, in the program of the bodies `deps`. -/
def runOn (deps : List (ℕ × Term)) (i : ℕ) (vs : List MachineValue) : Option MachineValue :=
  (evaluateFunctionBody (MachineProgram.ofList deps) 100000 i vs).map (·.1)

/-- A small memory: the word at `g^i` is `g^(i+1)` (as `E`) for `i < 64`. -/
def smallReader (a : K) : Option E :=
  ((List.range 64).find? fun i ↦ a == addressOfIndex i).map fun i ↦ ofK (addressOfIndex (i + 1))
cost_compile smallReaderC := smallReader

/-- A table: function `2` checks cell `6` holds `g^7` and cell `3` holds `g^e`, `e < 10`; `3` that
cell `6` holds the frame pointer; `4` the bound `e < 4` at cell `3`; `5` the memory bound at cell
`0`'s address, `3` cells below `g^10`; `6` the same below `g^5` (the word there is `g^5`); `7`
nothing (`none`). -/
def smallTable : Array (Option FnPre) := #[none, none,
  some ⟨[(6, .gp 7)], [(3, 10)], []⟩, some ⟨[(6, .fpg 0)], [], []⟩,
  some ⟨[], [(3, 4)], []⟩, some ⟨[], [], [(0, 3, 10)]⟩, some ⟨[], [], [(0, 3, 5)]⟩, none]

def D : DiscreteLogTables := discreteLogTables

def check (j : ℕ) (fp : K) : Bool :=
  runOn (preTestAtC.costDeps ++ smallReaderC.costDeps) preTestAtC.costIdx
    [encodeValue D, encodeValue smallTable, encodeValue genPows, .closure smallReaderC.costIdx [],
      encodeValue j, encodeValue fp] ==
    some (encodeValue (preTestAt D smallTable genPows smallReader j fp))

test_runs runs := [
  ("j = 2, fp = 1: holds", fun _ ↦ preTestAt D smallTable genPows smallReader 2 1 && check 2 1),
  ("j = 3, fp = 1: fails", fun _ ↦ !preTestAt D smallTable genPows smallReader 3 1 && check 3 1),
  ("j = 4, fp = 1: fails", fun _ ↦ !preTestAt D smallTable genPows smallReader 4 1 && check 4 1),
  ("j = 5, fp = 1: holds", fun _ ↦ preTestAt D smallTable genPows smallReader 5 1 && check 5 1),
  ("j = 6, fp = 1: fails", fun _ ↦ !preTestAt D smallTable genPows smallReader 6 1 && check 6 1),
  ("j = 7, fp = 1: holds", fun _ ↦ preTestAt D smallTable genPows smallReader 7 1 && check 7 1),
  ("j = 1, fp = 1: fails", fun _ ↦ !preTestAt D smallTable genPows smallReader 1 1 && check 1 1),
  ("j = 2, fp = g^0: holds", fun _ ↦
    preTestAt D smallTable genPows smallReader 2 (addressOfIndex 0) && check 2 (addressOfIndex 0)),
  ("j = 2, fp = g^1: fails", fun _ ↦
    !preTestAt D smallTable genPows smallReader 2 (addressOfIndex 1) && check 2 (addressOfIndex 1)),
  -- The powers table, compiled: `gen^(2^j)`, `j < 34`, by squarings.
  ("genPowsC", fun _ ↦ runOn genPowsC.costDeps genPowsC.costIdx [] == some (encodeValue genPows))]

end LeanVMTests.Cost.DecoderPreTest
