import LeanVM.Cost.Decoder.EntryTable
import LeanVMTests.Runs

/-!
# Tests: the decoder's compiled self test on small inputs

`selfTestC` run on two small memories, its output the Lean function's value (`Located.selfTest`):
function `0` and `1` (no callee) fail; function `2` (not a registered loop helper) holds whatever
the frame; function `35` (a registered loop helper) holds when the cell past its arguments holds
the frame pointer (every word `1`, at the frame `1`) and fails otherwise (the word at `g^i` is
`g^(i+1)`). Runs, compiled (`lake exe test-runs`).
-/

namespace LeanVMTests.Cost.DecoderSelfTest

open LeanVM.Cost LeanVM.Cost.Decoder LeanVM.Parameters LeanVM.Guest.Core LeanVM.Guest.Located

/-- A compiled function's value on `vs`, in the program of the bodies `deps`. -/
def runOn (deps : List (ℕ × Term)) (i : ℕ) (vs : List MachineValue) : Option MachineValue :=
  (evaluateFunctionBody (MachineProgram.ofList deps) 100000 i vs).map (·.1)

/-- A small memory: the word at `g^i` is `g^(i+1)` (as `E`) for `i < 64`. -/
def smallReader (a : K) : Option E :=
  ((List.range 64).find? fun i ↦ a == addressOfIndex i).map fun i ↦ ofK (addressOfIndex (i + 1))
cost_compile smallReaderC := smallReader

/-- A memory of ones. -/
def oneReader (_ : K) : Option E := some 1
cost_compile oneReaderC := oneReader

def check (rd : Reader) (rdC : ℕ) (deps : List (ℕ × Term)) (j : ℕ) (fp : K) : Bool :=
  runOn (selfTestC.costDeps ++ deps) selfTestC.costIdx
    [.closure rdC [], encodeValue j, encodeValue fp] == some (encodeValue (selfTest rd j fp))

test_runs runs := [
  ("j = 0: fails", fun _ ↦ !selfTest oneReader 0 1 && check oneReader oneReaderC.costIdx oneReaderC.costDeps 0 1),
  ("j = 1: fails", fun _ ↦ !selfTest oneReader 1 1 && check oneReader oneReaderC.costIdx oneReaderC.costDeps 1 1),
  ("j = 2: holds", fun _ ↦ selfTest smallReader 2 1 && check smallReader smallReaderC.costIdx smallReaderC.costDeps 2 1),
  ("j = 35, its pointer: holds", fun _ ↦
    selfTest oneReader 35 1 && check oneReader oneReaderC.costIdx oneReaderC.costDeps 35 1),
  ("j = 35, another word: fails", fun _ ↦
    !selfTest smallReader 35 1 && check smallReader smallReaderC.costIdx smallReaderC.costDeps 35 1)]

end LeanVMTests.Cost.DecoderSelfTest
