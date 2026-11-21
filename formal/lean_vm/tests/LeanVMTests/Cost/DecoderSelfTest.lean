import LeanVMTests.Cost.DecoderChain

/-!
# Tests: the decoder's compiled self test on small inputs

`selfTestC` run on two small memories, its output the Lean function's value (`Located.selfTest`):
function `0` and `1` (no callee) fail; function `2` (not a registered loop helper) holds whatever
the frame; function `36` (a registered loop helper) holds when the cell past its arguments holds
the frame pointer (every word `1`, at the frame `1`) and fails otherwise (`DecoderChain`'s reader,
the word at `g^i` is `g^(i+1)`). Runs, compiled (`lake exe test-runs`).

The reader is `DecoderChain`'s, not a second compilation of it: the cost compiler names a function
it outlines by its index in the chain, so two modules that both extend the chain at the same point
give theirs the same name, and `test-runs`, which imports both, could not load them.
-/

namespace LeanVMTests.Cost.DecoderSelfTest

open LeanVM.Cost LeanVM.Cost.Decoder LeanVM.Parameters LeanVM.Core LeanVM.Guest.Located

/-- A compiled function's value on `vs`, in the program of the bodies `deps`. -/
def runOn (deps : List (ℕ × Term)) (i : ℕ) (vs : List MachineValue) : Option MachineValue :=
  (evaluateFunctionBody (MachineProgram.ofList deps) 100000 i vs).map (·.1)

/-- A memory of ones. -/
def oneReader (_ : K) : Option E := some 1
cost_compile oneReaderC := oneReader

def check (rd : Reader) (rdC : ℕ) (deps : List (ℕ × Term)) (j : ℕ) (fp : K) : Bool :=
  runOn (selfTestC.costDeps ++ deps) selfTestC.costIdx
    [.closure rdC [], encodeValue j, encodeValue fp] == some (encodeValue (selfTest rd j fp))

test_runs runs := [
  ("j = 0: fails", fun _ ↦ !selfTest oneReader 0 1 && check oneReader oneReaderC.costIdx oneReaderC.costDeps 0 1),
  ("j = 1: fails", fun _ ↦ !selfTest oneReader 1 1 && check oneReader oneReaderC.costIdx oneReaderC.costDeps 1 1),
  ("j = 2: holds", fun _ ↦ selfTest DecoderChain.smallReader 2 1 &&
    check DecoderChain.smallReader DecoderChain.smallReaderC.costIdx DecoderChain.smallReaderC.costDeps 2 1),
  ("j = 36, its pointer: holds", fun _ ↦
    selfTest oneReader 36 1 && check oneReader oneReaderC.costIdx oneReaderC.costDeps 36 1),
  ("j = 36, another word: fails", fun _ ↦
    !selfTest DecoderChain.smallReader 36 1 &&
      check DecoderChain.smallReader DecoderChain.smallReaderC.costIdx DecoderChain.smallReaderC.costDeps 36 1)]

end LeanVMTests.Cost.DecoderSelfTest
