import LeanVM.Cost.Extractor.GsRun
import LeanVMTests.Cost.Samples
import LeanVMTests.Extraction.ToyWords
import LeanVMTests.Runs

/-!
# Tests: the compiled decoder runs

The decoder's compiled pieces (`LeanVM.Cost.Extractor`: the roots in `K`, Roth–Ruckenstein's
substitution; the interpolation and the lane's run in `PMChain.lean`) compute their functions' values
on small inputs, at the prices recorded here: runs, compiled (`lake exe test-runs`).
-/

namespace LeanVMTests.Cost.Decoder

open LeanVM.Cost LeanVM.Cost.Extractor LeanVM.Parameters LeanVM.Extraction LeanVM.Extraction.Fast
open LeanVMTests.Extraction LeanVMTests.Cost CompPoly CompPoly.GuruswamiSudan

/-- The value and the price of function `i`'s run on `args` in the program of `deps`. -/
def run (deps : List (ℕ × Term)) (i : ℕ) (args : List MachineValue) : Option (MachineValue × ℕ) :=
  evaluateFunctionBody (MachineProgram.ofList deps) 1000000 i args


/-! Roth–Ruckenstein's substitution by the butterfly (`substituteBF`, compiled on demand as
`substituteBF.c97`): its value is `substituteFast`'s, and its price, measured. One more
coefficient per row costs `≈ 68` steps per scaled row addition (`axpyRow`: the scaling, the raw
sum, one trim) and `28` per row (the shift by `X^t`); the proved bound (`substituteBFC_cost`)
charges a constant per row and level. -/

/-- The butterfly's price on `ny` rows of `nx` random coefficients. -/
def bfPrice (nx ny : ℕ) : Option ℕ :=
  (run LeanVM.Cost.Auto.LeanVM.Extraction.Fast.substituteBF.c97.costDeps
    LeanVM.Cost.Auto.LeanVM.Extraction.Fast.substituteBF.c97.costIdx
    [MachineEncoding.encodeValue (randomBivariate 7 nx ny), MachineEncoding.encodeValue (K.ofBits 5)]).map
    Prod.snd

/-- The scaled row additions of the butterfly on `n` rows: the bits set below `n`. -/
def bfOps (n : ℕ) : ℕ := ((List.range n).map fun y ↦ (Nat.toDigits 2 y).count '1').sum

test_runs runs := [
  ("rootsInFieldC is rootsInFieldFast", fun _ ↦
    (run rootsInFieldC.costDeps rootsInFieldC.costIdx [MachineEncoding.encodeValue rootPoly]).map (·.1) ==
      some (MachineEncoding.encodeValue (rootsInFieldFast rootPoly))),
  ("substituteBF is substituteFast", fun _ ↦ (List.range 3).all fun s ↦
    let Q := randomBivariate s 30 33
    (run LeanVM.Cost.Auto.LeanVM.Extraction.Fast.substituteBF.c97.costDeps
      LeanVM.Cost.Auto.LeanVM.Extraction.Fast.substituteBF.c97.costIdx
      [MachineEncoding.encodeValue Q, MachineEncoding.encodeValue (K.ofBits (lcg s))]).map (·.1) ==
      some (MachineEncoding.encodeValue (substituteFast Q (K.ofBits (lcg s))))),
  ("the butterfly's prices", fun _ ↦ bfPrice 100 33 == some 666967 && bfPrice 200 33 == some 1313767)]

-- per extra coefficient: `81` additions (`bfOps 33`) at `≈ 68`, `33` rows at `28`
#guard bfOps 33 == 81 && (1313767 - 666967) / 100 == 6468 && (6468 - 28 * 33) / 81 == 68

end LeanVMTests.Cost.Decoder
