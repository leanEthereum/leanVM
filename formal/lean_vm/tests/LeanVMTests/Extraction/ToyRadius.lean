import LeanVMTests.Extraction.ToyWords
import LeanVMTests.Runs

/-!
# Tests: the extractor's list decoder past the unique decoding radius

The list decoder (`decodeStacksAt`, `Toy.lean`) on a toy stack of `κ = 3`, `R = 2` (`n = 32`
columns, messages of `2^3 + 6 = 14` coefficients, `A = 22`) with ten errors: past the unique
decoding radius `⌊(32 − 14)/2⌋ = 9`, within the radius `n − A = 10`, it finds the stack (eleven
errors, past it, in `Toy.lean`). The slowest of the toy runs: compiled (`lake exe test-runs`).
-/

namespace LeanVMTests.Extraction

test_runs ToyRadius.runs := [
  ("ten errors, past the unique decoding radius: the stack", fun _ ↦
    decide (decodes 2 22 (randomStack 3 9)
      (corrupt 3 [1, 3, 5, 7, 9, 11, 13, 15, 17, 19] (wordOf 2 (randomStack 3 9))) = (true, 1)))]

end LeanVMTests.Extraction
