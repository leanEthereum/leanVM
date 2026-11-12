import LeanVMTests.Extraction.ToyWords

/-!
# Tests: the extractor's fast path on toy codes

The fast path (`fastStacks`, `LeanVM/Protocol/Extraction/Extractor.lean`) decodes a word without
errors by interpolation alone, also at the smallest deployed shape (`μ = 16`, `R = 1`), and gives
up on a word with an error among its first `2^κ` columns, which the list decoder still decodes
(`Toy.lean`; toy words of `ToyWords.lean`).
-/

namespace LeanVMTests.Extraction

open CompPoly LeanVM.Parameters LeanVM.Parameters.Whir LeanVM.Extraction
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile

/-! ## The fast path -/

-- `κ = 2`, `R = 2`: a word without errors.
#guard fastDecodes 2 (randomStack 2 8) (wordOf 2 (randomStack 2 8))

-- An error in column `0`, among the interpolated ones: the fast path finds nothing (the list
-- decoder decodes such a word, `Toy.lean`).
#guard
  let w := corrupt 2 [0] (wordOf 2 (randomStack 2 8))
  (fastStacks 8 2 fun v ↦ w.getD v []).isEmpty

-- An error past them: the fast path still finds the stack (it agrees on `15` of `16` columns).
#guard fastDecodes 2 (randomStack 2 8) (corrupt 2 [13] (wordOf 2 (randomStack 2 8)))

-- The smallest deployed shape, `μ = 16`, `R = 1`: a stack of `2^16` words on `2048` columns,
-- decoded by the fast path (interpreted, the word's encoding included).
#guard fastDecodes 1 (randomStack 5 16) (wordOf 1 (randomStack 5 16))

end LeanVMTests.Extraction
