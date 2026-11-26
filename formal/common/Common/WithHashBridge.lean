module

public import Common.WithHash

@[expose] public section

/-!
# The statement's SUF-CMA game is the hash-query form, the hash over `π`

A hash-query scheme (`Common.WithHash`) with each query answered by Keccak-256 over the model's
permutation `π` (`SufCma.schemeHashOverPermutation`) is a scheme of the statement's game
(`SufCma.SchemeWithHash.overPermutation`), whose game is the hash-query one
(`SufCma.forgeryGame_overPermutation`).
-/

open OracleComp OracleSpec

namespace Common.SufCma

variable {Seed PK SK Req Resp F : Type}

/-- **A hash-query scheme over `π`**: its algorithms with each hash query answered by Keccak-256
over `π` (`schemeHashOverPermutation`). -/
def SchemeWithHash.overPermutation (S : SchemeWithHash Seed PK SK Req Resp F) :
    Scheme Seed PK SK Req Resp F where
  sampleSeed := S.sample
  generateKeys seed := simulateQ schemeHashOverPermutation (S.keygen seed)
  sign sk r := simulateQ schemeHashOverPermutation (S.sign sk r)
  verify pk f := simulateQ schemeHashOverPermutation (S.verify pk f)
  winningCondition := S.win

/-- The statement's game of a hash-query scheme over `π` is its hash-query game. -/
theorem forgeryGame_overPermutation (S : SchemeWithHash Seed PK SK Req Resp F)
    (main : PK → OracleComp (RandomPermutationOracles + (Req →ₒ Resp)) F) :
    forgeryGame S.overPermutation main = forgeryGameWithHash S main := rfl

end Common.SufCma

end
