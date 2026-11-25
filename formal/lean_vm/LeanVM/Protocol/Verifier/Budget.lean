/-
  LeanVM.Protocol.Verifier.Budget

  The budgets of the verifier's queries and cost that the error arithmetic in bits reads.
-/

module

public import Mathlib.Data.Nat.Notation

/-!
# The verifier's budgets

The proofs count the verifier's oracle queries (`LeanVM.Protocol.Verifier.leanVmQueryBound`) and its
program's cost (`LeanVM.Protocol.Verifier.leanVmCost`) exactly, and the errors of
`LeanVM.Protocol.Errors` are stated at those counts. The bounds in bits read them through the round
budgets `verifierQueries` and `verifierCost`, which the counts fit (`leanVmQueryBound_add_three_le`,
`leanVmCost_le`), so that no count is restated as a numeral.
-/

namespace LeanVM

@[expose] public section

/-- The budget of the verifier's oracle queries, to Keccak-256 and Keccak-f together, on every
statement and proof: the IV, the seed's permutation, the sponge's permutations (one per challenge
and one per four absorbed scalars) and every Merkle hash of the openings. The proof establishes
`LeanVM.Protocol.Verifier.leanVmQueryBound` over every admissible shape, within this budget
leaving room for the agreement-set error's three further terms (`leanVmQueryBound_add_three_le`). -/
def verifierQueries : ℕ := 2 ^ 14

/-- The budget of the verifier program's cost, in quarters of a query: the proof establishes
`LeanVM.Protocol.Verifier.leanVmCost` (`leanVmCost_le`). -/
def verifierCost : ℕ := 2 ^ 16

end

end LeanVM
