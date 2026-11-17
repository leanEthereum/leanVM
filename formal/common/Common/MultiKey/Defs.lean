module

public import Common.AdvBudget
public import Statement.MultiKey

@[expose] public section

/-!
# The multi-key SUF-CMA game of hash-query schemes

The statement's multi-key game (`Statement/MultiKey.lean`: `Scheme.multiKey`, `keyLog`,
`signingRequestToKeyCost`, `MultiKeyStronglyUnforgeable`) is the single-key game of `k` keys as one
scheme. The same construction on hash-query schemes (`SchemeWithHash.multiKey`) passes to the
permutation by `SchemeWithHash.overPermutation` (`multiKey_overPermutation`).
-/

open OracleComp OracleSpec MeasureTheory
open scoped ENNReal
open HashSig.OverPermutation (sequenceFin)

namespace Common.SufCma

variable {Seed PK SK Req Resp F : Type}

/-- **`k` keys of a hash-query scheme as one scheme**, as `Scheme.multiKey`. -/
def SchemeWithHash.multiKey (k : ℕ) (S : SchemeWithHash Seed PK SK Req Resp F) :
    SchemeWithHash (Fin k → Seed) (Fin k → PK) (Fin k → SK) (Fin k × Req) Resp (Fin k × F) where
  sample := sequenceFin fun _ ↦ S.sample
  keygen seeds := do
    let pairs ← sequenceFin fun j ↦ S.keygen (seeds j)
    return (fun j ↦ (pairs j).1, fun j ↦ (pairs j).2)
  sign sks request := S.sign (sks request.1) request.2
  verify pks forgery := S.verify (pks forgery.1) forgery.2
  win log forgery := S.win (keyLog forgery.1 log) forgery.2

/-- The `k` keys of a hash-query scheme over `π` are the `k` keys of the scheme over `π`. -/
theorem multiKey_overPermutation (k : ℕ) (S : SchemeWithHash Seed PK SK Req Resp F) :
    (S.multiKey k).overPermutation = S.overPermutation.multiKey k := by
  simp only [SchemeWithHash.overPermutation, SchemeWithHash.multiKey, Scheme.multiKey,
    simulateQ_bind, simulateQ_pure, LeanXmss.simulateQ_sequenceFin]

end Common.SufCma
