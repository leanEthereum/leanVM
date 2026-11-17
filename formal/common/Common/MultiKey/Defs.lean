module

public import Common.AdvBudget

@[expose] public section

/-!
# The multi-key SUF-CMA game

`k` independently generated keys of a scheme form one scheme (`Scheme.multiKey`): the seeds are
sampled one per key, the keys generated in key order, a request `(j, r)` is answered by key `j`'s
signer, a forgery `(j, f)` is verified under key `j`'s public key and wins by the scheme's winning
condition on the transcript of key `j`'s requests (`keyLog`). The multi-key game is the
statement's game of that scheme (`forgeryGame (scheme.multiKey k)`): one shared permutation, the
adversary sees every public key, asks any key to sign, and wins by a fresh valid forgery under any
one of them. `MultiKeyStronglyUnforgeable` bounds it at `k · (q + slack + k) · 2^-bits` for every
`k` up to `maxKeys`, each key signing at most `maxSignings` requests; the adversary's own calls of
`π` and `π⁻¹` are charged as in `StronglyUnforgeable`, the honest parties' hashing (every key's
generation, signer and the forgery's verification) is not.

The same construction on hash-query schemes (`SchemeWithHash.multiKey`) passes to the
permutation by `SchemeWithHash.overPermutation` (`multiKey_overPermutation`).
-/

open OracleComp OracleSpec MeasureTheory
open scoped ENNReal
open HashSig.OverPermutation (sequenceFin)

namespace Common.SufCma

variable {Seed PK SK Req Resp F : Type}

/-- **Key `j`'s transcript**: the requests to key `j`, with their answers, in order. -/
def keyLog {k : ℕ} (j : Fin k) (log : QueryLog (Fin k × Req →ₒ Resp)) :
    QueryLog (Req →ₒ Resp) :=
  log.filterMap fun e ↦ if e.1.1 = j then some ⟨e.1.2, e.2⟩ else none

/-- **`k` keys of a scheme as one scheme**: a seed and a key pair per key, generated in key order;
a request `(j, r)` signed by key `j`; a forgery `(j, f)` verified under key `j`'s public key, and a
win by the scheme's condition on key `j`'s transcript. -/
def Scheme.multiKey (k : ℕ) (scheme : Scheme Seed PK SK Req Resp F) :
    Scheme (Fin k → Seed) (Fin k → PK) (Fin k → SK) (Fin k × Req) Resp (Fin k × F) where
  sampleSeed := sequenceFin fun _ ↦ scheme.sampleSeed
  generateKeys seeds := do
    let pairs ← sequenceFin fun j ↦ scheme.generateKeys (seeds j)
    return (fun j ↦ (pairs j).1, fun j ↦ (pairs j).2)
  sign sks request := scheme.sign (sks request.1) request.2
  verify pks forgery := scheme.verify (pks forgery.1) forgery.2
  winningCondition log forgery := scheme.winningCondition (keyLog forgery.1 log) forgery.2

/-- **The adversary's signing requests to key `j`**: one each; a coin, a permutation call and a
request to another key nothing. -/
def signingRequestToKeyCost {k : ℕ} (j : Fin k) :
    RandomPermutationOracles.Domain ⊕ (Fin k × Req) → ℕ
  | .inl _ => 0
  | .inr r => if r.1 = j then 1 else 0

/-- **Multi-key SUF-CMA security in the random-permutation model**: for every number of keys
`1 ≤ k ≤ maxKeys`, every adversary against `k` keys that itself makes at most `q` calls of `π` and
`π⁻¹` and at most `maxSignings` signing requests to each key, on every path whatever the answers,
wins the game of `scheme.multiKey k` with probability at most `k · (q + slack + k) · 2^-bits`. -/
def MultiKeyStronglyUnforgeable (scheme : Scheme Seed PK SK Req Resp F)
    (maxKeys maxSignings slack securityBits : ℕ) : Prop :=
  ∀ k, 1 ≤ k → k ≤ maxKeys → ∀ q, ∀ adversary : (Fin k → PK) →
      OracleComp (RandomPermutationOracles + (Fin k × Req →ₒ Resp)) (Fin k × F),
    (∀ pks, QueryCostAtMost (adversary pks) adversaryPermutationCost q) →
    (∀ pks j, QueryCostAtMost (adversary pks) (signingRequestToKeyCost j) maxSignings) →
      Pr{let b ← runWithRandomPermutation (forgeryGame (scheme.multiKey k) adversary)}[b = true] ≤
        (k : ℝ≥0∞) * ((q : ℝ≥0∞) + slack + k) * (2 : ℝ≥0∞)⁻¹ ^ securityBits

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
