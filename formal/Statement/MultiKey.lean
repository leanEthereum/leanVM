module

public import Statement.LeanXmss
public import Statement.LeanSphincs

/-!
# Many keys: the multi-key SUF-CMA game of leanXMSS and leanSPHINCS

An aggregate holds signatures under many keys. `k` independently generated keys of a scheme are
one scheme (`Scheme.multiKey`): the seeds are sampled one per key, the keys generated in key order,
a request `(j, r)` is answered by key `j`'s signer, a forgery `(j, f)` is verified under key `j`'s
public key and wins by the scheme's winning condition on the transcript of key `j`'s requests
(`keyLog`). The multi-key game is the game of `SufCma.lean` for that scheme
(`forgeryGame (scheme.multiKey k)`): one permutation `π`, the adversary sees every public key, asks
any key to sign, and wins by a forgery under any one key that verifies and is fresh for that key's
own requests. `MultiKeyStronglyUnforgeable` bounds it at `k · (q + slack + k) · 2^-bits` for every
`k` up to `maxKeys`, each key signing at most `maxSignings` requests; as in `StronglyUnforgeable`
the adversary's own calls of `π` and `π⁻¹` are charged, the honest parties' hashing (every key's
generation and signer, the forgery's verification) is not. The factor `k` is the key the forgery
names; the term `k²` is two keys clashing (equal public parameters, mainly).
-/

@[expose] public section

open OracleComp OracleSpec
open scoped ENNReal

namespace Common.SufCma

open HashSig.OverPermutation (sequenceFin)

variable {Seed PublicKey SecretKey SigningRequest SigningResponse Forgery : Type}

/-- **Key `j`'s transcript**: the requests to key `j`, with their answers, in order. -/
def keyLog {k : ℕ} (j : Fin k)
    (log : QueryLog (Fin k × SigningRequest →ₒ SigningResponse)) :
    QueryLog (SigningRequest →ₒ SigningResponse) :=
  log.filterMap fun e ↦ if e.1.1 = j then some ⟨e.1.2, e.2⟩ else none

/-- **`k` keys of a scheme as one scheme**: a seed and a key pair per key, generated in key order;
a request `(j, r)` signed by key `j`; a forgery `(j, f)` verified under key `j`'s public key, and a
win by the scheme's condition on key `j`'s transcript. -/
def Scheme.multiKey (k : ℕ)
    (scheme : Scheme Seed PublicKey SecretKey SigningRequest SigningResponse Forgery) :
    Scheme (Fin k → Seed) (Fin k → PublicKey) (Fin k → SecretKey) (Fin k × SigningRequest)
      SigningResponse (Fin k × Forgery) where
  sampleSeed := sequenceFin fun _ ↦ scheme.sampleSeed
  generateKeys seeds := do
    let pairs ← sequenceFin fun j ↦ scheme.generateKeys (seeds j)
    return (fun j ↦ (pairs j).1, fun j ↦ (pairs j).2)
  sign secretKeys request := scheme.sign (secretKeys request.1) request.2
  verify publicKeys forgery := scheme.verify (publicKeys forgery.1) forgery.2
  winningCondition log forgery := scheme.winningCondition (keyLog forgery.1 log) forgery.2

/-- **The adversary's signing requests to key `j`**: one each; a coin, a permutation call and a
request to another key nothing. -/
def signingRequestToKeyCost {k : ℕ} (j : Fin k) :
    RandomPermutationOracles.Domain ⊕ (Fin k × SigningRequest) → ℕ
  | .inl _ => 0
  | .inr r => if r.1 = j then 1 else 0

/-- **Multi-key SUF-CMA security in the random-permutation model**: for every number of keys
`1 ≤ k ≤ maxKeys`, every adversary against `k` keys that itself makes at most `q` calls of `π` and
`π⁻¹` and at most `maxSignings` signing requests to each key, on every path whatever the answers,
wins the game of `scheme.multiKey k` with probability at most `k · (q + slack + k) · 2^-bits`. -/
def MultiKeyStronglyUnforgeable
    (scheme : Scheme Seed PublicKey SecretKey SigningRequest SigningResponse Forgery)
    (maxKeys maxSignings slack securityBits : ℕ) : Prop :=
  ∀ k, 1 ≤ k → k ≤ maxKeys → ∀ q, ∀ adversary : (Fin k → PublicKey) →
      OracleComp (RandomPermutationOracles + (Fin k × SigningRequest →ₒ SigningResponse))
        (Fin k × Forgery),
    (∀ pks, QueryCostAtMost (adversary pks) adversaryPermutationCost q) →
    (∀ pks j, QueryCostAtMost (adversary pks) (signingRequestToKeyCost j) maxSignings) →
      Pr{let b ← runWithRandomPermutation (forgeryGame (scheme.multiKey k) adversary)}[b = true] ≤
        (k : ℝ≥0∞) * ((q : ℝ≥0∞) + slack + k) * (2 : ℝ≥0∞)⁻¹ ^ securityBits

end Common.SufCma

namespace LeanXmss.RandomPermutationModel

open Common.SufCma

/-- **leanXMSS for many keys**: for up to `2^32` independently generated keys, an adversary that
itself makes at most `q` calls of `π` and `π⁻¹` and at most `lifetime = 2^32` signing requests to
each key forges under some key with probability at most `k · (q + 2^10 + k) · 2^-127`. Proved by
`XmssSecurity.leanXmss_multiKey`. -/
abbrev LeanXmssMultiKeyStronglyUnforgeable : Prop :=
  MultiKeyStronglyUnforgeable sufCmaScheme (2 ^ 32) lifetime securitySlack 127

end LeanXmss.RandomPermutationModel

namespace Sphincs

open Common.SufCma

/-- **leanSPHINCS for many keys**: for up to `2^32` independently generated keys, an adversary that
itself makes at most `q` calls of `π` and `π⁻¹` and at most `N = 1,182,000,000` signing requests to
each key forges under some key with probability at most `k · (q + 2^19 + k) · 2^-127`. Proved by
`Sphincs.leanSphincs_multiKey`. -/
abbrev LeanSphincsMultiKeyStronglyUnforgeable : Prop :=
  MultiKeyStronglyUnforgeable RandomPermutationModel.sufCmaScheme (2 ^ 32) signatureLimit
    securitySlack 127

end Sphincs

end
