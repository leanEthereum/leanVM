import SphincsSecurity.Statement

open OracleComp OracleSpec ENNReal

namespace SphincsSecurity

/-- `unifSpec` for uniform sampling, `HashSpec` for the random oracle. A query is `.inl` to sample or `.inr` to hash, so `HasHashQueryBound` counts only the hash side. -/
abbrev OracleWorld := unifSpec + HashSpec

namespace Seeded

open Concrete

noncomputable def keygen : OracleComp OracleWorld (PublicKey × SecretKey) := do
  let seed ← liftM sampleMasterSeed
  let parameter ← liftM (deriveKey 0 .parameter seed : OracleComp HashSpec Digest)
  let root ← liftM (treeRoot parameter topLayer rootTree seed : OracleComp HashSpec Digest)
  return (⟨root, parameter⟩, ⟨seed, parameter, root⟩)

end Seeded

/-- The random-oracle semantics: hash queries are answered lazily and consistently by uniform sampling and cached; uniform-sampling queries are forwarded unchanged. -/
noncomputable def romImpl : QueryImpl OracleWorld (StateT (QueryCache HashSpec) ProbComp) :=
  unifFwdImpl HashSpec +
    (randomOracle : QueryImpl HashSpec (StateT (QueryCache HashSpec) ProbComp))

/-- The interface of a stateless signature scheme in the random-oracle experiment. Signing may fail, so it returns an option. -/
structure Scheme (Key : Type := Seeded.SecretKey) where
  keygen : OracleComp OracleWorld (PublicKey × Key)
  sign : Key → Message → OracleComp OracleWorld (Option Signature)
  verify : PublicKey → Message → Signature → OracleComp OracleWorld Bool

/-- A classical adaptive adversary. After receiving the public key, it may query the shared random oracle, request signatures, and finally return a claimed forgery. -/
structure Adversary where
  main : PublicKey → OracleComp (OracleWorld + SigningSpec) Forgery

/-- The signing oracle used in the game. It records every request and response while forwarding the request to the scheme's signer. -/
def signingOracle {Key : Type} (scheme : Scheme Key) (sk : Key) :
    QueryImpl SigningSpec (WriterT (QueryLog SigningSpec) (OracleComp OracleWorld)) :=
  QueryImpl.withLogging fun request => scheme.sign sk request

/-- Forward the shared random oracle and uniform sampling to the adversary unchanged, alongside the logged signing oracle. -/
def forwardOracles :
    QueryImpl OracleWorld (WriterT (QueryLog SigningSpec) (OracleComp OracleWorld)) :=
  fun input => liftM (OracleWorld.query input)

/-- The complete strong-unforgeability experiment.

The random oracle is sampled lazily by the semantics of `OracleWorld`. Key generation, the adversary, the signing oracle, and final verification all share the same oracle. The game returns `true` precisely when the transcript holds at most `q_s` signatures, the claimed forgery is not one the signer returned for that message, and the signature verifies. -/
noncomputable def gameCore {Key : Type} (scheme : Scheme Key) (adversary : Adversary) :
    OracleComp OracleWorld Bool := do
  let (pk, sk) ← scheme.keygen
  let ((forgery, log) : Forgery × QueryLog SigningSpec) ←
    (simulateQ (forwardOracles + signingOracle scheme sk) (adversary.main pk)).run
  let verified ← scheme.verify pk forgery.message forgery.signature
  return decide (SigningTranscript.Valid log ∧ ¬SigningTranscript.Contains log forgery) && verified

/-- The probability that the adversary wins, over key generation, the adversary, and the random oracle, which starts from the empty cache. The final cache is discarded. -/
noncomputable def forgeAdvantage {Key : Type} (scheme : Scheme Key) (adversary : Adversary) : ℝ≥0∞ :=
  Pr[= true | (simulateQ romImpl (gameCore scheme adversary)).run' ∅]

/-- Count one per hash call, including cache hits, and zero per uniform sample. -/
noncomputable def countedRomImpl :=
  romImpl.withAddCost (fun | .inl _ => (0 : Nat) | .inr _ => 1)

/-- Every execution of the consistent random oracle uses at most `q` hash calls, including key generation, adversarial hashing, signing, and final verification. -/
def HasHashQueryBound {Key : Type} (scheme : Scheme Key) (adversary : Adversary) (q : Nat) : Prop :=
  ∀ result ∈ support ((simulateQ countedRomImpl (gameCore scheme adversary)).run.run' ∅),
    result.2 ≤ q

/-- Having `bits` bits of classical security means that every classical adaptive adversary whose complete experiment stays within a nonzero hash-query budget `q` forges with probability at most `q / 2^bits`. The bound is a slope, so it bounds what a query buys and not what the first one does; a budget below what the honest experiment alone spends admits no adversary and the bound is vacuous there. -/
def HasClassicalSecurityBits {Key : Type} (scheme : Scheme Key) (bits : Nat) : Prop :=
  ∀ q, 1 ≤ q → ∀ adversary, HasHashQueryBound scheme adversary q →
    forgeAdvantage scheme adversary ≤ q / ((2 ^ bits : Nat) : ℝ≥0∞)

noncomputable def Seeded.scheme : Scheme Seeded.SecretKey where
  keygen := Seeded.keygen
  sign := fun sk message => liftM (Seeded.sign sk message : OracleComp HashSpec _)
  verify := fun publicKey message signature =>
    liftM (Concrete.verify publicKey message signature : OracleComp HashSpec Bool)

end SphincsSecurity
