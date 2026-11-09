module

public import LeanXmss.Scheme
public import VCVio.OracleComp.QueryTracking.WriterCost
public import Statement.LeanXmss
public import Common.WithHash

/-!
# leanXMSS security statement

Strong unforgeability under chosen-message attacks (SUF-CMA) in the classical random-oracle model,
with a 127-bit target, for the scheme of `Scheme.lean`. The adversary picks each request's leaf index
and may not reuse one: the scheme is stateful.
-/

open OracleComp OracleSpec ENNReal

namespace LeanXmss

open HashSig

@[expose] public section

namespace Security

/-- A probabilistic adaptive adversary with private randomness and access to hashing and signing. -/
structure Adversary where
  main : PublicKey → OracleComp (OracleWorld + SigningOracleSpec) Forgery

/-- Record each signing request and its answer. -/
def signingOracle (sk : LeanXmss.SchemeSeedKey) :
    QueryImpl SigningOracleSpec (WriterT (QueryLog SigningOracleSpec) (OracleComp OracleWorld)) :=
  QueryImpl.withLogging fun request =>
    liftM (KeyGenerationAndSigning.signWithHash sk request.leafIndex request.message : OracleComp
        HashSpec _)

/-- Sample the master seed, then run all parties with one shared hash oracle. -/
noncomputable def gameCore (adversary : Adversary) : OracleComp OracleWorld Bool := do
  let seed ← liftM sampleMasterSeed
  let (pk, sk) ← liftM (KeyGenerationAndSigning.keygenFromSeedWithHash seed)
  let ((forgery, log) : Forgery × QueryLog SigningOracleSpec) ←
    (simulateQ (QueryImpl.ofLift OracleWorld (WriterT (QueryLog SigningOracleSpec) (OracleComp OracleWorld)) +
      signingOracle sk) (adversary.main pk)).run
  let verified ← liftM (Verification.verifyWithHash pk forgery.message forgery.signature : OracleComp HashSpec Bool)
  return decide (SigningTranscript.NoLeafIndexReused log ∧ ¬SigningTranscript.Contains log forgery)
      && verified

/-- Forward private sampling for free; answer hash queries consistently and count every call,
including cache hits. -/
noncomputable def countedOracle :=
  (unifFwdImpl HashSpec + (randomOracle : QueryImpl HashSpec (StateT (QueryCache HashSpec) ProbComp))).withAddCost
    (fun | .inl _ => (0 : Nat) | .inr _ => 1)

/-- Run the game from an empty random-oracle cache, recording success and the total number of hash
calls. -/
noncomputable def experiment (adversary : Adversary) : ProbComp (Bool × Nat) :=
  (simulateQ countedOracle (gameCore adversary)).run.run' ∅

/-- The probability of a successful forgery. -/
noncomputable def forgeAdvantage (adversary : Adversary) : ℝ≥0∞ :=
  Pr{let result ← experiment adversary}[result.1 = true]

/-- Every execution uses at most `q` hash calls, including key generation, signing and verification. -/
def HasHashQueryBound (adversary : Adversary) (q : Nat) : Prop :=
  ∀ result ∈ support (experiment adversary), result.2 ≤ q

/-- The adversary's own hash calls: at most `q` on every path. The signing oracle's calls, key
generation's and the final verification's are not the adversary's. -/
def AdversaryHashQueryBound (adversary : Adversary) (q : Nat) : Prop :=
  ∀ pk, IsQueryBoundP (adversary.main pk) (fun input => input matches .inl (.inr _)) q

/-- At most `s` signing requests on every path. -/
def SigningRequestBound (adversary : Adversary) (s : Nat) : Prop :=
  ∀ pk, IsQueryBoundP (adversary.main pk) (fun input => input matches .inr _) s

end Security

end

end LeanXmss
