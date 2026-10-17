import XmssSecurity.Scheme
import VCVio.OracleComp.QueryTracking.WriterCost

/-!
# XMSS security statement

Strong unforgeability under chosen-message attacks (SUF-CMA) in the classical random-oracle model, with a 127-bit security target for the scheme in `Scheme.lean`.
-/

open OracleComp OracleSpec ENNReal

namespace XmssSecurity

/-! ## The security experiment -/

/-- A signing request contains a 32-bit leaf index and a 32-byte message. -/
structure SignRequest where
  leafIndex : LeafIndex
  message : Message
deriving DecidableEq

/-- A claimed forgery: a leaf index, a message, and a signature. -/
structure Forgery where
  leafIndex : LeafIndex
  message : Message
  signature : Signature
deriving DecidableEq

/-- The request a forgery claims to answer. -/
def Forgery.request (forgery : Forgery) : SignRequest :=
  ⟨forgery.leafIndex, forgery.message⟩

/-- The signing oracle answers a request with either a signature or `none` if the signer fails. -/
abbrev SigningSpec := SignRequest →ₒ Option Signature

namespace SigningTranscript

/-- A signing transcript is valid exactly when no leaf index occurs twice. Thus the adversary may make adaptive signing requests, but may not request two signatures at the same leaf index. -/
def Valid (log : QueryLog SigningSpec) : Prop :=
  (log.map fun entry => entry.1.leafIndex).Nodup

instance (log : QueryLog SigningSpec) : Decidable (Valid log) :=
  inferInstanceAs (Decidable ((log.map fun entry => entry.1.leafIndex).Nodup))

/-- The signer returned the claimed forgery exactly when the transcript contains the same leaf index, message, and signature. A different signature for a signed message is therefore a valid strong forgery. -/
def Contains (log : QueryLog SigningSpec) (forgery : Forgery) : Prop :=
  ∃ entry ∈ log, entry.1 = forgery.request ∧ entry.2 = some forgery.signature

instance (log : QueryLog SigningSpec) (forgery : Forgery) : Decidable (Contains log forgery) :=
  inferInstanceAs
    (Decidable (∃ entry ∈ log, entry.1 = forgery.request ∧ entry.2 = some forgery.signature))

end SigningTranscript

namespace Security

/-- A probabilistic adaptive adversary with private randomness and access to hashing and signing. -/
structure Adversary where
  main : PublicKey → OracleComp (OracleWorld + SigningSpec) Forgery

/-- Record each signing request and its answer. -/
def signingOracle (sk : Seeded.SecretKey) :
    QueryImpl SigningSpec (WriterT (QueryLog SigningSpec) (OracleComp OracleWorld)) :=
  QueryImpl.withLogging fun request => liftM (Seeded.sign sk request.leafIndex request.message : OracleComp HashSpec _)

/-- Sample the master seed, then run all parties with one shared hash oracle. -/
noncomputable def gameCore (adversary : Adversary) : OracleComp OracleWorld Bool := do
  let seed ← liftM sampleMasterSeed
  let (pk, sk) ← liftM (Seeded.keygenFromSeed seed)
  let ((forgery, log) : Forgery × QueryLog SigningSpec) ←
    (simulateQ (QueryImpl.ofLift OracleWorld (WriterT (QueryLog SigningSpec) (OracleComp OracleWorld)) + signingOracle sk) (adversary.main pk)).run
  let verified ← liftM (Concrete.verify pk forgery.leafIndex forgery.message forgery.signature : OracleComp HashSpec Bool)
  return decide (SigningTranscript.Valid log ∧ ¬SigningTranscript.Contains log forgery) && verified

/-- Forward private sampling for free; answer hash queries consistently and count every call, including cache hits. -/
noncomputable def countedOracle :=
  (unifFwdImpl HashSpec + (randomOracle : QueryImpl HashSpec (StateT (QueryCache HashSpec) ProbComp))).withAddCost
    (fun | .inl _ => (0 : Nat) | .inr _ => 1)

/-- Run the game from an empty random-oracle cache, recording success and the total number of hash calls. -/
noncomputable def experiment (adversary : Adversary) : ProbComp (Bool × Nat) :=
  (simulateQ countedOracle (gameCore adversary)).run.run' ∅

/-- The probability of a successful forgery. -/
noncomputable def forgeAdvantage (adversary : Adversary) : ℝ≥0∞ :=
  Pr[fun result => result.1 = true | experiment adversary]

/-- Every execution uses at most `q` hash calls, including key generation, signing, and verification. -/
def HasHashQueryBound (adversary : Adversary) (q : Nat) : Prop :=
  ∀ result ∈ support (experiment adversary), result.2 ≤ q

/-- Every adversary with nonzero query budget `q` wins with probability at most `q / 2^bits`. -/
def HasClassicalSecurityBits (bits : Nat) : Prop :=
  ∀ q, 1 ≤ q → ∀ adversary, HasHashQueryBound adversary q →
    forgeAdvantage adversary ≤ q / ((2 ^ bits : Nat) : ℝ≥0∞)

end Security

/-- The security claim. -/
abbrev XmssSecurityStatement : Prop := Security.HasClassicalSecurityBits 127

end XmssSecurity
