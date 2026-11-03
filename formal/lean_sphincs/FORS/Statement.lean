import FORS.Scheme
import VCVio.OracleComp.QueryTracking.WriterCost

/-!
# The security statement

The SUF-CMA game of the security target, adapted from leanVM b7a107256 to pruning: forgeries,
signing transcripts and their tests, adversaries, and the counted experiment with the deterministic
signer `Seeded.sign` (`Scheme.lean`; the Rust signer's, with FORS in place of the forest), whose randomizers are derived from the master
seed and the message (a repeated request returns the same signature). Every hash call counts,
including repeated calls and the calls of the honest parties. The module ends with the forgery
advantage, the hash-query budget and the security-bits target `SecurityBits P bits`; `Main.lean`
spells out `SecurityBits P 127` as `Secure127 P` and states it for each configuration `P`.
-/

open OracleComp OracleSpec ENNReal

namespace FORS

variable [Params]

/-- A forgery: a message and a signature. -/
structure Forgery where
  message : Message
  signature : Signature
deriving DecidableEq

/-- The signing oracle: a message, answered by a signature or `none` (the signer failed). -/
abbrev SigningSpec := Message →ₒ Option Signature

namespace SigningTranscript

/-- The adversary asked for at most `signatureLimit` signatures. -/
def Valid (log : QueryLog SigningSpec) : Prop := log.length ≤ signatureLimit

instance (log : QueryLog SigningSpec) : Decidable (Valid log) :=
  inferInstanceAs (Decidable (log.length ≤ signatureLimit))

/-- The transcript holds the forgery: its message, answered with its signature (strong
unforgeability: a new signature of a signed message is a forgery). -/
def Contains (log : QueryLog SigningSpec) (forgery : Forgery) : Prop :=
  ∃ entry ∈ log, entry.1 = forgery.message ∧ entry.2 = some forgery.signature

instance (log : QueryLog SigningSpec) (forgery : Forgery) : Decidable (Contains log forgery) :=
  inferInstanceAs
    (Decidable (∃ entry ∈ log, entry.1 = forgery.message ∧ entry.2 = some forgery.signature))

end SigningTranscript

namespace Security

/-- An adversary: from the public key, a computation with uniform randomness, the hash (random
oracle) and the signing oracle, which outputs a forgery. -/
structure Adversary where
  main : PublicKey → OracleComp (OracleWorld + SigningSpec) Forgery

/-- The random oracle, a lazily sampled cache of uniform 32-byte answers, with a cost of one per hash
query (repeated queries included); uniform randomness is free. -/
noncomputable def countedOracle :=
  (unifFwdImpl HashSpec + (randomOracle : QueryImpl HashSpec (StateT (QueryCache HashSpec) ProbComp))).withAddCost
    (fun | .inl _ => (0 : Nat) | .inr _ => 1)

/-- The signing oracle: `Seeded.sign` with the secret key, logging every request and answer. -/
noncomputable def signingOracle (sk : Seeded.SecretKey) :
    QueryImpl SigningSpec (WriterT (QueryLog SigningSpec) (OracleComp OracleWorld)) :=
  QueryImpl.withLogging fun request =>
    liftM (Seeded.sign sk request : OracleComp HashSpec (Option Signature))

/-- The game: a uniform master seed, key generation, the adversary with the signing oracle, and the
verification of its forgery. It wins when the forgery verifies, the adversary asked for at most
`signatureLimit` signatures, and no signing answer was the forgery. -/
noncomputable def gameCore (adversary : Adversary) : OracleComp OracleWorld Bool := do
  let seed ← liftM sampleMasterSeed
  let (pk, sk) ← liftM (Seeded.keygenFromSeed seed)
  let ((forgery, log) : Forgery × QueryLog SigningSpec) ←
    (simulateQ (QueryImpl.ofLift OracleWorld
      (WriterT (QueryLog SigningSpec) (OracleComp OracleWorld)) + signingOracle sk)
      (adversary.main pk)).run
  let verified ← liftM (Concrete.verify pk forgery.message forgery.signature : OracleComp HashSpec Bool)
  return decide (SigningTranscript.Valid log ∧ ¬SigningTranscript.Contains log forgery) && verified

/-- The game under the counted random oracle, from an empty cache: whether the adversary won, and
the number of hash queries of the whole run (key generation, signing and verification included). -/
noncomputable def experiment (adversary : Adversary) : ProbComp (Bool × Nat) :=
  (simulateQ countedOracle (gameCore adversary)).run.run' ∅

/-- The probability that the adversary wins. -/
noncomputable def forgeAdvantage (adversary : Adversary) : ℝ≥0∞ :=
  Pr[fun result => result.1 = true | experiment adversary]

/-- Every run of the experiment makes at most `q` hash queries. -/
def HasHashQueryBound (adversary : Adversary) (q : Nat) : Prop :=
  ∀ result ∈ support (experiment adversary), result.2 ≤ q

/-- `bits` bits of classical security: an adversary whose runs make at most `q ≥ 1` hash queries
wins with probability at most `q / 2^bits`. -/
def HasClassicalSecurityBits (bits : Nat) : Prop :=
  ∀ q, 1 ≤ q → ∀ adversary, HasHashQueryBound adversary q →
    forgeAdvantage adversary ≤ q / ((2 ^ bits : Nat) : ℝ≥0∞)

end Security

/-- **The security target**: the scheme with parameters `P` has `bits` bits of classical security,
`HasClassicalSecurityBits` of the instance `P`. -/
abbrev SecurityBits (P : Params) (bits : Nat) : Prop := @Security.HasClassicalSecurityBits P bits

end FORS
