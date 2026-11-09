module

public import FORS.Scheme
public import VCVio.OracleComp.QueryTracking.WriterCost

@[expose] public section

/-!
# The security statement

The SUF-CMA game of the security target: forgeries, signing transcripts and their tests,
adversaries, and the counted experiment. The secret key is a uniform 32-byte `SK.seed`
(`Seeded.keygen`), from which key generation derives `PK.seed` and `SK.prf` (two hashes of
`leanSPHINCS || SK.seed || d`, for `d = 0, 1`) and every secret (one `PRF` call each). The signer is
the deterministic `Seeded.sign` (`Scheme.lean`; the Rust signer's), whose randomizers are derived
from `SK.prf`, `PK.seed` and the message (a repeated request returns the same signature). Every hash
call counts, including repeated calls and the calls of the honest parties, the two that derive
`PK.seed` and `SK.prf` among them. The module ends with the forgery advantage; the security target,
which charges only the adversary's own hash queries (`Security.AdvCount.AdvHash`), is `Secure127` of
`Main.lean`.
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

/-- The game: a uniform `SK.seed`, key generation from it, the adversary with the signing oracle, and
the verification of its forgery. It wins when the forgery verifies, the adversary asked for at most
`signatureLimit` signatures, and no signing answer was the forgery. -/
noncomputable def gameCore (adversary : Adversary) : OracleComp OracleWorld Bool := do
  let seed ← liftM sampleMasterSeed
  let (pk, sk) ← liftM (Seeded.keygen seed)
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
  Pr{let result ← experiment adversary}[result.1 = true]

end Security

end FORS
