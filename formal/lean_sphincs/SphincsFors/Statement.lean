import SphincsFors.Randomized
import VCVio.OracleComp.QueryTracking.WriterCost

/-!
The SUF-CMA experiment, adapted from leanVM b7a107256 to pruning: forgeries, signing transcripts and
their tests, adversaries, and the counted experiment with the randomized signer (genuinely random
randomizers). All hash calls in the experiment count, including repeated calls and honest-party
calls. The security target, for the deterministic signer, is in `StatementDet`.
-/

open OracleComp OracleSpec ENNReal

namespace SphincsFors

structure Forgery where
  message : Message
  signature : Signature
deriving DecidableEq

abbrev SigningSpec := Message →ₒ Option Signature

variable [Params]

namespace SigningTranscript

def Valid (log : QueryLog SigningSpec) : Prop := log.length ≤ signatureLimit

instance (log : QueryLog SigningSpec) : Decidable (Valid log) :=
  inferInstanceAs (Decidable (log.length ≤ signatureLimit))

def Contains (log : QueryLog SigningSpec) (forgery : Forgery) : Prop :=
  ∃ entry ∈ log, entry.1 = forgery.message ∧ entry.2 = some forgery.signature

instance (log : QueryLog SigningSpec) (forgery : Forgery) : Decidable (Contains log forgery) :=
  inferInstanceAs
    (Decidable (∃ entry ∈ log, entry.1 = forgery.message ∧ entry.2 = some forgery.signature))

end SigningTranscript

namespace Security

structure Adversary where
  main : PublicKey → OracleComp (OracleWorld + SigningSpec) Forgery

noncomputable def signingOracle (sk : Seeded.SecretKey) :
    QueryImpl SigningSpec (WriterT (QueryLog SigningSpec) (OracleComp OracleWorld)) :=
  QueryImpl.withLogging fun request => liftM (Randomized.sign sk request)

noncomputable def gameCore (adversary : Adversary) : OracleComp OracleWorld Bool := do
  let seed ← liftM sampleMasterSeed
  let (pk, sk) ← liftM (Seeded.keygenFromSeed seed)
  let ((forgery, log) : Forgery × QueryLog SigningSpec) ←
    (simulateQ (QueryImpl.ofLift OracleWorld
      (WriterT (QueryLog SigningSpec) (OracleComp OracleWorld)) + signingOracle sk)
      (adversary.main pk)).run
  let verified ← liftM (Concrete.verify pk forgery.message forgery.signature : OracleComp HashSpec Bool)
  return decide (SigningTranscript.Valid log ∧ ¬SigningTranscript.Contains log forgery) && verified

noncomputable def countedOracle :=
  (unifFwdImpl HashSpec + (randomOracle : QueryImpl HashSpec (StateT (QueryCache HashSpec) ProbComp))).withAddCost
    (fun | .inl _ => (0 : Nat) | .inr _ => 1)

noncomputable def experiment (adversary : Adversary) : ProbComp (Bool × Nat) :=
  (simulateQ countedOracle (gameCore adversary)).run.run' ∅

end Security

end SphincsFors
