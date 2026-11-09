module

public import XmssSecurity.Statement

@[expose] public section

open OracleComp OracleSpec ENNReal

namespace XmssSecurity

namespace Concrete

abbrev digestBytes (value : Digest) : HashInput := bytesLE 16 value

abbrev messageBytes (message : Message) : HashInput := bytesLE 32 message

abbrev randomnessBytes (randomness : Randomness) : HashInput := bytesLE 16 randomness

end Concrete

/-- The random-oracle semantics: hash queries are answered lazily and consistently by uniform sampling and cached; uniform-sampling queries are forwarded unchanged. -/
noncomputable def romImpl : QueryImpl OracleWorld (StateT (QueryCache HashSpec) ProbComp) :=
  unifFwdImpl HashSpec +
    (randomOracle : QueryImpl HashSpec (StateT (QueryCache HashSpec) ProbComp))

/-- The interface of a synchronized signature scheme in the random-oracle experiment. -/
structure Scheme (Key : Type := Seeded.SecretKey) where
  keygen : OracleComp OracleWorld (PublicKey × Key)
  sign : Key → LeafIndex → Message → OracleComp OracleWorld (Option Signature)
  verify : PublicKey → LeafIndex → Message → Signature → OracleComp OracleWorld Bool

/-- A classical adaptive adversary. After receiving the public key, it may query the shared random oracle, request signatures, and finally return a claimed forgery. -/
structure Adversary where
  main : PublicKey → OracleComp (OracleWorld + SigningSpec) Forgery

/-- The signing oracle used in the game. It records every request and response while forwarding the request to the scheme's signer. -/
def signingOracle {Key : Type} (scheme : Scheme Key) (sk : Key) :
    QueryImpl SigningSpec (WriterT (QueryLog SigningSpec) (OracleComp OracleWorld)) :=
  QueryImpl.withLogging fun request => scheme.sign sk request.leafIndex request.message

/-- Forward the shared random oracle and uniform sampling to the adversary unchanged, alongside the logged signing oracle. -/
def forwardOracles :
    QueryImpl OracleWorld (WriterT (QueryLog SigningSpec) (OracleComp OracleWorld)) :=
  fun input => liftM (OracleWorld.query input)

noncomputable def Seeded.gameRest {Key : Type} (randomizedScheme : Scheme Key) (adversary : Adversary)
    (pk : PublicKey) (sk : Key) : OracleComp OracleWorld Bool := do
  let ((forgery, log) : Forgery × QueryLog SigningSpec) ←
    (simulateQ (forwardOracles + signingOracle randomizedScheme sk) (adversary.main pk)).run
  let verified ← randomizedScheme.verify pk forgery.leafIndex forgery.message forgery.signature
  return decide (SigningTranscript.Valid log ∧ ¬SigningTranscript.Contains log forgery) && verified

/-- Key generation, followed by the adversary and final verification. -/
noncomputable def gameCore {Key : Type} (scheme : Scheme Key) (adversary : Adversary) :
    OracleComp OracleWorld Bool := do
  let (pk, sk) ← scheme.keygen
  Seeded.gameRest scheme adversary pk sk

/-- Success probability from an empty random-oracle cache. -/
noncomputable def forgeAdvantage {Key : Type} (scheme : Scheme Key) (adversary : Adversary) : ℝ≥0∞ :=
  Pr{let x ← (simulateQ romImpl (gameCore scheme adversary)).run' ∅}[x = true]

/-- Count one per hash call, including cache hits, and zero per uniform sample. -/
noncomputable def countedRomImpl :=
  romImpl.withAddCost (fun | .inl _ => (0 : Nat) | .inr _ => 1)

end XmssSecurity
