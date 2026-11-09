module

public import XmssSecurity.Scheme
public import VCVio.OracleComp.QueryTracking.WriterCost

@[expose] public section

/-!
# The model's signing requests and forgeries

The requests, forgeries and signing transcripts of the model's SUF-CMA game (`Proof/RandomizedStatement.lean`) for the scheme in `Scheme.lean`.
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

end XmssSecurity
