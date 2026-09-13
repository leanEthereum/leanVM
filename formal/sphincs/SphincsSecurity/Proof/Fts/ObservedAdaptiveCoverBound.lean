import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Fts.JointProbeMessageAnswers
import SphincsSecurity.Proof.Fts.ObservedFreshCoverBound
namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
open FtsProbeSimulation (messageAnswers)
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

noncomputable def fixedSigningViews (parameter : PublicParameter) (cache : QueryCache HashSpec)
    (root : Digest) (log : QueryLog SigningSpec) (input : HashInput) : Fin log.length → Option FewTimeView :=
  eligibleSigningViews (messageAnswers parameter cache) root (payloadOf input) log

def SigningDigestsCached (parameter : PublicParameter) (cache : QueryCache HashSpec)
    (root : Digest) (log : QueryLog SigningSpec) : Prop :=
  ∀ entry ∈ log, ∀ signature, entry.2 = some signature →
    messageAnswers parameter cache (messageDigestPayload root entry.1 signature.randomness) ≠ none

end SphincsSecurity.Concrete
