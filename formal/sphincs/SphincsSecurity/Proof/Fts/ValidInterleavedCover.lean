import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Fts.InterleavedCoverStep
namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
open FtsProbeSimulation (messageAnswers)
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

def ValidSigningStep (log : QueryLog SigningSpec) : (OracleWorld + SigningSpec).Domain → Prop
  | .inl _ => log.length ≤ signatureLimit
  | .inr _ => log.length < signatureLimit
