import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Fts.FewTimeUniform

/-! ## ObservedCoverPattern -/

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

def observedSigningView? (answers : HashInput → Option HashOutput) (root : Digest) (entry : SigningEntry) : Option FewTimeView := do
  let signature ← entry.2
  let answer ← answers (messageDigestPayload root entry.1 signature.randomness)
  pure (hashOutputFewTimeView answer)

end SphincsSecurity.Concrete

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

noncomputable def eligibleSigningView? (answers : HashInput → Option HashOutput) (root : Digest)
    (targetPayload : HashInput) (entry : SigningEntry) : Option FewTimeView := do
  let signature ← entry.2
  if messageDigestPayload root entry.1 signature.randomness = targetPayload then none
  else observedSigningView? answers root entry

noncomputable def eligibleSigningViews (answers : HashInput → Option HashOutput) (root : Digest)
    (targetPayload : HashInput) (log : QueryLog SigningSpec) : Fin log.length → Option FewTimeView :=
  fun slot => eligibleSigningView? answers root targetPayload (log.get slot)

end SphincsSecurity.Concrete
