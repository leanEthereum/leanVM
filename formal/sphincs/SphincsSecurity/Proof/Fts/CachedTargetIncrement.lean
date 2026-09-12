import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Fts.ObservedOccupancy
namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
open FtsProbeSimulation (messageAnswers)
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

theorem eligibleSigningViews_fresh_eq_observed (parameter : PublicParameter) (root : Digest)
    (before : QueryCache HashSpec) (log : QueryLog SigningSpec) (payload : HashInput)
    (hfresh : before (tweakableHashInput parameter .message payload) = none)
    (hsigned : SigningDigestsCached parameter before root log) :
    eligibleSigningViews (messageAnswers parameter before) root payload log =
      observedOptionalSigningViews (messageAnswers parameter before) root log := by
  funext slot
  simp only [eligibleSigningViews, observedOptionalSigningViews]
  cases hresponse : (log.get slot).2 with
  | none =>
      change Option.bind (log.get slot).2 _ = Option.bind (log.get slot).2 _
      rw [hresponse]
      rfl
  | some signature =>
      have hne : messageDigestPayload root (log.get slot).1 signature.randomness ≠ payload := by
        intro heq
        have hcached := hsigned (log.get slot) (List.get_mem _ _) signature hresponse
        apply hcached
        change before (tweakableHashInput parameter .message (messageDigestPayload root (log.get slot).1 signature.randomness)) = none
        rwa [heq]
      unfold eligibleSigningView?
      rw [hresponse]
      change (if messageDigestPayload root (log.get slot).1 signature.randomness = payload then none else _) = _
      rw [if_neg hne]

end SphincsSecurity.Concrete
