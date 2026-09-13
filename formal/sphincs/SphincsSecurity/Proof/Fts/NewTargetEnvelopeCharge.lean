import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Fts.ConcreteTargetShapeSigning
import SphincsSecurity.Proof.Fts.TargetShapeEnvelope
namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
open FtsProbeSimulation (MessageHashInput)
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

noncomputable def newTargetEnvelopeCharge (key : SecretKey) (before after : QueryCache HashSpec)
    (log : QueryLog SigningSpec) (uniform reuse arrival : ENNReal) (queries signings : Nat)
    (groups : Finset (Finset FtsTree)) (remaining : Finset FtsTree) : ENNReal :=
  cacheMessageWeight key.parameter (fun input target => if before input = none then
    targetShapeEnvelope uniform reuse arrival queries signings (targetShapeMoments key after log (payloadOf input) target) groups remaining else 0) after

theorem newTargetEnvelopeCharge_of_no_new (key : SecretKey) (before after : QueryCache HashSpec)
    (log : QueryLog SigningSpec) (uniform reuse arrival : ENNReal) (queries signings : Nat)
    (groups : Finset (Finset FtsTree)) (remaining : Finset FtsTree)
    (hnone : ∀ payload output, before (tweakableHashInput key.parameter .message payload) = none →
      after (tweakableHashInput key.parameter .message payload) = some output → ¬ Admissible (truncateMessageDigest output)) :
    newTargetEnvelopeCharge key before after log uniform reuse arrival queries signings groups remaining = 0 := by
  apply ENNReal.tsum_eq_zero.mpr
  intro input
  unfold cacheMessageEntryWeight
  cases houtput : after input with
  | none => rfl
  | some output =>
      simp only
      split_ifs with hgood hfresh
      · obtain ⟨payload, rfl⟩ := hgood.1
        exact (hnone payload output hfresh houtput hgood.2).elim
      · rfl
      · rfl

end SphincsSecurity.Concrete
