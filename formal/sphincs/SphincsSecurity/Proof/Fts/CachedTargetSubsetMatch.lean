import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Fts.CacheMessageWeight
import SphincsSecurity.Proof.Fts.SubsetTargetAssignment
namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

noncomputable def cachedTargetSubsetMatch (parameter : PublicParameter) (cache : QueryCache HashSpec)
    (targetInput : HashInput) (target : FewTimeView) (required : Finset FtsTree) : ENNReal :=
  cacheMessageWeight parameter (fun input source =>
    if input = targetInput then 0 else (sourceSubsetMatch target source required : ENNReal)) cache

theorem cachedTargetSubsetMatch_cacheQuery (parameter : PublicParameter) (before : QueryCache HashSpec)
    (targetInput : HashInput) (target : FewTimeView) (required : Finset FtsTree) (input : HashInput) (output : HashOutput)
    (hfresh : before input = none) :
    cachedTargetSubsetMatch parameter (before.cacheQuery input output) targetInput target required =
      cachedTargetSubsetMatch parameter before targetInput target required +
        if FtsProbeSimulation.MessageHashInput parameter input ∧ Admissible (truncateMessageDigest output) then
          if input = targetInput then 0 else (sourceSubsetMatch target (hashOutputFewTimeView output) required : ENNReal) else 0 := by
  exact cacheMessageWeight_cacheQuery parameter _ before input output hfresh

theorem cachedTargetSubsetMatch_cacheQuery_self (parameter : PublicParameter) (before : QueryCache HashSpec)
    (targetInput : HashInput) (target : FewTimeView) (required : Finset FtsTree) (output : HashOutput)
    (hfresh : before targetInput = none) :
    cachedTargetSubsetMatch parameter (before.cacheQuery targetInput output) targetInput target required =
      cachedTargetSubsetMatch parameter before targetInput target required := by
  rw [cachedTargetSubsetMatch_cacheQuery parameter before targetInput target required targetInput output hfresh]
  simp only [if_true, ite_self, add_zero]

end SphincsSecurity.Concrete
