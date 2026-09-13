import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Fts.CacheMessageWeight
namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
open FtsProbeSimulation (MessageHashInput)
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

noncomputable def cachedIndexMultiplicity (parameter : PublicParameter) (cache : QueryCache HashSpec) (index : Index) : ENNReal :=
  cacheMessageWeight parameter (fun _ source => if source.1 = index then 1 else 0) cache

theorem cachedIndexMultiplicity_cacheQuery (parameter : PublicParameter) (cache : QueryCache HashSpec)
    (input : HashInput) (output : HashOutput) (hfresh : cache input = none) (index : Index) :
    cachedIndexMultiplicity parameter (cache.cacheQuery input output) index = cachedIndexMultiplicity parameter cache index +
      (if MessageHashInput parameter input ∧ Admissible (truncateMessageDigest output) ∧ (hashOutputFewTimeView output).1 = index then 1 else 0) := by
  rw [cachedIndexMultiplicity, cacheMessageWeight_cacheQuery parameter _ cache input output hfresh]
  simp only [← ite_and, and_assoc]
  rfl

end SphincsSecurity.Concrete
