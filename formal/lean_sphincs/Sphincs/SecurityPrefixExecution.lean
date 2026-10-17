import Sphincs.SecurityPrefixSampling
import SphincsBase.Proof.Chains.AdaptiveChainCapTwoEdge
import SphincsBase.Proof.Chains.AdaptiveChainErasure

/-!
The oracle world for one hidden WOTS prefix (outside queries plus prefix queries), the predicates
that count source and split hash calls, and the fixed-function source world (`fixedHashWorld`:
fresh private draws and a supplied hash function).
-/

open OracleComp OracleSpec ENNReal

namespace Sphincs.Security.Prefix
open SphincsBase.Concrete.PartialChainEndpoint
set_option backward.isDefEq.respectTransparency false

abbrev World (segment : Segment) := OracleWorld + PrefixSpec segment.digit.val Digest

noncomputable local instance (segment : Segment) : IsUniformSpec (World segment) :=
  IsUniformSpec.ofFintypeInhabited _

/-- Source-side hash calls, excluding private uniform samples. -/
def SourceHash : OracleWorld.Domain → Prop
  | .inl _ => False
  | .inr _ => True

instance (input : OracleWorld.Domain) : Decidable (SourceHash input) := by
  cases input <;> unfold SourceHash <;> infer_instance

/-- Target-side hash calls count either the outside or the selected-prefix branch once. -/
def SplitHash (segment : Segment) : (World segment).Domain → Prop
  | .inl input => SourceHash input
  | .inr _ => True

instance (segment : Segment) (input : (World segment).Domain) : Decidable (SplitHash segment input) := by
  cases input <;> simp only [SplitHash] <;> infer_instance

/-- Fresh private uniform sampling together with a supplied fixed hash function. -/
noncomputable def fixedHashWorld (outside : QueryImpl HashSpec Id) : QueryImpl OracleWorld PMF
  | .inl _sample => PMF.uniformOfFintype _
  | .inr bytes => PMF.pure (outside bytes)

private theorem counted_query {ι : Type} {spec : OracleSpec ι}
    (selected : ι → Prop) [DecidablePred selected] (input : ι) :
    SphincsBase.QueryCap.counted selected (liftM (spec.query input) : OracleComp spec (spec.Range input)) =
      (do let value ← liftM (spec.query input); pure (value, if selected input then 1 else 0)) := rfl

end Sphincs.Security.Prefix
