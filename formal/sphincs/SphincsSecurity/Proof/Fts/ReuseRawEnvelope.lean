import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Fts.TargetShapeEnvelope
import SphincsSecurity.Proof.Fts.FreshTargetShapeAverage
import SphincsSecurity.Proof.Fts.InterleavedCoverStep
import SphincsSecurity.Proof.Fts.TargetShapeCardinality

/-! ## WorldRawIndexEnvelope -/

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
set_option backward.isDefEq.respectTransparency false

noncomputable def observedRawIndexShapeVector (key : SecretKey) (state : CoverLogState) : TargetShapeVector :=
  liftTargetIndexVector (targetIndexMoments key state.1 state.2)

end SphincsSecurity.Concrete

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable

noncomputable def reuseRawEnvelope (key : SecretKey) (reuse : ENNReal) (queries signatures : Nat)
    (state : CoverLogState) : TargetShapeVector :=
  targetShapeEnvelope (Fintype.card Index : ENNReal)⁻¹ reuse
    (((2 ^ ftsTreeHeight : Nat) : ENNReal)⁻¹ * (Fintype.card Index : ENNReal)⁻¹) queries signatures
    (observedRawIndexShapeVector key state)

end SphincsSecurity.Concrete
