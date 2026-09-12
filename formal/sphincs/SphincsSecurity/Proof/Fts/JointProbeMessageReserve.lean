import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Statement

namespace SphincsSecurity.Concrete.FtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

def MessageHashInput (parameter : PublicParameter) (input : HashInput) : Prop :=
  ∃ payload, tweakableHashInput parameter .message payload = input

end SphincsSecurity.Concrete.FtsProbeSimulation
