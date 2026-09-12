import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Statement

namespace SphincsSecurity.Concrete.FtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal

noncomputable def messageAnswers (parameter : PublicParameter) (cache : QueryCache HashSpec) : HashInput → Option HashOutput :=
  fun payload => cache (tweakableHashInput parameter .message payload)

end SphincsSecurity.Concrete.FtsProbeSimulation
