import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Fts.FtsProbeAdversary
namespace SphincsSecurity.AdaptiveRevealProbe

open OracleComp OracleSpec

variable {Coordinate : Type} [Fintype Coordinate] [DecidableEq Coordinate]

end SphincsSecurity.AdaptiveRevealProbe

namespace SphincsSecurity.Concrete.FtsProbeSimulation

open OracleComp OracleSpec

theorem signingTraceComputation_query_bind
    (input : (OracleWorld + SigningSpec).Domain)
    (next : (OracleWorld + SigningSpec).Range input →
      OracleComp (OracleWorld + SigningSpec) alpha) :
    signingTraceComputation
        ((liftM ((OracleWorld + SigningSpec).query input) :
          OracleComp (OracleWorld + SigningSpec) _) >>= next) = (do
      let output ← liftM ((OracleWorld + SigningSpec).query input)
      (fun result => (result.1, signingLogFragment input output ++ result.2)) <$>
        signingTraceComputation (next output)) := by
  simp [signingTraceComputation]

end SphincsSecurity.Concrete.FtsProbeSimulation
