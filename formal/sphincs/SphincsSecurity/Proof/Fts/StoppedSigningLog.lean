import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Ots.OtsProbeOrigin
namespace SphincsSecurity.Concrete.FtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal
set_option backward.isDefEq.respectTransparency false

def withSigningLog (computation : OracleComp (OracleWorld + SigningSpec) α) (log : QueryLog SigningSpec) :
    OracleComp (OracleWorld + SigningSpec) (α × QueryLog SigningSpec) :=
  (fun result => (result.1, log ++ result.2)) <$> signingTraceComputation computation

@[simp] theorem withSigningLog_pure (value : α) (log : QueryLog SigningSpec) :
    withSigningLog (pure value) log = pure (value, log) := by
  simp [withSigningLog, signingTraceComputation]

theorem withSigningLog_query_bind (input : (OracleWorld + SigningSpec).Domain)
    (next : (OracleWorld + SigningSpec).Range input → OracleComp (OracleWorld + SigningSpec) α) (log : QueryLog SigningSpec) :
    withSigningLog (OracleSpec.query input >>= next) log =
      (liftM (OracleSpec.query input) : OracleComp (OracleWorld + SigningSpec) _) >>= fun output =>
        withSigningLog (next output) (log ++ signingLogFragment input output) := by
  rw [withSigningLog, signingTraceComputation_query_bind, map_bind]
  apply bind_congr
  intro output
  simp only [withSigningLog, Functor.map_map, List.append_assoc]

end SphincsSecurity.Concrete.FtsProbeSimulation
