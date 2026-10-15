import SphincsFors.Randomized

/-! The uncounted shared random-oracle interpreter used for honest completeness. -/

open OracleComp OracleSpec

namespace SphincsFors.Completeness

noncomputable def romImpl : QueryImpl OracleWorld (StateT (QueryCache HashSpec) ProbComp) :=
  unifFwdImpl HashSpec + (randomOracle : QueryImpl HashSpec (StateT (QueryCache HashSpec) ProbComp))

theorem simulate_lift_hash {α : Type} (oa : OracleComp HashSpec α) :
    simulateQ romImpl (liftM oa : OracleComp OracleWorld α) = simulateQ randomOracle oa :=
  QueryImpl.simulateQ_add_liftM_right _ _ oa

theorem run_lift_prob {α : Type} (oa : ProbComp α) (cache : QueryCache HashSpec) :
    (simulateQ romImpl (liftM oa : OracleComp OracleWorld α)).run cache =
      (fun x => (x, cache)) <$> oa :=
  roSim.run_liftM _ oa cache

end SphincsFors.Completeness
