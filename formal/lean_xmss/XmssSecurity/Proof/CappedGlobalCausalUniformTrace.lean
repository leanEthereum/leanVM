import XmssSecurity.Proof.CappedGlobalCausalSetup
import XmssSecurity.Proof.RevealProbeOracleSimulation

open OracleComp OracleSpec

namespace XmssSecurity.CappedChain

theorem simulate_eagerTrace_globalCausalUniformImpl
    (table : GlobalChainValueIndex → Digest) (n : Nat)
    (state : GlobalCausalHashState) :
    (simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
      ((globalCausalUniformImpl n).run state)).run =
      (fun output => ((output, state),
        ([] : RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex))) <$>
          (liftM (unifSpec.query n) : ProbComp (Fin (n + 1))) := by
  unfold globalCausalUniformImpl
  rw [OracleComp.liftM_run_StateT, simulateQ_bind]
  simp [RevealProbeOracleSimulation.uniformQuery,
    RevealProbeOracleSimulation.eagerTraceImpl,
    RevealProbeOracleSimulation.eagerImpl,
    RevealProbeOracleSimulation.traceFragment,
    QueryImpl.withTraceAppend_apply, WriterT.run_tell,
    map_eq_bind_pure_comp]

end XmssSecurity.CappedChain
