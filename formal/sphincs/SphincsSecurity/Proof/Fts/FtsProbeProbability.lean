import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Fts.FtsProbeAdversary
namespace SphincsSecurity.Concrete.FtsProbeSimulation

open OracleComp OracleSpec
open OracleComp.ProgramLogic.Relational

theorem simulateQ_expanded_liftOracleWorldLeft
    (secretKey : SecretKey) (computation : OracleComp OracleWorld alpha) :
    simulateQ (expandedAdversaryImpl secretKey)
        (liftOracleWorldLeft computation) = computation := by
  have hhandler : expandedAdversaryImpl secretKey =
      QueryImpl.id' OracleWorld +
        (fun request => scheme.sign secretKey request) := by
    funext input
    cases input <;> rfl
  rw [hhandler, simulateQ_liftOracleWorldLeft, simulateQ_id']

theorem simulateQ_expanded_tracedGameRestComputation
    (adversary : Adversary) (secretKey : SecretKey) :
    simulateQ (expandedAdversaryImpl secretKey)
        (tracedGameRestComputation adversary
          ⟨secretKey.root, secretKey.parameter⟩) =
      gameRest scheme adversary ⟨secretKey.root, secretKey.parameter⟩ secretKey := by
  unfold tracedGameRestComputation gameRest
  rw [simulateQ_bind,
    ← simulateQ_withTraceAppend_run_eq_signingTraceComputation,
    ← forwardOracles_add_signingOracle_eq_withTraceAppend]
  apply bind_congr
  intro result
  rcases result with ⟨forgery, log⟩
  rw [simulateQ_bind,
    simulateQ_expanded_liftOracleWorldLeft]
  simp [simulateQ_pure]

end SphincsSecurity.Concrete.FtsProbeSimulation
