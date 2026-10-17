import XmssSecurity.Proof.RandomizedStatement

open OracleComp OracleSpec

namespace XmssSecurity.Seeded

variable {State : Type}

noncomputable def worldHandler (hash : QueryImpl HashSpec (StateT State ProbComp)) :
    QueryImpl OracleWorld (StateT State ProbComp) :=
  ((QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT State ProbComp)) + hash

theorem worldHandler_lift_prob {α : Type} (hash : QueryImpl HashSpec (StateT State ProbComp))
    (computation : ProbComp α) :
    simulateQ (worldHandler hash) (liftM computation : OracleComp OracleWorld α) =
      (liftM computation : StateT State ProbComp α) := by
  rw [worldHandler, QueryImpl.simulateQ_add_liftM_left, simulateQ_liftTarget, simulateQ_ofLift_eq_self]

theorem worldHandler_sampling_bind {α β : Type} (hash : QueryImpl HashSpec (StateT State ProbComp))
    (sampler : ProbComp α) (next : α → OracleComp OracleWorld β) (state : State) :
    (simulateQ (worldHandler hash) ((liftM sampler : OracleComp OracleWorld α) >>= next)).run state =
      (sampler >>= fun value => (simulateQ (worldHandler hash) (next value)).run state) := by
  rw [simulateQ_bind, worldHandler_lift_prob]
  simp only [StateT.run_bind, StateT.run_liftM, bind_assoc, pure_bind]


end XmssSecurity.Seeded
