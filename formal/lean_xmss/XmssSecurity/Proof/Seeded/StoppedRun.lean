import VCVio.OracleComp.EvalDist.Sum
import XmssSecurity.Proof.RandomizedStatement

open OracleComp OracleSpec

namespace XmssSecurity.Seeded

set_option backward.isDefEq.respectTransparency false

theorem run'_lift_hash_bind {α β : Type} (computation : OracleComp HashSpec α)
    (next : α → OracleComp OracleWorld β) (cache : QueryCache HashSpec) :
    (simulateQ romImpl ((liftM computation : OracleComp OracleWorld α) >>= next)).run' cache =
      ((simulateQ randomOracle computation).run cache >>= fun result =>
        (simulateQ romImpl (next result.1)).run' result.2) := by
  rw [simulateQ_bind, StateT.run'_eq, StateT.run_bind]
  have h : simulateQ romImpl (liftM computation : OracleComp OracleWorld α) =
      simulateQ randomOracle computation :=
    QueryImpl.simulateQ_add_liftM_right _ _ computation
  rw [h, map_bind]
  rfl

theorem run'_lift_sample_bind {α β : Type} (computation : ProbComp α)
    (next : α → OracleComp OracleWorld β) (cache : QueryCache HashSpec) :
    (simulateQ romImpl ((liftM computation : OracleComp OracleWorld α) >>= next)).run' cache =
      (computation >>= fun result => (simulateQ romImpl (next result)).run' cache) := by
  rw [simulateQ_bind, StateT.run'_eq, StateT.run_bind]
  have h : simulateQ romImpl (liftM computation : OracleComp OracleWorld α) =
      simulateQ (unifFwdImpl HashSpec) computation :=
    QueryImpl.simulateQ_add_liftM_left _ _ computation
  rw [h, unifFwdImpl.simulateQ_run]
  simp only [bind_map_left, map_bind]
  rfl

noncomputable def stopBefore {α : Type} (bad : OracleWorld.Domain → Prop)
    [DecidablePred bad] (computation : OracleComp OracleWorld α) :
    OracleComp OracleWorld (Option α) :=
  OracleComp.construct (fun value => pure (some value))
    (fun input _ next => if bad input then pure none else do
      let answer ← liftM (OracleWorld.query input)
      next answer) computation

theorem stopBefore_pure {α : Type} (bad : OracleWorld.Domain → Prop)
    [DecidablePred bad] (value : α) :
    stopBefore bad (pure value) = pure (some value) := rfl

theorem stopBefore_query_bind {α : Type} (bad : OracleWorld.Domain → Prop)
    [DecidablePred bad] (input : OracleWorld.Domain)
    (next : OracleWorld.Range input → OracleComp OracleWorld α) :
    stopBefore bad (liftM (OracleWorld.query input) >>= next) =
      (if bad input then pure none else do
        let answer ← liftM (OracleWorld.query input)
        stopBefore bad (next answer)) := rfl

theorem run'_query_bind {α : Type} (input : OracleWorld.Domain)
    (next : OracleWorld.Range input → OracleComp OracleWorld α)
    (cache : QueryCache HashSpec) :
    (simulateQ romImpl (liftM (OracleWorld.query input) >>= next)).run' cache =
      ((romImpl input).run cache >>= fun result =>
        (simulateQ romImpl (next result.1)).run' result.2) := by
  simp only [simulateQ_bind, simulateQ_spec_query, StateT.run'_eq, StateT.run_bind, map_bind]

theorem probEvent_stopBefore_le {α : Type} (bad : OracleWorld.Domain → Prop)
    [DecidablePred bad] (computation : OracleComp OracleWorld α)
    (cache : QueryCache HashSpec) (event : α → Prop) :
    Pr{let value ← (simulateQ romImpl (stopBefore bad computation)).run' cache}[∃ a, value = some a ∧ event a] ≤
        Pr{let x ← (simulateQ romImpl computation).run' cache}[event x] := by
  classical
  induction computation using OracleComp.inductionOn generalizing cache with
  | pure value => simp [stopBefore_pure]
  | query_bind input next ih =>
      rw [stopBefore_query_bind]
      split
      · simp
      · simp only [run'_query_bind, OracleComp.prEvent_bind_eq_tsum]
        exact ENNReal.tsum_le_tsum fun result => mul_le_mul' le_rfl (ih result.1 result.2)

theorem probEvent_le_stopBefore_add_failure {α : Type} (bad : OracleWorld.Domain → Prop)
    [DecidablePred bad] (computation : OracleComp OracleWorld α)
    (cache : QueryCache HashSpec) (event : α → Prop) :
    Pr{let x ← (simulateQ romImpl computation).run' cache}[event x] ≤
      Pr{let value ← (simulateQ romImpl (stopBefore bad computation)).run' cache}[∃ a, value = some a ∧ event a] +
      Pr{let x ← (simulateQ romImpl (stopBefore bad computation)).run' cache}[x = none] := by
  classical
  induction computation using OracleComp.inductionOn generalizing cache with
  | pure value => simp [stopBefore_pure]
  | query_bind input next ih =>
      rw [stopBefore_query_bind]
      split
      · simp
      · simp only [run'_query_bind, OracleComp.prEvent_bind_eq_tsum, OracleComp.prEvent_bind_eq_tsum,
          ← ENNReal.tsum_add]
        exact ENNReal.tsum_le_tsum fun result =>
          (mul_le_mul' le_rfl (ih result.1 result.2)).trans_eq (mul_add ..)

end XmssSecurity.Seeded
