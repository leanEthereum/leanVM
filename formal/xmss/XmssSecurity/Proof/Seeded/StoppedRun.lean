import XmssSecurity.Proof.Seeded.GameExpansion

open OracleComp OracleSpec

namespace XmssSecurity.Seeded

set_option backward.isDefEq.respectTransparency false

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
    Pr[fun value => ∃ a, value = some a ∧ event a |
      (simulateQ romImpl (stopBefore bad computation)).run' cache] ≤
        Pr[event | (simulateQ romImpl computation).run' cache] := by
  classical
  induction computation using OracleComp.inductionOn generalizing cache with
  | pure value => simp [stopBefore_pure]
  | query_bind input next ih =>
      rw [stopBefore_query_bind]
      split
      · simp
      · simp only [run'_query_bind, probEvent_bind_eq_tsum]
        exact ENNReal.tsum_le_tsum fun result => mul_le_mul' le_rfl (ih result.1 result.2)

theorem probEvent_le_stopBefore_add_failure {α : Type} (bad : OracleWorld.Domain → Prop)
    [DecidablePred bad] (computation : OracleComp OracleWorld α)
    (cache : QueryCache HashSpec) (event : α → Prop) :
    Pr[event | (simulateQ romImpl computation).run' cache] ≤
      Pr[fun value => ∃ a, value = some a ∧ event a |
        (simulateQ romImpl (stopBefore bad computation)).run' cache] +
      Pr[= none | (simulateQ romImpl (stopBefore bad computation)).run' cache] := by
  classical
  induction computation using OracleComp.inductionOn generalizing cache with
  | pure value => simp [stopBefore_pure]
  | query_bind input next ih =>
      rw [stopBefore_query_bind]
      split
      · simp
      · simp only [run'_query_bind, probEvent_bind_eq_tsum, probOutput_bind_eq_tsum,
          ← ENNReal.tsum_add]
        exact ENNReal.tsum_le_tsum fun result =>
          (mul_le_mul' le_rfl (ih result.1 result.2)).trans_eq (mul_add ..)

end XmssSecurity.Seeded
