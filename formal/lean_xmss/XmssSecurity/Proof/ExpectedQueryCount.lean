module

public import VCVio.OracleComp.QueryTracking.QueryBound
public import VCVio.OracleComp.ProbComp
public import VCVio.OracleComp.EvalDist.Sum

@[expose] public section

open OracleSpec OracleComp ENNReal

namespace XmssSecurity

/-- The expected number of matching source queries after interpreting a computation in a
stateful probabilistic oracle implementation. -/
noncomputable def expectedSimulatedQueryCount
    {ι : Type} {spec : OracleSpec ι} {α state : Type}
    (implementation : QueryImpl spec (StateT state ProbComp))
    (predicate : spec.Domain → Prop) [DecidablePred predicate]
    (computation : OracleComp spec α) (initialState : state) : ENNReal :=
  (OracleComp.recOn (motive := fun _ => state → ENNReal) computation
    (fun _ _ => 0)
    (fun input _ continuationCounts currentState =>
      (if predicate input then 1 else 0) +
        ∑' result, Pr{let x ← (implementation input).run currentState}[x = result] *
          continuationCounts result.1 result.2)) initialState

@[simp]
theorem expectedSimulatedQueryCount_pure
    {ι : Type} {spec : OracleSpec ι} {α state : Type}
    (implementation : QueryImpl spec (StateT state ProbComp))
    (predicate : spec.Domain → Prop) [DecidablePred predicate]
    (value : α) (initialState : state) :
    expectedSimulatedQueryCount implementation predicate
      (pure value : OracleComp spec α) initialState = 0 := by
  rfl

@[simp]
theorem expectedSimulatedQueryCount_query_bind
    {ι : Type} {spec : OracleSpec ι} {α state : Type}
    (implementation : QueryImpl spec (StateT state ProbComp))
    (predicate : spec.Domain → Prop) [DecidablePred predicate]
    (input : spec.Domain) (next : spec.Range input → OracleComp spec α)
    (initialState : state) :
    expectedSimulatedQueryCount implementation predicate
        (liftM (spec.query input) >>= next) initialState =
      (if predicate input then 1 else 0) +
        ∑' result, Pr{let x ← (implementation input).run initialState}[x = result] *
          expectedSimulatedQueryCount implementation predicate
            (next result.1) result.2 := by
  rfl

/-- Expected simulated query count decomposes into the head count plus the expected continuation
count. -/
theorem expectedSimulatedQueryCount_bind
    {ι : Type} {spec : OracleSpec ι} {α β state : Type}
    (implementation : QueryImpl spec (StateT state ProbComp))
    (predicate : spec.Domain → Prop) [DecidablePred predicate]
    (head : OracleComp spec α) (continuation : α → OracleComp spec β)
    (initialState : state) :
    expectedSimulatedQueryCount implementation predicate
        (head >>= continuation) initialState =
      expectedSimulatedQueryCount implementation predicate head initialState +
        ∑' result, Pr{let x ← (simulateQ implementation head).run initialState}[x = result] *
          expectedSimulatedQueryCount implementation predicate
            (continuation result.1) result.2 := by
  induction head using OracleComp.inductionOn generalizing initialState with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, OracleComp.tsum_prEvent_pure_mul]
      simp
  | query_bind input next ih =>
      rw [bind_assoc, expectedSimulatedQueryCount_query_bind,
        expectedSimulatedQueryCount_query_bind]
      simp_rw [ih, mul_add]
      rw [ENNReal.tsum_add]
      rw [simulateQ_bind, StateT.run_bind, simulateQ_query,
        OracleComp.tsum_prEvent_bind_mul]
      simp only [OracleQuery.input_query, OracleQuery.cont_query]
      rw [id_map]
      ac_rfl

theorem expectedSimulatedQueryCount_map
    {index : Type} {spec : OracleSpec index} {α β state : Type}
    (implementation : QueryImpl spec (StateT state ProbComp))
    (predicate : spec.Domain → Prop) [DecidablePred predicate]
    (project : α → β) (computation : OracleComp spec α)
    (initialState : state) :
    expectedSimulatedQueryCount implementation predicate
        (project <$> computation) initialState =
      expectedSimulatedQueryCount implementation predicate computation
        initialState := by
  rw [map_eq_bind_pure_comp]
  change expectedSimulatedQueryCount implementation predicate
      (computation >>= fun value => pure (project value)) initialState = _
  calc
    _ = expectedSimulatedQueryCount implementation predicate computation
          initialState +
        ∑' result,
          Pr{let x ← (simulateQ implementation computation).run initialState}[x = result] *
            expectedSimulatedQueryCount implementation predicate
              (pure (project result.1)) result.2 :=
      expectedSimulatedQueryCount_bind implementation predicate computation
        (fun value => pure (project value)) initialState
    _ = _ := by simp

/-- Expected simulated query counts add exactly for disjoint source predicates. -/
theorem expectedSimulatedQueryCount_or_of_disjoint
    {ι : Type} {spec : OracleSpec ι} {α state : Type}
    (implementation : QueryImpl spec (StateT state ProbComp))
    (left right : spec.Domain → Prop) [DecidablePred left] [DecidablePred right]
    (hdisjoint : ∀ input, ¬(left input ∧ right input))
    (computation : OracleComp spec α) (initialState : state) :
    expectedSimulatedQueryCount implementation
        (fun input => left input ∨ right input) computation initialState =
      expectedSimulatedQueryCount implementation left computation initialState +
        expectedSimulatedQueryCount implementation right computation initialState := by
  induction computation using OracleComp.recOn generalizing initialState with
  | pure value =>
      change expectedSimulatedQueryCount implementation
          (fun input => left input ∨ right input)
          (pure value : OracleComp spec α) initialState =
        expectedSimulatedQueryCount implementation left
            (pure value : OracleComp spec α) initialState +
          expectedSimulatedQueryCount implementation right
            (pure value : OracleComp spec α) initialState
      simp
  | queryBind input next ih =>
      change (if left input ∨ right input then 1 else 0) +
          ∑' result, Pr{let x ← (implementation input).run initialState}[x = result] *
            expectedSimulatedQueryCount implementation
              (fun input => left input ∨ right input) (next result.1) result.2 =
        ((if left input then 1 else 0) +
          ∑' result, Pr{let x ← (implementation input).run initialState}[x = result] *
            expectedSimulatedQueryCount implementation left
              (next result.1) result.2) +
        ((if right input then 1 else 0) +
          ∑' result, Pr{let x ← (implementation input).run initialState}[x = result] *
            expectedSimulatedQueryCount implementation right
              (next result.1) result.2)
      simp_rw [ih, mul_add]
      rw [ENNReal.tsum_add]
      have hindicator :
          (if left input ∨ right input then (1 : ENNReal) else 0) =
            (if left input then 1 else 0) + (if right input then 1 else 0) := by
        by_cases hleft : left input <;> by_cases hright : right input
        · exact (hdisjoint input ⟨hleft, hright⟩).elim
        · simp [hleft, hright]
        · simp [hleft, hright]
        · simp [hleft, hright]
      rw [hindicator]
      ac_rfl

end XmssSecurity
