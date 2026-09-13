import SphincsSecurity.Proof.Ots.OtsPrefixVisibleContact
import SphincsSecurity.Proof.Base.QueryTraceInvariant
namespace SphincsSecurity.Concrete.OtsContactTrace

open _root_.OracleComp OracleSpec PartialChainEndpoint
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

def SeenRow (segment : OtsPrefix) (query : segment.Query) (answer : Digest) (trace : Trace) : Prop :=
  ∃ entry ∈ trace.toList, segment.parse entry.1 = some query ∧ truncateHash entry.2 = answer

theorem seenRow_one (segment : OtsPrefix) (query : segment.Query) (answer : Digest) : ¬SeenRow segment query answer 1 := by
  simp [SeenRow]

theorem seenRow_of (segment : OtsPrefix) (query : segment.Query) (answer : Digest) (entry : HashInput × HashOutput) :
    SeenRow segment query answer (FreeMonoid.of entry) ↔ segment.parse entry.1 = some query ∧ truncateHash entry.2 = answer := by
  simp [SeenRow]

theorem seenRow_mul (segment : OtsPrefix) (query : segment.Query) (answer : Digest) (before after : Trace) :
    SeenRow segment query answer (before * after) ↔ SeenRow segment query answer before ∨ SeenRow segment query answer after := by
  simp only [SeenRow, FreeMonoid.toList_mul, List.mem_append, or_and_right, exists_or]

def RowsObserved (segment : OtsPrefix) (trace : Trace) (observed : Fin segment.digit.val → Digest → Option Digest) : Prop :=
  ∀ query : segment.Query, ∀ answer, SeenRow segment query answer trace ↔ observed query.1 query.2 = some answer

theorem rowsObserved_empty (segment : OtsPrefix) : RowsObserved segment 1 (fun _ _ => none) := by
  intro query answer
  simp only [seenRow_one, reduceCtorEq]

end SphincsSecurity.Concrete.OtsContactTrace

namespace SphincsSecurity.Concrete.OtsPrefix

open _root_.OracleComp OracleSpec PartialChainEndpoint OtsContactTrace
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

private theorem record_some_iff {State : Type} [DecidableEq State] {n : Nat}
    (observed : Fin n → State → Option State) (query target : Fin n × State) (answer value : State)
    (hc : observed query.1 query.2 = none ∨ observed query.1 query.2 = some answer) :
    record observed query answer target.1 target.2 = some value ↔
      observed target.1 target.2 = some value ∨ query = target ∧ answer = value := by
  by_cases he : target = query
  · subst target
    simp only [record, Function.update_self, Option.some.injEq, true_and]
    constructor
    · exact Or.inr
    · rintro (h | h)
      · rcases hc with hc | hc
        · simp only [hc, reduceCtorEq] at h
        · exact Option.some.inj (hc.symm.trans h)
      · exact h
  · have hrow : record observed query answer target.1 target.2 = observed target.1 target.2 := by
      by_cases hl : target.1 = query.1
      · have hi : target.2 ≠ query.2 := fun hi => he (Prod.ext hl hi)
        simp only [record, hl, Function.update_self, Function.update_of_ne hi]
      · simp only [record, Function.update_of_ne hl]
    simp only [hrow, Ne.symm he, false_and, or_false]

theorem visible_step_rows (segment : OtsPrefix) (high : segment.Query → High) (auxiliary : QueryImpl OracleWorld PMF)
    (trace : Trace) (observed : Fin segment.digit.val → Digest → Option Digest) (hrows : RowsObserved segment trace observed)
    (input : OracleWorld.Domain) (result : OracleWorld.Range input × (Fin segment.digit.val → Digest → Option Digest))
    (hr : result ∈ ((segment.visibleLazyImpl high auxiliary input).run observed).support) :
    RowsObserved segment (trace * hashObservationTrace input result.1) result.2 := by
  cases input with
  | inl input =>
      simp only [visibleLazyImpl, QueryImpl.apply_compose, visibleWorldImpl, simulateQ_spec_query,
        lazyImpl, StateT.run_mk, PMF.mem_support_map_iff] at hr
      obtain ⟨answer, _, rfl⟩ := hr
      simpa only [hashObservationTrace, mul_one] using hrows
  | inr bytes =>
      cases hp : segment.parse bytes with
      | none =>
          simp only [visibleLazyImpl, QueryImpl.apply_compose, visibleWorldImpl, visibleHashImpl, hp,
            simulateQ_spec_query, lazyImpl, StateT.run_mk, PMF.mem_support_map_iff] at hr
          obtain ⟨answer, _, rfl⟩ := hr
          intro query value
          simpa only [hashObservationTrace, seenRow_mul, seenRow_of, hp, reduceCtorEq, false_and, or_false] using hrows query value
      | some query =>
          have hb := (segment.parse_some_iff bytes query).mp hp
          subst bytes
          simp only [visibleLazyImpl, QueryImpl.apply_compose, visibleWorldImpl, visibleHashImpl, parse_input,
            simulateQ_map, simulateQ_spec_query, lazyImpl, StateT.run_map, StateT.run_mk,
            PMF.monad_map_eq_map, PMF.map_comp, Function.comp_def, PMF.mem_support_map_iff] at hr
          obtain ⟨answer, ha, rfl⟩ := hr
          have hc : observed query.1 query.2 = none ∨ observed query.1 query.2 = some answer := by
            cases hrow : observed query.1 query.2 with
            | none => exact Or.inl rfl
            | some old =>
                rw [hrow, rowLaw, PMF.mem_support_pure_iff] at ha
                exact Or.inr (congrArg some ha.symm)
          intro target value
          rw [hashObservationTrace, seenRow_mul, seenRow_of, hrows target value, record_some_iff observed query target answer value hc]
          simp only [parse_input, Option.some.injEq, truncate_combine]

theorem visible_traced_rows (segment : OtsPrefix) (high : segment.Query → High) (auxiliary : QueryImpl OracleWorld PMF)
    {Result : Type} (computation : OracleComp OracleWorld Result) (history : Trace)
    (observed : Fin segment.digit.val → Digest → Option Digest) (hrows : RowsObserved segment history observed)
    (result : (Result × Trace) × (Fin segment.digit.val → Digest → Option Digest))
    (hr : result ∈ (lazyRun auxiliary (QueryPause.traced (segment.visibleObservationTrace high)
      (simulateQ (segment.visibleWorldImpl high) computation)) observed).support) :
    RowsObserved segment (history * result.1.2) result.2 := by
  have ht : QueryPause.traced (segment.visibleObservationTrace high) (simulateQ (segment.visibleWorldImpl high) computation) =
      simulateQ (segment.visibleWorldImpl high) (QueryPause.traced hashObservationTrace computation) :=
    segment.visible_observation_program high computation
  rw [ht, lazyRun, ← QueryImpl.simulateQ_compose] at hr
  exact QueryPause.traced_simulation_invariant hashObservationTrace (segment.visibleLazyImpl high auxiliary)
    (RowsObserved segment) (fun trace rows h input answer ha => segment.visible_step_rows high auxiliary trace rows h input answer ha)
    computation history observed hrows result hr

end SphincsSecurity.Concrete.OtsPrefix
