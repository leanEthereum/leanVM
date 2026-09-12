import SphincsSecurity.Proof.Ots.OtsPrefixVisible
import SphincsSecurity.Proof.Base.QueryPause

/-! ## QueryPauseTranslation -/

namespace SphincsSecurity.QueryPause

open _root_.OracleComp OracleSpec
set_option backward.isDefEq.respectTransparency false

variable {Source Target Memory Result : Type} {source : OracleSpec Source} {target : OracleSpec Target}

theorem run_translation (stop : Memory → Prop) [DecidablePred stop]
    (sourceStep : (input : source.Domain) → source.Range input → Memory → Memory)
    (targetStep : (input : target.Domain) → target.Range input → Memory → Memory)
    (queryMap : source.Domain → target.Domain)
    (answerMap : (input : source.Domain) → target.Range (queryMap input) → source.Range input)
    (impl : QueryImpl source (OracleComp target))
    (himpl : ∀ input, impl input = answerMap input <$> liftM (target.query (queryMap input)))
    (hstep : ∀ input answer memory, targetStep (queryMap input) answer memory = sourceStep input (answerMap input answer) memory)
    (computation : OracleComp source Result) (memory : Memory) :
    run stop targetStep (simulateQ impl computation) memory =
      (fun paused => (paused.1, simulateQ impl paused.2)) <$> simulateQ impl (run stop sourceStep computation memory) := by
  induction computation using OracleComp.inductionOn generalizing memory with
  | pure result => simp only [simulateQ_pure, run_pure, map_pure]
  | query_bind input next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, himpl, bind_map_left, run_query_bind]
      by_cases hs : stop memory
      · simp only [if_pos hs, simulateQ_pure, map_pure, simulateQ_bind, simulateQ_spec_query, himpl, bind_map_left]
      · simp only [if_neg hs, simulateQ_bind, simulateQ_spec_query, himpl, bind_map_left, map_bind, hstep, ih]

end SphincsSecurity.QueryPause

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec
set_option backward.isDefEq.respectTransparency false

def hashObservationTrace : (input : OracleWorld.Domain) → OracleWorld.Range input → FreeMonoid (HashInput × HashOutput)
  | .inl _, _ => 1
  | .inr input, answer => FreeMonoid.of (input, answer)

namespace OtsPrefix

noncomputable def visibleObservationTrace (segment : OtsPrefix) (high : segment.Query → High) :
    (input : segment.VisibleWorld.Domain) → segment.VisibleWorld.Range input → FreeMonoid (HashInput × HashOutput)
  | .inl input, answer => hashObservationTrace input answer
  | .inr query, answer => FreeMonoid.of (segment.input query, combine answer (high query))

private theorem withTrace_run {Input Target Trace : Type} {spec : OracleSpec Input} {target : OracleSpec Target} [Monoid Trace]
    (impl : QueryImpl spec (OracleComp target)) (trace : (input : spec.Domain) → spec.Range input → Trace) (input : spec.Domain) :
    (impl.withTrace trace input).run = (fun answer => (answer, trace input answer)) <$> impl input := by
  simp [QueryImpl.withTrace_apply, WriterT.run_bind, WriterT.run_tell]

theorem visible_observation_step (segment : OtsPrefix) (high : segment.Query → High) (input : OracleWorld.Domain) :
    (simulateQ ((QueryImpl.id' segment.VisibleWorld).withTrace (segment.visibleObservationTrace high))
      (segment.visibleWorldImpl high input)).run =
        ((segment.visibleWorldImpl high).withTrace hashObservationTrace input).run := by
  cases input with
  | inl input =>
      simp only [visibleWorldImpl, simulateQ_spec_query, withTrace_run, visibleObservationTrace, hashObservationTrace]
      rfl
  | inr bytes =>
      cases hparse : segment.parse bytes with
      | none =>
          simp only [visibleWorldImpl, visibleHashImpl, hparse, simulateQ_spec_query, withTrace_run,
            visibleObservationTrace, hashObservationTrace]
          rfl
      | some query =>
          have hbytes := (segment.parse_some_iff bytes query).mp hparse
          subst bytes
          simp only [visibleWorldImpl, visibleHashImpl, parse_input, simulateQ_map, simulateQ_spec_query, WriterT.run_map,
            withTrace_run, visibleObservationTrace, hashObservationTrace, Functor.map_map]
          rfl

theorem visible_observation_program (segment : OtsPrefix) (high : segment.Query → High)
    {Result : Type} (computation : OracleComp OracleWorld Result) :
    (simulateQ ((QueryImpl.id' segment.VisibleWorld).withTrace (segment.visibleObservationTrace high))
      (simulateQ (segment.visibleWorldImpl high) computation)).run =
    simulateQ (segment.visibleWorldImpl high)
      ((simulateQ ((QueryImpl.id' OracleWorld).withTrace hashObservationTrace) computation).run) := by
  rw [← QueryImpl.simulateQ_compose]
  symm
  apply simulateQ_writer_compose
  intro input
  rw [QueryImpl.apply_compose, visible_observation_step, withTrace_run, withTrace_run, simulateQ_map]
  change (fun answer => (answer, hashObservationTrace input answer)) <$>
    simulateQ (segment.visibleWorldImpl high) (liftM (OracleWorld.query input)) = _
  rw [simulateQ_spec_query]

theorem visible_pause_program (segment : OtsPrefix) (high : segment.Query → High)
    (stop : FreeMonoid (HashInput × HashOutput) → Prop) [DecidablePred stop]
    {Result : Type} (computation : OracleComp OracleWorld Result) (trace : FreeMonoid (HashInput × HashOutput)) :
    QueryPause.run stop (fun input answer history => history * segment.visibleObservationTrace high input answer)
      (simulateQ (segment.visibleWorldImpl high) computation) trace =
    (fun paused => (paused.1, simulateQ (segment.visibleWorldImpl high) paused.2)) <$>
      simulateQ (segment.visibleWorldImpl high)
        (QueryPause.run stop (fun input answer history => history * hashObservationTrace input answer) computation trace) := by
  classical
  have htranslation (input : OracleWorld.Domain) : ∃ (query : segment.VisibleWorld.Domain)
      (decode : segment.VisibleWorld.Range query → OracleWorld.Range input),
      segment.visibleWorldImpl high input = decode <$> liftM (segment.VisibleWorld.query query) ∧
        ∀ answer (history : FreeMonoid (HashInput × HashOutput)),
          history * segment.visibleObservationTrace high query answer = history * hashObservationTrace input (decode answer) := by
    cases input with
    | inl input =>
        refine ⟨.inl (.inl input), id, ?_, ?_⟩
        · simp only [visibleWorldImpl, id_map]
        · intro answer history; rfl
    | inr bytes =>
        cases hparse : segment.parse bytes with
        | none =>
            refine ⟨.inl (.inr bytes), id, ?_, ?_⟩
            · simp only [visibleWorldImpl, visibleHashImpl, hparse, id_map]
            · intro answer history; rfl
        | some query =>
            refine ⟨.inr query, fun answer => combine answer (high query), ?_, ?_⟩
            · simp only [visibleWorldImpl, visibleHashImpl, hparse]
              rfl
            · intro answer history
              simp only [visibleObservationTrace, hashObservationTrace, (segment.parse_some_iff bytes query).mp hparse]
  exact QueryPause.run_translation stop _ _ (fun input => (htranslation input).choose)
    (fun input => (htranslation input).choose_spec.choose) (segment.visibleWorldImpl high)
    (fun input => (htranslation input).choose_spec.choose_spec.1)
    (fun input => (htranslation input).choose_spec.choose_spec.2) computation trace

end OtsPrefix
end SphincsSecurity.Concrete
