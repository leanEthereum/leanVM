import SphincsSecurity.Proof.Base.QueryPauseTrace
import SphincsSecurity.Proof.Reference.QueryAllocation
namespace SphincsSecurity.QueryPause

open _root_.OracleComp OracleSpec
set_option backward.isDefEq.respectTransparency false

variable {Index Trace Result : Type} {spec : OracleSpec Index} [Monoid Trace]
  (observation : (input : spec.Domain) → spec.Range input → Trace)

theorem traced_simulation_invariant {State : Type} (impl : QueryImpl spec (StateT State PMF))
    (invariant : Trace → State → Prop)
    (hstep : ∀ history state, invariant history state → ∀ input,
      ∀ result ∈ ((impl input).run state).support, invariant (history * observation input result.1) result.2)
    (computation : OracleComp spec Result) (history : Trace) (state : State) (hinitial : invariant history state)
    (result : (Result × Trace) × State)
    (hresult : result ∈ ((simulateQ impl (traced observation computation)).run state).support) :
    invariant (history * result.1.2) result.2 := by
  induction computation using OracleComp.inductionOn generalizing history state result with
  | pure value =>
      simp only [traced_pure, simulateQ_pure, StateT.run_pure, PMF.monad_pure_eq_pure, PMF.mem_support_pure_iff] at hresult
      subst result
      simpa only [mul_one] using hinitial
  | query_bind input next ih =>
      simp only [traced_query_bind, simulateQ_bind, simulateQ_map, simulateQ_spec_query, StateT.run_bind, StateT.run_map,
        PMF.monad_bind_eq_bind, PMF.monad_map_eq_map, PMF.mem_support_bind_iff, PMF.mem_support_map_iff] at hresult
      obtain ⟨middle, hmiddle, tail, htail, rfl⟩ := hresult
      simpa only [mul_assoc] using ih middle.1 (history * observation input middle.1) middle.2
        (hstep history state hinitial input middle hmiddle) tail htail

theorem traced_counted_forget (selected : Index → Prop) [DecidablePred selected] (computation : OracleComp spec Result) :
    (fun result => (result.1.1, result.2)) <$> QueryCap.counted selected (traced observation computation) =
      QueryCap.counted selected computation := by
  rw [← QueryCap.counted_map, traced_forget]

theorem traced_counted_le (selected : Index → Prop) [DecidablePred selected] (cost : Trace → Nat)
    (hcost : ∀ first second, cost (first * second) = cost first + cost second)
    (hstep : ∀ input answer, (if selected input then 1 else 0) ≤ cost (observation input answer))
    (computation : OracleComp spec Result) (result : (Result × Trace) × Nat)
    (hresult : result ∈ support (QueryCap.counted selected (traced observation computation))) : result.2 ≤ cost result.1.2 := by
  apply QueryCap.counted_writer_simulate_le selected cost hcost ((QueryImpl.id' spec).withTrace observation) _ computation result hresult
  intro input output houtput
  have hquery : (((QueryImpl.id' spec).withTrace observation) input).run =
      (fun answer => (answer, observation input answer)) <$> (liftM (spec.query input) : OracleComp spec _) := by
    simp [QueryImpl.withTrace_apply, WriterT.run_bind, WriterT.run_tell]
  rw [hquery, QueryCap.counted_map, support_map] at houtput
  obtain ⟨counted, hcounted, rfl⟩ := houtput
  rw [QueryCap.counted_query, support_map] at hcounted
  obtain ⟨answer, _, rfl⟩ := hcounted
  exact hstep input answer

end SphincsSecurity.QueryPause
