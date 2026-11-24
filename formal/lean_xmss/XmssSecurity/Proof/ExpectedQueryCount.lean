module

public import VCVio.OracleComp.QueryTracking.ExpectedQueryCount
public import VCVio.OracleComp.ProbComp
public import VCVio.OracleComp.EvalDist.Sum

@[expose] public section

/-! VCVio's `OracleComp.expectedSimulatedQueryCount` (an integral against the output measure) read
as a sum over the outcomes of a `ProbComp` run, the form the proofs' other expectations
(`expectedSimulatedCost`, `expectedFinal`) take. -/

open OracleSpec OracleComp ENNReal MeasureTheory

namespace XmssSecurity

/-- The expectation of a value over a `ProbComp` is the sum over its outcomes. -/
theorem lintegral_id_evalDist_map_eq_tsum {α : Type} (computation : ProbComp α) (f : α → ℝ≥0∞) :
    ∫⁻ r, r ∂𝒟[f <$> computation] = ∑' x, Pr{let y ← computation}[y = x] * f x := by
  let : MeasurableSpace α := ⊤
  rw [lintegral_evalDist_map computation .of_discrete measurable_id']
  exact lintegral_evalDist_eq_tsum computation f

variable {ι : Type} {spec : OracleSpec ι} {α β state : Type}
  (implementation : QueryImpl spec (StateT state ProbComp))
  (predicate : spec.Domain → Prop) [DecidablePred predicate]

theorem expectedSimulatedQueryCount_query_bind_tsum (input : spec.Domain)
    (next : spec.Range input → OracleComp spec α) (initialState : state) :
    expectedSimulatedQueryCount implementation predicate
        (liftM (spec.query input) >>= next) initialState =
      (if predicate input then 1 else 0) +
        ∑' result, Pr{let x ← (implementation input).run initialState}[x = result] *
          expectedSimulatedQueryCount implementation predicate (next result.1) result.2 := by
  rw [expectedSimulatedQueryCount_query_bind, lintegral_id_evalDist_map_eq_tsum]

/-- The expected count of a bind: the head's plus the expected continuation's. -/
theorem expectedSimulatedQueryCount_bind_tsum (head : OracleComp spec α)
    (continuation : α → OracleComp spec β) (initialState : state) :
    expectedSimulatedQueryCount implementation predicate (head >>= continuation) initialState =
      expectedSimulatedQueryCount implementation predicate head initialState +
        ∑' result, Pr{let x ← (simulateQ implementation head).run initialState}[x = result] *
          expectedSimulatedQueryCount implementation predicate (continuation result.1) result.2 := by
  rw [expectedSimulatedQueryCount_bind, lintegral_id_evalDist_map_eq_tsum]

end XmssSecurity
