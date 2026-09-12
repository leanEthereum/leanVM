import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Fts.SigningProposalRecord

/-! ## JointProbeMessageHashBudget -/

namespace SphincsSecurity.Concrete.FtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

noncomputable def messageHashCharge (parameter : PublicParameter) (_ : QueryCache HashSpec) (input : HashInput) : ENNReal :=
  if MessageHashInput parameter input then 1 else 0

end SphincsSecurity.Concrete.FtsProbeSimulation

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
open FtsProbeSimulation (messageHashCharge)
attribute [local instance] Classical.propDecidable

noncomputable def boundaryRun {α : Type} (parameter : PublicParameter)
    (computation : OracleComp OracleWorld α) (cache : QueryCache HashSpec) :
    ProbComp ((α × SigningBoundaryTrace) × QueryCache HashSpec) :=
  ((simulateQ (romImpl.withTrace (signingBoundaryTrace parameter)) computation).run).run cache

theorem boundaryRun_forget {α : Type} (parameter : PublicParameter)
    (computation : OracleComp OracleWorld α) (cache : QueryCache HashSpec) :
    (fun result => (result.1.1, result.2)) <$> boundaryRun parameter computation cache =
      (simulateQ romImpl computation).run cache := by
  have h := congrArg (fun comp : StateT (QueryCache HashSpec) ProbComp α => comp.run cache)
    (QueryImpl.fst_map_run_withTrace romImpl (signingBoundaryTrace parameter) computation)
  simpa only [StateT.run_map, boundaryRun] using h

theorem boundaryRun_bind {α β : Type} (parameter : PublicParameter)
    (computation : OracleComp OracleWorld α) (next : α → OracleComp OracleWorld β)
    (cache : QueryCache HashSpec) :
    boundaryRun parameter (computation >>= next) cache =
      boundaryRun parameter computation cache >>= fun first =>
        (fun second => ((second.1.1, first.1.2 * second.1.2), second.2)) <$>
          boundaryRun parameter (next first.1.1) first.2 := by
  simp only [boundaryRun, simulateQ_bind, WriterT.run_bind, StateT.run_bind, StateT.run_map]

theorem boundaryRun_query (parameter : PublicParameter)
    (input : OracleWorld.Domain) (cache : QueryCache HashSpec) :
    boundaryRun parameter (OracleSpec.query input) cache =
      (fun result => ((result.1, signingBoundaryTrace parameter input result.1), result.2)) <$>
        (romImpl input).run cache := by
  simp [boundaryRun, QueryImpl.withTrace_apply]

theorem SigningBoundaryTrace.messageCalls_mul (first second : SigningBoundaryTrace) :
    (first * second).messageCalls = first.messageCalls ++ second.messageCalls := by
  simp only [SigningBoundaryTrace.messageCalls, FreeMonoid.toList_mul, List.filterMap_append]

noncomputable def expectedBoundaryMessageCalls {α : Type} (parameter : PublicParameter)
    (computation : OracleComp OracleWorld α) (cache : QueryCache HashSpec) : ENNReal :=
  ∑' result, Pr[= result | boundaryRun parameter computation cache] * result.1.2.messageCalls.length

@[simp] theorem expectedBoundaryMessageCalls_pure {α : Type} (parameter : PublicParameter)
    (value : α) (cache : QueryCache HashSpec) :
    expectedBoundaryMessageCalls parameter (pure value) cache = 0 := by
  simp [expectedBoundaryMessageCalls, boundaryRun, SigningBoundaryTrace.messageCalls]

theorem expectedBoundaryMessageCalls_bind {α β : Type} (parameter : PublicParameter)
    (computation : OracleComp OracleWorld α) (next : α → OracleComp OracleWorld β)
    (cache : QueryCache HashSpec) :
    expectedBoundaryMessageCalls parameter (computation >>= next) cache =
      expectedBoundaryMessageCalls parameter computation cache +
        ∑' result, Pr[= result | (simulateQ romImpl computation).run cache] *
          expectedBoundaryMessageCalls parameter (next result.1) result.2 := by
  rw [expectedBoundaryMessageCalls, boundaryRun_bind, tsum_probOutput_bind_mul]
  simp_rw [tsum_probOutput_map_mul, SigningBoundaryTrace.messageCalls_mul, List.length_append,
    Nat.cast_add, mul_add, ENNReal.tsum_add, ENNReal.tsum_mul_right]
  simp only [tsum_probOutput_of_liftM_PMF, one_mul]
  rw [← boundaryRun_forget parameter computation cache, tsum_probOutput_map_mul]
  simp only [expectedBoundaryMessageCalls, mul_add, ENNReal.tsum_add]

theorem signingBoundaryTrace_messageCalls (parameter : PublicParameter)
    (input : OracleWorld.Domain) (output : OracleWorld.Range input) (cache : QueryCache HashSpec) :
    ((signingBoundaryTrace parameter input output).messageCalls.length : ENNReal) =
      hashQueryCharge (messageHashCharge parameter) cache input := by
  cases input with
  | inl input => simp [signingBoundaryTrace, SigningBoundaryTrace.messageCalls, hashQueryCharge]
  | inr input =>
      by_cases hinput : FtsProbeSimulation.MessageHashInput parameter input <;>
        simp [signingBoundaryTrace, SigningBoundaryTrace.messageCalls, messageHashCharge,
          hashQueryCharge, hinput]

theorem expectedBoundaryMessageCalls_query (parameter : PublicParameter)
    (input : OracleWorld.Domain) (cache : QueryCache HashSpec) :
    expectedBoundaryMessageCalls parameter (OracleSpec.query input) cache =
      hashQueryCharge (messageHashCharge parameter) cache input := by
  rw [expectedBoundaryMessageCalls, boundaryRun_query, tsum_probOutput_map_mul]
  simp only [signingBoundaryTrace_messageCalls parameter input _ cache,
    ENNReal.tsum_mul_right, romImpl_query_mass, one_mul]

theorem expectedBoundaryMessageCalls_eq_queryCharge {α : Type} (parameter : PublicParameter)
    (computation : OracleComp OracleWorld α) (cache : QueryCache HashSpec) :
    expectedBoundaryMessageCalls parameter computation cache =
      expectedQueryCharge (messageHashCharge parameter) computation cache := by
  induction computation using OracleComp.inductionOn generalizing cache with
  | pure value => simp only [expectedBoundaryMessageCalls_pure, expectedQueryCharge_pure]
  | query_bind input next ih =>
      rw [expectedBoundaryMessageCalls_bind, expectedQueryCharge_query_bind,
        expectedBoundaryMessageCalls_query, simulateQ_spec_query]
      simp only [ih]

end SphincsSecurity.Concrete
