import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Fts.CacheSize
import SphincsSecurity.Proof.Scheme.Charge
namespace SphincsSecurity

open OracleComp OracleSpec ENNReal

def hashQueryCharge (charge : QueryCache HashSpec → HashInput → ℝ≥0∞)
    (cache : QueryCache HashSpec) : OracleWorld.Domain → ℝ≥0∞ :=
  Sum.elim (fun _ => 0) (charge cache)

noncomputable def expectedQueryCharge {α : Type}
    (charge : QueryCache HashSpec → HashInput → ℝ≥0∞)
    (computation : OracleComp OracleWorld α) : QueryCache HashSpec → ℝ≥0∞ :=
  OracleComp.construct (fun _ _ => 0)
    (fun query _ next cache =>
      hashQueryCharge charge cache query +
        ∑' result, Pr[= result | (romImpl query).run cache] * next result.1 result.2)
    computation

@[simp] theorem expectedQueryCharge_pure {α : Type}
    (charge : QueryCache HashSpec → HashInput → ℝ≥0∞)
    (value : α) (cache : QueryCache HashSpec) :
    expectedQueryCharge charge (pure value) cache = 0 := rfl

theorem expectedQueryCharge_query_bind {α : Type}
    (charge : QueryCache HashSpec → HashInput → ℝ≥0∞)
    (query : OracleWorld.Domain)
    (next : OracleWorld.Range query → OracleComp OracleWorld α)
    (cache : QueryCache HashSpec) :
    expectedQueryCharge charge (OracleSpec.query query >>= next) cache =
      hashQueryCharge charge cache query +
        ∑' result, Pr[= result | (romImpl query).run cache] *
          expectedQueryCharge charge (next result.1) result.2 := by
  cases query <;> rfl

theorem romImpl_query_mass (query : OracleWorld.Domain) (cache : QueryCache HashSpec) :
    (∑' result, Pr[= result | (romImpl query).run cache]) = 1 := by
  cases query with
  | inl input =>
      simp [romImpl, unifFwdImpl, QueryImpl.liftTarget, HasQuery.toQueryImpl,
        StateT.run_monadLift]
      rw [ENNReal.tsum_prod']
      simp only [tsum_ite_eq, tsum_fintype, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      simp [Fintype.card_fin]
      exact ENNReal.mul_inv_cancel (by positivity) (by finiteness)
  | inr input =>
      change (∑' result, Pr[= result | (randomOracle input).run cache]) = 1
      by_cases hfresh : cache input = none
      · rw [randomOracle, QueryImpl.withCaching_run_none _ hfresh]
        simp [uniformSampleImpl]
      · obtain ⟨answer, hanswer⟩ := Option.ne_none_iff_exists'.mp hfresh
        rw [randomOracle, QueryImpl.withCaching_run_some _ hanswer]
        simp

theorem finite_of_mem_support_romImpl {query : OracleWorld.Domain}
    {cache : QueryCache HashSpec} (hfinite : Finite cache)
    {result : OracleWorld.Range query × QueryCache HashSpec}
    (hresult : result ∈ support ((romImpl query).run cache)) : Finite result.2 := by
  cases query with
  | inl input =>
      apply Finite.of_enncard_le (q := {input | cache input ≠ none}.ncard)
      rw [romImpl_uniform_query_enncard_eq input cache result hresult,
        hfinite.cachedInputs_ncard_toENNReal_eq_enncard]
  | inr input =>
      apply Finite.of_enncard_le (q := {input | cache input ≠ none}.ncard + 1)
      push_cast
      rw [hfinite.cachedInputs_ncard_toENNReal_eq_enncard]
      exact romImpl_hash_query_enncard_le input cache result hresult

theorem expected_potential_simulateQ_le_queryCharge {α : Type}
    (potential : QueryCache HashSpec → ℝ≥0∞)
    (charge : QueryCache HashSpec → HashInput → ℝ≥0∞)
    (hstep : ∀ (query : OracleWorld.Domain) (cache : QueryCache HashSpec), Finite cache →
      (∑' result, Pr[= result | (romImpl query).run cache] * potential result.2) ≤
        potential cache + hashQueryCharge charge cache query)
    (computation : OracleComp OracleWorld α) (cache : QueryCache HashSpec)
    (hfinite : Finite cache) :
    (∑' result, Pr[= result | (simulateQ romImpl computation).run cache] * potential result.2) ≤
      potential cache + expectedQueryCharge charge computation cache := by
  induction computation using OracleComp.inductionOn generalizing cache with
  | pure value => simp [simulateQ_pure]
  | query_bind query next ih =>
      rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, tsum_probOutput_bind_mul,
        expectedQueryCharge_query_bind]
      calc
        _ ≤ ∑' result, Pr[= result | (romImpl query).run cache] *
            (potential result.2 + expectedQueryCharge charge (next result.1) result.2) := by
          apply ENNReal.tsum_le_tsum
          intro result
          by_cases hresult : result ∈ support ((romImpl query).run cache)
          · exact mul_le_mul' le_rfl
              (ih result.1 result.2 (finite_of_mem_support_romImpl hfinite hresult))
          · rw [probOutput_eq_zero_of_not_mem_support hresult, zero_mul, zero_mul]
        _ = (∑' result, Pr[= result | (romImpl query).run cache] * potential result.2) +
            ∑' result, Pr[= result | (romImpl query).run cache] *
              expectedQueryCharge charge (next result.1) result.2 := by
          simp_rw [mul_add, ENNReal.tsum_add]
        _ ≤ (potential cache +
              hashQueryCharge charge cache query) +
            ∑' result, Pr[= result | (romImpl query).run cache] *
              expectedQueryCharge charge (next result.1) result.2 :=
          add_le_add (hstep query cache hfinite) le_rfl
        _ = _ := by rw [add_assoc]

theorem expectedQueryCharge_mul {α : Type}
    (charge : QueryCache HashSpec → HashInput → ℝ≥0∞) (factor : ℝ≥0∞)
    (computation : OracleComp OracleWorld α) (cache : QueryCache HashSpec) :
    expectedQueryCharge (fun cache input => charge cache input * factor) computation cache =
      expectedQueryCharge charge computation cache * factor := by
  induction computation using OracleComp.inductionOn generalizing cache with
  | pure value => simp
  | query_bind query next ih =>
      simp only [expectedQueryCharge_query_bind, ih]
      simp_rw [← mul_assoc, ENNReal.tsum_mul_right]
      cases query <;> simp only [hashQueryCharge, Sum.elim_inl, Sum.elim_inr] <;> ring

theorem expected_potential_romImpl_le_charge
    (potential : QueryCache HashSpec → ℝ≥0∞)
    (charge : QueryCache HashSpec → HashInput → ℝ≥0∞)
    (hfresh : ∀ cache : QueryCache HashSpec, Finite cache → ∀ input : HashInput,
      cache input = none →
      (∑' answer : HashOutput, Pr[= answer | ($ᵗ HashOutput : ProbComp HashOutput)] *
        potential (cache.cacheQuery input answer)) ≤ potential cache + charge cache input)
    (query : OracleWorld.Domain) (cache : QueryCache HashSpec) (hfinite : Finite cache) :
    (∑' result, Pr[= result | (romImpl query).run cache] * potential result.2) ≤
      potential cache + hashQueryCharge charge cache query := by
  cases query with
  | inl input =>
      simp [romImpl, unifFwdImpl, QueryImpl.liftTarget, HasQuery.toQueryImpl,
        StateT.run_monadLift, hashQueryCharge]
      rw [ENNReal.tsum_prod']
      simp only [tsum_ite_eq, tsum_fintype, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      simp [Fintype.card_fin]
      rw [← mul_assoc, ENNReal.mul_inv_cancel (by positivity) (by finiteness), one_mul]
  | inr input =>
      change (∑' result, Pr[= result | (randomOracle input).run cache] * potential result.2) ≤
        potential cache + charge cache input
      by_cases huncached : cache input = none
      · rw [randomOracle, QueryImpl.withCaching_run_none _ huncached,
          tsum_probOutput_map_mul]
        exact hfresh cache hfinite input huncached
      · obtain ⟨answer, hanswer⟩ := Option.ne_none_iff_exists'.mp huncached
        rw [randomOracle, QueryImpl.withCaching_run_some _ hanswer]
        simp

end SphincsSecurity
