import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Base.RomQueryCharge
namespace SphincsSecurity

open OracleComp OracleSpec ENNReal

theorem expectedQueryCharge_bind
    (charge : QueryCache HashSpec → HashInput → ℝ≥0∞)
    (computation : OracleComp OracleWorld α) (next : α → OracleComp OracleWorld β)
    (cache : QueryCache HashSpec) :
    expectedQueryCharge charge (computation >>= next) cache =
      expectedQueryCharge charge computation cache +
        ∑' result, Pr[= result | (simulateQ romImpl computation).run cache] *
          expectedQueryCharge charge (next result.1) result.2 := by
  induction computation using OracleComp.inductionOn generalizing cache with
  | pure value =>
      simp only [pure_bind, expectedQueryCharge_pure, simulateQ_pure, StateT.run_pure,
        tsum_probOutput_pure_mul, zero_add]
  | query_bind query continuation ih =>
      rw [bind_assoc, expectedQueryCharge_query_bind, expectedQueryCharge_query_bind,
        simulateQ_query_bind, StateT.run_bind, tsum_probOutput_bind_mul]
      simp_rw [ih, mul_add, ENNReal.tsum_add, ← ENNReal.tsum_mul_left]
      rw [add_assoc]
      rfl

end SphincsSecurity
