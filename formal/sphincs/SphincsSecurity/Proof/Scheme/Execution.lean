import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.IdealStatement

/-!
# Winning execution frame

A winning support point is split into the honest root computation, the adversary and signing run,
and final verification. The final hash-only run supplies one answer function and its cached query
trace for deterministic extraction.
-/

namespace SphincsSecurity

open OracleComp OracleSpec

theorem simulateQ_romImpl_cache_le {alpha : Type} (oa : OracleComp OracleWorld alpha)
    (cache : QueryCache HashSpec) (z : alpha × QueryCache HashSpec)
    (hmem : z ∈ support ((simulateQ romImpl oa).run cache)) : cache ≤ z.2 := by
  apply OracleComp.simulateQ_run_preservesInv romImpl (cache ≤ ·) _ oa cache le_rfl z hmem
  intro input current hle result hresult
  cases input with
  | inl sample =>
      change result ∈ support (((unifFwdImpl HashSpec) sample).run current) at hresult
      have hrun := unifFwdImpl.simulateQ_run
        (hashSpec := HashSpec) (liftM (unifSpec.query sample) : ProbComp _) current
      simp only [simulateQ_spec_query] at hrun
      rw [hrun, support_map] at hresult
      obtain ⟨value, _, heq⟩ := hresult
      rw [← (Prod.mk.inj heq).2]
      exact hle
  | inr hashInput =>
      change result ∈ support
        (((randomOracle : QueryImpl HashSpec _) hashInput).run current) at hresult
      exact hle.trans (QueryImpl.withCaching_cache_le uniformSampleImpl hashInput current
        result hresult)

end SphincsSecurity
