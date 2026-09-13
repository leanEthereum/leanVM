import SphincsSecurity.Statement

open OracleComp OracleSpec

namespace DeterministicSigning

set_option backward.isDefEq.respectTransparency false

variable {D R : Type} [DecidableEq D]

/-- All queries along this execution have the stated answers in the cache. -/
inductive Resolves (cache : QueryCache (D →ₒ R)) {α : Type} : OracleComp (D →ₒ R) α → α → Prop
  | pure (value : α) : Resolves cache (pure value) value
  | query (input : D) (answer : R) (hanswer : cache input = some answer)
      (next : R → OracleComp (D →ₒ R) α) (value : α)
      (tail : Resolves cache (next answer) value) :
      Resolves cache (liftM ((D →ₒ R).query input) >>= next) value

omit [DecidableEq D] in
theorem Resolves.mono {α : Type} {left right : QueryCache (D →ₒ R)}
    {computation : OracleComp (D →ₒ R) α} {value : α}
    (h : Resolves left computation value) (hle : left ≤ right) : Resolves right computation value := by
  induction h with
  | pure value => exact .pure value
  | query input answer hanswer next value _ ih => exact .query input answer (hle hanswer) next value ih

variable [SampleableType R]

theorem cache_le_of_run {α : Type} (computation : OracleComp (D →ₒ R) α)
    (before : QueryCache (D →ₒ R)) (result : α × QueryCache (D →ₒ R))
    (h : result ∈ support ((simulateQ randomOracle computation).run before)) : before ≤ result.2 := by
  induction computation using OracleComp.inductionOn generalizing before result with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at h
      subst result
      exact le_rfl
  | query_bind input next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at h
      obtain ⟨step, hstep, htail⟩ := h
      exact (QueryImpl.withCaching_cache_le _ input before step hstep).trans (ih step.1 step.2 result htail)

theorem query_caches (input : D) (before : QueryCache (D →ₒ R))
    (result : R × QueryCache (D →ₒ R))
    (h : result ∈ support ((randomOracle (spec := D →ₒ R) input).run before)) :
    result.2 input = some result.1 := by
  cases hc : before input with
  | none =>
      rw [QueryImpl.withCaching_run_none _ hc, support_map] at h
      obtain ⟨answer, _, rfl⟩ := h
      exact QueryCache.cacheQuery_self _ _ _
  | some answer =>
      rw [QueryImpl.withCaching_run_some _ hc, mem_support_pure_iff] at h
      subst result
      exact hc

theorem resolves_of_run {α : Type} (computation : OracleComp (D →ₒ R) α)
    (before : QueryCache (D →ₒ R)) (result : α × QueryCache (D →ₒ R))
    (h : result ∈ support ((simulateQ randomOracle computation).run before)) :
    Resolves result.2 computation result.1 := by
  induction computation using OracleComp.inductionOn generalizing before result with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at h
      subst result
      exact .pure value
  | query_bind input next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at h
      obtain ⟨step, hstep, htail⟩ := h
      have hle := cache_le_of_run (next step.1) step.2 result htail
      exact .query input step.1 (hle (query_caches input before step hstep)) next result.1
        (ih step.1 step.2 result htail)

theorem Resolves.run_eq_pure {α : Type} {cache : QueryCache (D →ₒ R)}
    {computation : OracleComp (D →ₒ R) α} {value : α}
    (h : Resolves cache computation value) :
    (simulateQ randomOracle computation).run cache = Pure.pure (value, cache) := by
  induction h with
  | pure value => rfl
  | query input answer hanswer next value _ ih =>
      rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind,
        QueryImpl.withCaching_run_some _ hanswer, pure_bind, ih]

/-- Repeating a deterministic execution gives the same answer, even after more oracle queries. -/
theorem replay_run {α : Type} (computation : OracleComp (D →ₒ R) α)
    (before : QueryCache (D →ₒ R)) (result : α × QueryCache (D →ₒ R))
    (h : result ∈ support ((simulateQ randomOracle computation).run before))
    (after : QueryCache (D →ₒ R)) (hle : result.2 ≤ after) :
    (simulateQ randomOracle computation).run after = pure (result.1, after) :=
  ((resolves_of_run computation before result h).mono hle).run_eq_pure

end DeterministicSigning
