import SphincsSecurity.Proof.Deterministic.FreshRequests

open OracleComp OracleSpec

namespace DeterministicSigning

set_option backward.isDefEq.respectTransparency false

variable {ι : Type} {base : OracleSpec ι} {Request Answer : Type} [DecidableEq Request]

/-- Forward the first request and replay its answer on every repetition. -/
def memoize {α : Type} (computation : OracleComp (base + (Request →ₒ Answer)) α)
    (cache : QueryCache (Request →ₒ Answer)) : OracleComp (base + (Request →ₒ Answer)) α :=
  OracleComp.recOn computation (fun value _ => pure value)
    (fun input _ ih cached => match input with
      | .inl input => liftM ((base + (Request →ₒ Answer)).query (.inl input)) >>= fun answer => ih answer cached
      | .inr request => match cached request with
        | some answer => ih answer cached
        | none => liftM ((base + (Request →ₒ Answer)).query (.inr request)) >>= fun answer =>
            ih answer (cached.cacheQuery request answer)) cache

theorem memoize_pure {α : Type} (value : α) (cache : QueryCache (Request →ₒ Answer)) :
    memoize (pure value : OracleComp (base + (Request →ₒ Answer)) α) cache = pure value := rfl

theorem memoize_base {α : Type} (input : base.Domain)
    (next : base.Range input → OracleComp (base + (Request →ₒ Answer)) α)
    (cache : QueryCache (Request →ₒ Answer)) :
    memoize (liftM ((base + (Request →ₒ Answer)).query (.inl input)) >>= next) cache =
      (liftM ((base + (Request →ₒ Answer)).query (.inl input)) >>= fun answer => memoize (next answer) cache) := rfl

theorem memoize_request {α : Type} (input : Request)
    (next : Answer → OracleComp (base + (Request →ₒ Answer)) α)
    (cache : QueryCache (Request →ₒ Answer)) :
    memoize (liftM ((base + (Request →ₒ Answer)).query (.inr input)) >>= next) cache =
      match cache input with
      | some answer => memoize (next answer) cache
      | none => liftM ((base + (Request →ₒ Answer)).query (.inr input)) >>= fun answer =>
          memoize (next answer) (cache.cacheQuery input answer) := rfl

theorem memoize_map {α β : Type} (f : α → β)
    (computation : OracleComp (base + (Request →ₒ Answer)) α)
    (cache : QueryCache (Request →ₒ Answer)) :
    memoize (f <$> computation) cache = f <$> memoize computation cache := by
  induction computation using OracleComp.inductionOn generalizing cache with
  | pure value => simp only [map_pure, memoize_pure]
  | query_bind input next ih =>
      cases input with
      | inl input =>
          simp only [map_bind, memoize_base]
          exact bind_congr fun answer => ih answer cache
      | inr input =>
          simp only [map_bind, memoize_request]
          cases h : cache input with
          | some answer => exact ih answer cache
          | none =>
              simp only [map_bind]
              exact bind_congr fun answer => ih answer _

theorem freshRequests_memoize {α : Type} (computation : OracleComp (base + (Request →ₒ Answer)) α)
    (cache : QueryCache (Request →ₒ Answer)) :
    FreshRequests {request | cache request ≠ none} (memoize computation cache) := by
  induction computation using OracleComp.inductionOn generalizing cache with
  | pure value => exact .pure value
  | query_bind input next ih =>
      cases input with
      | inl input =>
          rw [memoize_base]
          exact .base input _ (fun answer => ih answer cache)
      | inr input =>
          rw [memoize_request]
          cases hc : cache input with
          | some answer => exact ih answer cache
          | none =>
              apply FreshRequests.request (used := {request | cache request ≠ none}) input (fun h => h hc)
              intro answer
              have hset : {request | (cache.cacheQuery input answer) request ≠ none} =
                  insert input {request | cache request ≠ none} := by
                ext request
                by_cases h : request = input
                · subst request
                  simp only [QueryCache.cacheQuery_self, ne_eq, reduceCtorEq, not_false_eq_true,
                    Set.mem_setOf_eq, Set.mem_insert_iff, true_or]
                · simp [h]
              rw [← hset]
              exact ih answer _

theorem memoize_baseLift_bind {α β : Type}
    (computation : OracleComp (base + (Request →ₒ Answer)) α)
    (next : α → OracleComp base β) (cache : QueryCache (Request →ₒ Answer)) :
    memoize (computation >>= fun value => baseLift (next value)) cache =
      (memoize computation cache >>= fun value => baseLift (next value)) := by
  induction computation using OracleComp.inductionOn generalizing cache with
  | pure value =>
      simp only [pure_bind, memoize_pure]
      induction next value using OracleComp.inductionOn with
      | pure value => rfl
      | query_bind input tail ih =>
          simp only [baseLift, simulateQ_bind, simulateQ_spec_query]
          exact bind_congr ih
  | query_bind input tail ih =>
      simp only [bind_assoc]
      cases input with
      | inl input =>
          simp only [memoize_base, bind_assoc]
          exact bind_congr (fun answer => ih answer cache)
      | inr input =>
          simp only [memoize_request]
          cases hc : cache input with
          | some answer => exact ih answer cache
          | none =>
              simp only [bind_assoc]
              exact bind_congr (fun answer => ih answer (cache.cacheQuery input answer))

end DeterministicSigning
