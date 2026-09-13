import SphincsSecurity.Proof.Deterministic.Memoize

open OracleComp OracleSpec

namespace DeterministicSigning

set_option backward.isDefEq.respectTransparency false

variable {ι : Type} {base : OracleSpec ι} {Request Answer : Type}

abbrev RequestLog (Request Answer : Type) := QueryLog (Request →ₒ Answer)

def withRequestLog {α : Type} (computation : OracleComp (base + (Request →ₒ Answer)) α) :
    OracleComp (base + (Request →ₒ Answer)) (α × RequestLog Request Answer) :=
  OracleComp.recOn computation (fun value => pure (value, []))
    (fun input _ ih => match input with
      | .inl input => liftM ((base + (Request →ₒ Answer)).query (.inl input)) >>= ih
      | .inr input => liftM ((base + (Request →ₒ Answer)).query (.inr input)) >>= fun answer =>
          (fun result => (result.1, ⟨input, answer⟩ :: result.2)) <$> ih answer)

theorem withRequestLog_pure {α : Type} (value : α) :
    withRequestLog (pure value : OracleComp (base + (Request →ₒ Answer)) α) = pure (value, []) := rfl

theorem withRequestLog_base {α : Type} (input : base.Domain)
    (next : base.Range input → OracleComp (base + (Request →ₒ Answer)) α) :
    withRequestLog (liftM ((base + (Request →ₒ Answer)).query (.inl input)) >>= next) =
      (liftM ((base + (Request →ₒ Answer)).query (.inl input)) >>= fun answer => withRequestLog (next answer)) := rfl

theorem withRequestLog_request {α : Type} (input : Request)
    (next : Answer → OracleComp (base + (Request →ₒ Answer)) α) :
    withRequestLog (liftM ((base + (Request →ₒ Answer)).query (.inr input)) >>= next) =
      (liftM ((base + (Request →ₒ Answer)).query (.inr input)) >>= fun answer =>
        (fun result => (result.1, ⟨input, answer⟩ :: result.2)) <$> withRequestLog (next answer)) := rfl

theorem withRequestLog_map {α β : Type} (f : α → β)
    (computation : OracleComp (base + (Request →ₒ Answer)) α) :
    withRequestLog (f <$> computation) = (fun result => (f result.1, result.2)) <$> withRequestLog computation := by
  induction computation using OracleComp.inductionOn with
  | pure value => simp only [map_pure, withRequestLog_pure]
  | query_bind input next ih =>
      cases input with
      | inl input =>
          simp only [map_bind, withRequestLog_base]
          exact bind_congr ih
      | inr input =>
          simp only [map_bind, withRequestLog_request]
          apply bind_congr
          intro answer
          rw [ih answer]
          simp only [Functor.map_map]

theorem fst_withRequestLog {α : Type}
    (computation : OracleComp (base + (Request →ₒ Answer)) α) :
    Prod.fst <$> withRequestLog computation = computation := by
  induction computation using OracleComp.inductionOn with
  | pure value => rfl
  | query_bind input next ih =>
      cases input with
      | inl input =>
          simp only [withRequestLog_base, map_bind]
          exact bind_congr ih
      | inr input =>
          simp only [withRequestLog_request, map_bind, Functor.map_map]
          exact bind_congr ih

theorem FreshRequests.withRequestLog {α : Type} {used : Set Request}
    {computation : OracleComp (base + (Request →ₒ Answer)) α}
    (h : FreshRequests used computation) : FreshRequests used (withRequestLog computation) := by
  induction h with
  | pure value => exact .pure _
  | base input next _ ih =>
      rw [withRequestLog_base]
      exact .base input _ ih
  | request input hnew next _ ih =>
      rw [withRequestLog_request]
      exact .request input hnew _ (fun answer => (ih answer).map _)

variable [DecidableEq Request]

theorem withRequestLog_memoize_forget {α : Type}
    (computation : OracleComp (base + (Request →ₒ Answer)) α)
    (cache : QueryCache (Request →ₒ Answer)) :
    (fun result => (result.1.1, result.2)) <$> withRequestLog (memoize (withRequestLog computation) cache) =
      withRequestLog (memoize computation cache) := by
  rw [← withRequestLog_map Prod.fst, ← memoize_map, fst_withRequestLog]

/-- Forwarded signing requests form a sublist of the original transcript. -/
theorem memoize_log_sublist {α : Type} (computation : OracleComp (base + (Request →ₒ Answer)) α)
    (cache : QueryCache (Request →ₒ Answer))
    (result : (α × RequestLog Request Answer) × RequestLog Request Answer)
    (h : result ∈ support (withRequestLog (memoize (withRequestLog computation) cache))) :
    result.2.Sublist result.1.2 := by
  induction computation using OracleComp.inductionOn generalizing cache result with
  | pure value =>
      simp only [withRequestLog_pure, memoize_pure, mem_support_pure_iff] at h
      subst result
      exact .slnil
  | query_bind input next ih =>
      cases input with
      | inl input =>
          simp only [withRequestLog_base, memoize_base, mem_support_bind_iff] at h
          obtain ⟨answer, _, h⟩ := h
          exact ih answer cache result h
      | inr input =>
          rw [withRequestLog_request, memoize_request] at h
          cases hc : cache input with
          | some answer =>
              simp only [hc, memoize_map, withRequestLog_map, support_map, Set.mem_image] at h
              obtain ⟨tail, htail, rfl⟩ := h
              exact (ih answer cache tail htail).cons _
          | none =>
              simp only [hc, withRequestLog_request, memoize_map, withRequestLog_map,
                mem_support_bind_iff, support_map, Set.mem_image] at h
              obtain ⟨answer, _, middle, hmiddle, rfl⟩ := h
              obtain ⟨tail, htail, rfl⟩ := hmiddle
              exact (ih answer (cache.cacheQuery input answer) tail htail).cons_cons _

end DeterministicSigning
