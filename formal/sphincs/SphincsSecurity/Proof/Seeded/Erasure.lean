import SphincsSecurity.Proof.Seeded.BudgetTransfer
import SphincsSecurity.Proof.Scheme.Execution

open OracleComp OracleSpec

namespace SphincsSecurity.Seeded

set_option backward.isDefEq.respectTransparency false

variable {ι : Type} {spec : OracleSpec ι}

/-- Remove queries whose answers are already fixed, retaining every other query. -/
inductive Erases (known : QueryCache spec) {α : Type} :
    OracleComp spec α → OracleComp spec α → Prop
  | pure (value : α) : Erases known (pure value) (pure value)
  | query (input : spec.Domain) (left right : spec.Range input → OracleComp spec α)
      (next : ∀ answer, Erases known (left answer) (right answer)) :
      Erases known (liftM (spec.query input) >>= left) (liftM (spec.query input) >>= right)
  | skip (input : spec.Domain) (answer : spec.Range input)
      (hknown : known input = some answer) (next : spec.Range input → OracleComp spec α)
      (right : OracleComp spec α) (tail : Erases known (next answer) right) :
      Erases known (liftM (spec.query input) >>= next) right
  | trans {left middle right : OracleComp spec α}
      (first : Erases known left middle) (second : Erases known middle right) : Erases known left right

theorem Erases.refl {α : Type} (known : QueryCache spec) (computation : OracleComp spec α) :
    Erases known computation computation := by
  induction computation using OracleComp.inductionOn with
  | pure value => exact .pure value
  | query_bind input next ih => exact .query input next next ih

theorem Erases.bind {α β : Type} {known : QueryCache spec} {left right : OracleComp spec α}
    (h : Erases known left right) (nextLeft nextRight : α → OracleComp spec β)
    (hnext : ∀ value, Erases known (nextLeft value) (nextRight value)) :
    Erases known (left >>= nextLeft) (right >>= nextRight) := by
  induction h generalizing β with
  | pure value => simpa only [pure_bind] using hnext value
  | query input left right _ ih =>
      simpa only [bind_assoc] using Erases.query input _ _ (fun answer => ih answer nextLeft nextRight hnext)
  | skip input answer hknown next right _ ih =>
      simpa only [bind_assoc] using Erases.skip input answer hknown _ _ (ih nextLeft nextRight hnext)
  | trans _ _ first second =>
      exact .trans (first nextLeft nextLeft (fun _ => Erases.refl known _))
        (second nextLeft nextRight hnext)

theorem Erases.map {α β : Type} {known : QueryCache spec} {left right : OracleComp spec α}
    (h : Erases known left right) (f : α → β) : Erases known (f <$> left) (f <$> right) := by
  simpa only [bind_pure_comp] using h.bind (fun a => Pure.pure (f a)) (fun a => Pure.pure (f a))
    (fun a => Erases.pure (f a))

theorem Erases.bind_known {α β : Type} {known : QueryCache spec} {left : OracleComp spec α}
    {value : α} (h : Erases known left (Pure.pure value)) (next : α → OracleComp spec β)
    (right : OracleComp spec β) (tail : Erases known (next value) right) :
    Erases known (left >>= next) right :=
  .trans (by simpa only [pure_bind] using h.bind next next (fun _ => Erases.refl known _)) tail

def worldKnown (known : QueryCache HashSpec) : QueryCache OracleWorld
  | .inl _ => none
  | .inr input => known input

theorem Erases.lift_hash {α : Type} {known : QueryCache HashSpec}
    {left right : OracleComp HashSpec α} (h : Erases known left right) :
    Erases (worldKnown known) (liftM left : OracleComp OracleWorld α) (liftM right) := by
  induction h with
  | pure value => simpa only [liftM_pure] using Erases.pure value
  | query input left right _ ih =>
      simp only [liftM_bind]
      change Erases _ (liftM (OracleWorld.query (.inr input)) >>= _)
        (liftM (OracleWorld.query (.inr input)) >>= _)
      exact Erases.query (known := worldKnown known) (Sum.inr input) _ _ ih
  | skip input answer hknown next right _ ih =>
      simp only [liftM_bind]
      change Erases _ (liftM (OracleWorld.query (.inr input)) >>= _) _
      exact Erases.skip (known := worldKnown known) (Sum.inr input) answer hknown _ _ ih
  | trans _ _ first second => exact .trans first second

theorem romImpl_preserves_known (known cache : QueryCache HashSpec) (h : known ≤ cache)
    (input : OracleWorld.Domain) (result : OracleWorld.Range input × QueryCache HashSpec)
    (hresult : result ∈ support ((romImpl input).run cache)) : known ≤ result.2 := by
  apply h.trans
  apply simulateQ_romImpl_cache_le (liftM (OracleWorld.query input) : OracleComp OracleWorld _) cache result
  simpa only [simulateQ_spec_query] using hresult

theorem Erases.evalDist_run {α : Type} {known : QueryCache HashSpec}
    {left right : OracleComp OracleWorld α} (h : Erases (worldKnown known) left right)
    (cache : QueryCache HashSpec) (hcache : known ≤ cache) :
    𝒟[(simulateQ romImpl left).run cache] = 𝒟[(simulateQ romImpl right).run cache] := by
  induction h generalizing cache with
  | pure value => rfl
  | query input left right _ ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
      exact evalDist_bind_congr fun result hresult =>
        ih result.1 result.2 (romImpl_preserves_known known cache hcache input result hresult)
  | skip input answer hknown next right _ ih =>
      cases input with
      | inl input => simp [worldKnown] at hknown
      | inr input =>
          have hc : cache input = some answer := hcache hknown
          simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
          change 𝒟[(randomOracle (spec := HashSpec) input).run cache >>= _] = _
          rw [QueryImpl.withCaching_run_some _ hc, pure_bind]
          exact ih cache hcache
  | trans _ _ first second => exact (first cache hcache).trans (second cache hcache)

theorem Erases.hashQueryBound {α : Type} {known : QueryCache HashSpec}
    {left right : OracleComp OracleWorld α} (h : Erases (worldKnown known) left right)
    (cache : QueryCache HashSpec) (hcache : known ≤ cache) (q : Nat)
    (hbound : HashQueryBound left cache q) : HashQueryBound right cache q := by
  induction h generalizing cache q with
  | pure value => exact hbound
  | query input left right _ ih =>
      obtain ⟨step, hstep⟩ := probComp_support_nonempty ((romImpl input).run cache)
      have hcost := (hashQueryBound_query_bind input left cache q hbound step hstep).1
      apply hashQueryBound_query_bind_of input right cache q hcost
      intro result hresult
      exact ih result.1 result.2 (romImpl_preserves_known known cache hcache input result hresult) _
        (hashQueryBound_query_bind input left cache q hbound result hresult).2
  | skip input answer hknown next right _ ih =>
      cases input with
      | inl input => simp [worldKnown] at hknown
      | inr input =>
          have hc : cache input = some answer := hcache hknown
          have hstep : (answer, cache) ∈ support ((romImpl (.inr input)).run cache) := by
            change (answer, cache) ∈ support ((randomOracle (spec := HashSpec) input).run cache)
            rw [QueryImpl.withCaching_run_some _ hc]
            simp
          exact (ih cache hcache _ (hashQueryBound_query_bind _ _ _ _ hbound _ hstep).2).mono (Nat.sub_le _ _)
  | trans _ _ first second => exact second cache hcache q (first cache hcache q hbound)

end SphincsSecurity.Seeded
