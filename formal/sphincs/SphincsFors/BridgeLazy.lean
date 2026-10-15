import SphincsFors.BridgeHiddenSample
import SphincsFors.SecurityHiddenOutside
import SphincsFors.SecurityHiddenCost
import SphincsFors.SecuritySeedGuess
import SphincsFors.SecurityHiddenGraph

/-! Inside the stopped hidden-row execution, a uniformly sampled outside table over the short
inputs is exactly the lazy outside random oracle started from the structural cache. -/

open OracleComp OracleSpec ENNReal

namespace SphincsFors.Security.HiddenBridge

open Eager Short

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
attribute [local instance] Classical.propDecidable
noncomputable local instance lazyCoordinateDecEq : DecidableEq HiddenGraph.Coordinate :=
  Classical.decEq _
noncomputable local instance lazyInputDecEq : DecidableEq HashInput := Classical.decEq _

/-- Ordinary source queries are all short. -/
def LongSource {ι : Type} : (HiddenRows.SourceSpec HashInput HashOutput ι).Domain → Prop
  | .inr (.inl bytes) => ¬IsShort bytes
  | _ => False

abbrev OnlyShort {ι α : Type} (computation : OracleComp (HiddenRows.SourceSpec HashInput HashOutput ι) α) :
    Prop :=
  computation.IsQueryBoundP LongSource 0

section Lazy

variable {A : Type} (model : HiddenRows.Model HashInput HashOutput A HiddenGraph.Coordinate)
  (table : HiddenGraph.Table)

theorem outside_stopped_private {α : Type} (draw : unifSpec.Domain)
    (next : unifSpec.Range draw → OracleComp (HiddenRows.SourceSpec HashInput HashOutput HiddenGraph.Coordinate) α)
    (known : HiddenReveal.Knowledge HiddenGraph.Coordinate) (cache : QueryCache HashSpec) :
    HiddenOutside.stopped model table
      (liftM ((HiddenRows.SourceSpec HashInput HashOutput HiddenGraph.Coordinate).query (.inl draw)) >>= next)
      known cache =
      liftM (unifSpec.query draw) >>= fun value => HiddenOutside.stopped model table (next value) known cache := by
  unfold HiddenOutside.stopped
  rw [OracleComp.construct_query_bind]
  rfl

theorem outside_stopped_reveal {α : Type} (coordinate : HiddenGraph.Coordinate)
    (next : Digest → OracleComp (HiddenRows.SourceSpec HashInput HashOutput HiddenGraph.Coordinate) α)
    (known : HiddenReveal.Knowledge HiddenGraph.Coordinate) (cache : QueryCache HashSpec) :
    HiddenOutside.stopped model table
      (liftM ((HiddenRows.SourceSpec HashInput HashOutput HiddenGraph.Coordinate).query
        (.inr (.inr coordinate))) >>= next) known cache =
      HiddenOutside.stopped model table (next (table coordinate))
        (known.cacheQuery coordinate (table coordinate)) cache := by
  unfold HiddenOutside.stopped
  rw [OracleComp.construct_query_bind]
  rfl

theorem outside_stopped_hash {α : Type} (bytes : HashInput)
    (next : HashOutput → OracleComp (HiddenRows.SourceSpec HashInput HashOutput HiddenGraph.Coordinate) α)
    (known : HiddenReveal.Knowledge HiddenGraph.Coordinate) (cache : QueryCache HashSpec) :
    HiddenOutside.stopped model table
      (liftM ((HiddenRows.SourceSpec HashInput HashOutput HiddenGraph.Coordinate).query
        (.inr (.inl bytes))) >>= next) known cache =
      (let ordinary := HiddenOutside.outsideRead bytes cache >>= fun result =>
          HiddenOutside.stopped model table (next result.1) known result.2
      match model.parse bytes with
      | none => ordinary
      | some query =>
          if known (model.incoming query.1) = none ∧ query.2 = table (model.incoming query.1) then
            pure none
          else if query.2 = table (model.incoming query.1) then
            HiddenOutside.stopped model table (next (model.combine query.1 (table (model.outgoing query.1))))
              (known.cacheQuery (model.outgoing query.1) (table (model.outgoing query.1))) cache
          else ordinary) := by
  unfold HiddenOutside.stopped
  rw [OracleComp.construct_query_bind]
  rfl

theorem rows_answer_none (outside : HashInput → HashOutput) (bytes : HashInput)
    (h : model.parse bytes = none) : HiddenRows.answer model table outside bytes = outside bytes := by
  simp [HiddenRows.answer, h]

theorem rows_answer_match (outside : HashInput → HashOutput) (bytes : HashInput)
    (query : A × Digest) (h : model.parse bytes = some query)
    (hmatch : query.2 = table (model.incoming query.1)) :
    HiddenRows.answer model table outside bytes =
      model.combine query.1 (table (model.outgoing query.1)) := by
  simp [HiddenRows.answer, h, hmatch]

theorem rows_answer_miss (outside : HashInput → HashOutput) (bytes : HashInput)
    (query : A × Digest) (h : model.parse bytes = some query)
    (hmiss : ¬query.2 = table (model.incoming query.1)) :
    HiddenRows.answer model table outside bytes = outside bytes := by
  simp [HiddenRows.answer, h, hmiss]

omit model table in
theorem extend_cacheQuery' (cache : QueryCache HashSpec) (outside : Eager.Table) {bytes : HashInput}
    (h : IsShort bytes) (hnone : cache bytes = none) (answer : HashOutput) :
    extend (cache.cacheQuery bytes answer) outside =
      extend cache (Function.update outside ⟨bytes, h⟩ answer) := by
  funext query
  by_cases hq : query = bytes
  · subst query
    simp [extend, h, QueryCache.cacheQuery_self, hnone]
  · simp only [extend, QueryCache.cacheQuery_of_ne _ _ hq]
    split
    · rename_i hshort
      rw [Function.update_of_ne (fun heq => hq (congrArg Subtype.val heq))]
    · rfl

omit model table in
theorem extend_update_self (cache : QueryCache HashSpec) (outside : Eager.Table) {bytes : HashInput}
    (h : IsShort bytes) (hnone : cache bytes = none) (answer : HashOutput) :
    extend cache (Function.update outside ⟨bytes, h⟩ answer) bytes = answer := by
  simp [extend, hnone, h]

/-- One ordinary query answered by the sampled outside table is one lazy outside read. -/
theorem evalDist_ordinary_step {α : Type} (bytes : HashInput) (hshort : IsShort bytes)
    (next : HashOutput → OracleComp (HiddenRows.SourceSpec HashInput HashOutput HiddenGraph.Coordinate) α)
    (known : HiddenReveal.Knowledge HiddenGraph.Coordinate) (cache : QueryCache HashSpec)
    (ih : ∀ answer (cache' : QueryCache HashSpec),
      𝒟[($ᵗ Eager.Table) >>= fun outside =>
        HiddenRows.stopped model table (extend cache' outside) (next answer) known] =
      𝒟[Option.map Prod.fst <$> HiddenOutside.stopped model table (next answer) known cache']) :
    𝒟[($ᵗ Eager.Table) >>= fun outside =>
        HiddenRows.stopped model table (extend cache outside) (next (extend cache outside bytes)) known] =
      𝒟[Option.map Prod.fst <$> (HiddenOutside.outsideRead bytes cache >>= fun result =>
        HiddenOutside.stopped model table (next result.1) known result.2)] := by
  cases hc : cache bytes with
  | some answer =>
      have hext : ∀ outside, extend cache outside bytes = answer := fun outside => by simp [extend, hc]
      simp only [hext]
      rw [HiddenOutside.outsideRead, QueryImpl.withCaching_run_some _ hc, pure_bind]
      exact ih answer cache
  | none =>
      rw [HiddenOutside.outsideRead, QueryImpl.withCaching_run_none _ hc, bind_map_left, map_bind]
      let ψ : Eager.Table → ProbComp (Option α) := fun outside =>
        HiddenRows.stopped model table (extend cache outside) (next (extend cache outside bytes)) known
      have hupdate : ∀ (answer : HashOutput) (outside : Eager.Table),
          ψ (Function.update outside ⟨bytes, hshort⟩ answer) =
            HiddenRows.stopped model table (extend (cache.cacheQuery bytes answer) outside) (next answer) known := by
        intro answer outside
        simp only [ψ, extend_update_self cache outside hshort hc answer,
          extend_cacheQuery' cache outside hshort hc answer]
      change 𝒟[($ᵗ Eager.Table) >>= ψ] = _
      calc 𝒟[($ᵗ Eager.Table) >>= ψ]
          = 𝒟[(($ᵗ HashOutput : ProbComp HashOutput) >>= fun answer => ($ᵗ Eager.Table) >>=
              fun outside => pure (Function.update outside ⟨bytes, hshort⟩ answer)) >>= ψ] := by
            symm
            rw [evalDist_bind, evalDist_uniformSample_bind_update (D := ShortIn) (R := HashOutput)
              ⟨bytes, hshort⟩, ← evalDist_bind]
        _ = 𝒟[($ᵗ HashOutput : ProbComp HashOutput) >>= fun answer => ($ᵗ Eager.Table) >>= fun outside =>
              HiddenRows.stopped model table (extend (cache.cacheQuery bytes answer) outside) (next answer) known] := by
            simp only [bind_assoc, pure_bind, hupdate]
        _ = _ := by
            rw [evalDist_bind, evalDist_bind]
            congr 1
            funext answer
            exact ih answer _

/-- **Eager to lazy outside oracle** inside the stopped execution of a short-only program. -/
theorem evalDist_stopped_lazy {α : Type}
    (computation : OracleComp (HiddenRows.SourceSpec HashInput HashOutput HiddenGraph.Coordinate) α)
    (hshort : OnlyShort computation) (known : HiddenReveal.Knowledge HiddenGraph.Coordinate)
    (cache : QueryCache HashSpec) :
    𝒟[($ᵗ Eager.Table) >>= fun outside =>
        HiddenRows.stopped model table (extend cache outside) computation known] =
      𝒟[Option.map Prod.fst <$> HiddenOutside.stopped model table computation known cache] := by
  induction computation using OracleComp.inductionOn generalizing known cache with
  | pure value =>
      change 𝒟[($ᵗ Eager.Table) >>= fun _ => (pure (some value) : ProbComp _)] =
        𝒟[Option.map Prod.fst <$> (pure (some (value, cache)) : ProbComp _)]
      rw [DeferredSampling.evalDist_bind_const_neverFails _ (probFailure_uniformSample _), map_pure]
      rfl
  | query_bind input next ih =>
      rw [OnlyShort, isQueryBoundP_query_bind_iff] at hshort
      have hnext : ∀ answer, OnlyShort (next answer) := fun answer => by
        have := hshort.2 answer
        split at this <;> simpa [OnlyShort] using this
      rcases input with draw | (bytes | coordinate)
      · simp only [HiddenRows.stopped_private]
        rw [outside_stopped_private, map_bind]
        rw [evalDist_bind_bind_swap, evalDist_bind, evalDist_bind]
        congr 1
        funext value
        exact ih value (hnext value) known cache
      · have hlong : IsShort bytes := by
          rcases hshort.1 with hnot | hzero
          · simpa [LongSource] using hnot
          · omega
        simp only [HiddenRows.stopped_hash]
        rw [outside_stopped_hash]
        cases hp : model.parse bytes with
        | none =>
            simp only [rows_answer_none model table _ bytes hp]
            exact evalDist_ordinary_step model table bytes hlong next known cache
              fun answer cache' => ih answer (hnext answer) known cache'
        | some query =>
            dsimp only
            by_cases hstop : known (model.incoming query.1) = none ∧ query.2 = table (model.incoming query.1)
            · simp only [hstop, and_self, ↓reduceIte, map_pure]
              rw [DeferredSampling.evalDist_bind_const_neverFails _ (probFailure_uniformSample _)]
              rfl
            · by_cases hmatch : query.2 = table (model.incoming query.1)
              · have hknown : ¬known (model.incoming query.1) = none := fun h => hstop ⟨h, hmatch⟩
                simp only [hmatch, and_true, hknown, ↓reduceIte,
                  rows_answer_match model table _ bytes query hp hmatch]
                exact ih _ (hnext _) _ cache
              · simp only [hmatch, and_false, ↓reduceIte, rows_answer_miss model table _ bytes query hp hmatch]
                exact evalDist_ordinary_step model table bytes hlong next known cache
                  fun answer cache' => ih answer (hnext answer) known cache'
      · simp only [HiddenRows.stopped_reveal]
        rw [outside_stopped_reveal]
        exact ih _ (hnext _) _ cache

end Lazy

end SphincsFors.Security.HiddenBridge
