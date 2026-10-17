import SphincsFors.BridgeRich

/-! Every non-stopped lazy run is a run of one fixed answer function read off its final
cache, and each canonical row query in it had a reachable incoming coordinate: initially
known, revealed, or a successor of such a coordinate. -/

open OracleComp OracleSpec ENNReal

namespace SphincsFors.Security.HiddenBridge

open HiddenCost GraphView Stop

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
attribute [local instance] Classical.propDecidable
noncomputable local instance supportCoordinateDecEq : DecidableEq HiddenGraph.Coordinate :=
  Classical.decEq _
noncomputable local instance supportInputDecEq : DecidableEq HashInput := Classical.decEq _

section Support

variable {A : Type} (model : HiddenRows.Model HashInput HashOutput A HiddenGraph.Coordinate)
  (table : HiddenGraph.Table)

/-- Coordinates reachable from knowledge and a list of reveals by row successors. -/
inductive Reach (known : HiddenReveal.Knowledge HiddenGraph.Coordinate)
    (reveals : List HiddenGraph.Coordinate) : HiddenGraph.Coordinate → Prop
  | known (coordinate : HiddenGraph.Coordinate) (value : Digest) :
      known coordinate = some value → Reach known reveals coordinate
  | reveal (coordinate : HiddenGraph.Coordinate) : coordinate ∈ reveals → Reach known reveals coordinate
  | succ (address : A) :
      Reach known reveals (model.incoming address) → Reach known reveals (model.outgoing address)

/-- Every canonical row input of the trace had a reachable incoming coordinate. -/
def NoHiddenGuess (known : HiddenReveal.Knowledge HiddenGraph.Coordinate)
    (reveals : List HiddenGraph.Coordinate) (entries : List (Entry HashInput)) : Prop :=
  ∀ bytes, Sum.inl bytes ∈ entries → ∀ query, model.parse bytes = some query →
    query.2 = table (model.incoming query.1) → Reach model known reveals (model.incoming query.1)

/-- The answer function determined by a final outside cache. -/
noncomputable def finalFn (cache : QueryCache HashSpec) : HashInput → HashOutput :=
  HiddenRows.answer model table (fun bytes => (cache bytes).getD 0)

theorem reach_mono {known known' : HiddenReveal.Knowledge HiddenGraph.Coordinate}
    {reveals reveals' : List HiddenGraph.Coordinate}
    (hknown : ∀ coordinate value, known coordinate = some value →
      Reach model known' reveals' coordinate)
    (hreveals : ∀ coordinate ∈ reveals, Reach model known' reveals' coordinate)
    {coordinate : HiddenGraph.Coordinate} (h : Reach model known reveals coordinate) :
    Reach model known' reveals' coordinate := by
  induction h with
  | known coordinate value hvalue => exact hknown coordinate value hvalue
  | reveal coordinate hmem => exact hreveals coordinate hmem
  | succ address _ ih => exact .succ address ih

theorem costRun_map {α β : Type} (f : HashInput → HashOutput) (g : α → β)
    (computation : OracleComp CostSpec α) :
    costRun f table (g <$> computation) =
      (fun result => (g result.1, result.2)) <$> costRun f table computation := by
  rw [costRun, trace_map, simulateQ_map, costRun]

theorem withReveals_query_bind' {α : Type} (input : CostSpec.Domain)
    (next : CostSpec.Range input → OracleComp CostSpec α) :
    withReveals (liftM (CostSpec.query input) >>= next) =
      liftM (CostSpec.query input) >>= fun value =>
        (fun result => (result.1, revealed input ++ result.2)) <$> withReveals (next value) :=
  withReveals_query_bind input next

theorem outsideRead_support (bytes : HashInput) (cache : QueryCache HashSpec)
    (result : HashOutput × QueryCache HashSpec)
    (hresult : result ∈ support (HiddenOutside.outsideRead bytes cache)) :
    result.2 bytes = some result.1 ∧ ∀ input answer, cache input = some answer → result.2 input = some answer := by
  unfold HiddenOutside.outsideRead at hresult
  cases hc : cache bytes with
  | some answer =>
      rw [QueryImpl.withCaching_run_some _ hc, support_pure, Set.mem_singleton_iff] at hresult
      subst result
      exact ⟨hc, fun _ _ h => h⟩
  | none =>
      rw [QueryImpl.withCaching_run_none _ hc, support_map] at hresult
      obtain ⟨answer, _, rfl⟩ := hresult
      refine ⟨by change (cache.cacheQuery bytes answer) bytes = some answer
                 exact QueryCache.cacheQuery_self _ _ _, fun input value hinput => ?_⟩
      have hne : input ≠ bytes := by
        rintro rfl
        rw [hc] at hinput
        cases hinput
      change (cache.cacheQuery bytes answer) input = some value
      rw [QueryCache.cacheQuery_of_ne _ _ hne]
      exact hinput

theorem erase_trace_withReveals_query_bind {α : Type} (input : CostSpec.Domain)
    (next : CostSpec.Range input → OracleComp CostSpec α) :
    erase (trace (withReveals (liftM (CostSpec.query input) >>= next))) =
      eraseQuery input >>= fun value =>
        (fun result => ((result.1.1, revealed input ++ result.1.2), recorded input ++ result.2)) <$>
          erase (trace (withReveals (next value))) := by
  rw [withReveals_query_bind', erase_trace_query_bind]
  congr 1
  funext value
  rw [trace_map, erase_map, Functor.map_map]

omit model table in
theorem mem_support_option_map {α β : Type} (g : α → β) (program : ProbComp (Option α)) (value : β)
    (h : some value ∈ support (Option.map g <$> program)) :
    ∃ inner, some inner ∈ support program ∧ g inner = value := by
  rw [support_map] at h
  obtain ⟨result, hresult, heq⟩ := h
  cases result with
  | none => cases heq
  | some inner => exact ⟨inner, hresult, Option.some.inj heq⟩

/-- **Lazy stopped support.** -/
theorem lazy_support {β : Type} (computation : OracleComp CostSpec β) :
    ∀ (known : HiddenReveal.Knowledge HiddenGraph.Coordinate) (cache cacheF : QueryCache HashSpec)
      (value : β × List HiddenGraph.Coordinate) (entries : List (Entry HashInput)),
      some ((value, entries), cacheF) ∈ support
        (HiddenOutside.stopped model table (erase (trace (withReveals computation))) known cache) →
      (∀ input answer, cache input = some answer → cacheF input = some answer) ∧
      (value, entries) ∈ support (costRun (finalFn model table cacheF) table (withReveals computation)) ∧
      NoHiddenGuess model table known value.2 entries := by
  induction computation using OracleComp.inductionOn with
  | pure result =>
      intro known cache cacheF value entries h
      change some ((value, entries), cacheF) ∈ support
        (pure (some (((result, []), []), cache)) : ProbComp _) at h
      rw [support_pure, Set.mem_singleton_iff, Option.some.injEq, Prod.mk.injEq, Prod.mk.injEq] at h
      obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h
      refine ⟨fun _ _ hc => hc, ?_, fun _ hmem => by simp at hmem⟩
      change ((result, []), []) ∈ support (costRun _ table (pure (result, [])))
      rw [costRun_pure]
      simp
  | query_bind input next ih =>
      intro known cache cacheF value entries h
      rw [erase_trace_withReveals_query_bind] at h
      rw [withReveals_query_bind', costRun_query_bind]
      rcases input with (draw | (bytes | coordinate)) | amount
      · -- private draw
        change some _ ∈ support (HiddenOutside.stopped model table
          (liftM ((HiddenRows.SourceSpec HashInput HashOutput HiddenGraph.Coordinate).query (.inl draw)) >>= _)
          known cache) at h
        rw [outside_stopped_private, mem_support_bind_iff] at h
        obtain ⟨sample, hsample, h⟩ := h
        rw [outside_stopped_map] at h
        obtain ⟨⟨⟨value', entries'⟩, cacheF'⟩, hinner, heq⟩ := mem_support_option_map _ _ _ h
        simp only [Prod.mk.injEq] at heq
        obtain ⟨⟨rfl, rfl⟩, rfl⟩ := heq
        obtain ⟨hcache, hrun, hguess⟩ := ih sample known cache _ value' entries' hinner
        refine ⟨hcache, ?_, ?_⟩
        · rw [mem_support_bind_iff]
          refine ⟨sample, hsample, ?_⟩
          rw [costRun_map, Functor.map_map, support_map]
          exact ⟨(value', entries'), hrun, rfl⟩
        · intro bytes hmem query hparse hmatch
          simp only [recorded, List.nil_append] at hmem
          exact hguess bytes hmem query hparse hmatch
      · -- ordinary query
        change some _ ∈ support (HiddenOutside.stopped model table
          (liftM ((HiddenRows.SourceSpec HashInput HashOutput HiddenGraph.Coordinate).query
            (.inr (.inl bytes))) >>= _) known cache) at h
        rw [outside_stopped_hash] at h
        simp only [revealed, recorded, List.nil_append, List.singleton_append] at h ⊢
        have hfirst : fixedCostP (finalFn model table cacheF) table (.inl (.inr (.inl bytes))) =
            pure (finalFn model table cacheF bytes) := rfl
        rw [hfirst, pure_bind]
        cases hp : model.parse bytes with
        | none =>
            simp only [hp] at h
            rw [mem_support_bind_iff] at h
            obtain ⟨read, hread, h⟩ := h
            rw [outside_stopped_map] at h
            obtain ⟨⟨⟨value', entries'⟩, cacheF'⟩, hinner, heq⟩ := mem_support_option_map _ _ _ h
            simp only [Prod.mk.injEq] at heq
            obtain ⟨⟨rfl, rfl⟩, rfl⟩ := heq
            obtain ⟨hcache, hrun, hguess⟩ := ih read.1 known read.2 _ value' entries' hinner
            obtain ⟨hbytes, hgrow⟩ := outsideRead_support bytes cache read hread
            have hanswer : finalFn model table cacheF' bytes = read.1 := by
              rw [finalFn, rows_answer_none model table _ bytes hp, hcache _ _ hbytes]
              rfl
            refine ⟨fun input answer hc => hcache _ _ (hgrow _ _ hc), ?_, ?_⟩
            · rw [hanswer, support_map]
              exact ⟨(value', entries'), by simpa using hrun, rfl⟩
            · intro other hmem query hparse hmatch
              rcases List.mem_cons.mp hmem with heq | hmem
              · cases heq
                rw [hp] at hparse
                cases hparse
              · exact hguess other hmem query hparse hmatch
        | some query =>
            simp only [hp] at h
            by_cases hstop : known (model.incoming query.1) = none ∧ query.2 = table (model.incoming query.1)
            · rw [if_pos hstop] at h
              simp at h
            · rw [if_neg hstop] at h
              by_cases hmatch : query.2 = table (model.incoming query.1)
              · rw [if_pos hmatch, outside_stopped_map] at h
                have hknown : known (model.incoming query.1) ≠ none := fun hnone => hstop ⟨hnone, hmatch⟩
                obtain ⟨⟨⟨value', entries'⟩, cacheF'⟩, hinner, heq⟩ := mem_support_option_map _ _ _ h
                simp only [Prod.mk.injEq] at heq
                obtain ⟨⟨rfl, rfl⟩, rfl⟩ := heq
                obtain ⟨hcache, hrun, hguess⟩ := ih _ _ cache _ value' entries' hinner
                have hanswer : finalFn model table cacheF' bytes =
                    model.combine query.1 (table (model.outgoing query.1)) := by
                  rw [finalFn, rows_answer_match model table _ bytes query hp hmatch]
                refine ⟨hcache, ?_, ?_⟩
                · rw [hanswer, support_map]
                  exact ⟨(value', entries'), by simpa using hrun, rfl⟩
                · obtain ⟨incomingValue, hincoming⟩ := Option.ne_none_iff_exists'.mp hknown
                  intro other hmem query' hparse hmatch'
                  rcases List.mem_cons.mp hmem with heq | hmem
                  · cases heq
                    rw [hp] at hparse
                    cases hparse
                    exact .known _ _ hincoming
                  · refine reach_mono model ?_ (fun c hc => .reveal _ hc)
                      (hguess other hmem query' hparse hmatch')
                    intro c v hc
                    by_cases heq : c = model.outgoing query.1
                    · subst c
                      exact .succ query.1 (.known _ _ hincoming)
                    · rw [QueryCache.cacheQuery_of_ne _ _ heq] at hc
                      exact .known _ _ hc
              · rw [if_neg hmatch, mem_support_bind_iff] at h
                obtain ⟨read, hread, h⟩ := h
                rw [outside_stopped_map] at h
                obtain ⟨⟨⟨value', entries'⟩, cacheF'⟩, hinner, heq⟩ := mem_support_option_map _ _ _ h
                simp only [Prod.mk.injEq] at heq
                obtain ⟨⟨rfl, rfl⟩, rfl⟩ := heq
                obtain ⟨hcache, hrun, hguess⟩ := ih read.1 known read.2 _ value' entries' hinner
                obtain ⟨hbytes, hgrow⟩ := outsideRead_support bytes cache read hread
                have hanswer : finalFn model table cacheF' bytes = read.1 := by
                  rw [finalFn, rows_answer_miss model table _ bytes query hp hmatch, hcache _ _ hbytes]
                  rfl
                refine ⟨fun input answer hc => hcache _ _ (hgrow _ _ hc), ?_, ?_⟩
                · rw [hanswer, support_map]
                  exact ⟨(value', entries'), by simpa using hrun, rfl⟩
                · intro other hmem query' hparse hmatch'
                  rcases List.mem_cons.mp hmem with heq | hmem
                  · cases heq
                    rw [hp] at hparse
                    cases hparse
                    exact absurd hmatch' hmatch
                  · exact hguess other hmem query' hparse hmatch'
      · -- reveal
        change some _ ∈ support (HiddenOutside.stopped model table
          (liftM ((HiddenRows.SourceSpec HashInput HashOutput HiddenGraph.Coordinate).query
            (.inr (.inr coordinate))) >>= _) known cache) at h
        rw [outside_stopped_reveal, outside_stopped_map] at h
        obtain ⟨⟨⟨value', entries'⟩, cacheF'⟩, hinner, heq⟩ := mem_support_option_map _ _ _ h
        simp only [Prod.mk.injEq] at heq
        obtain ⟨⟨rfl, rfl⟩, rfl⟩ := heq
        obtain ⟨hcache, hrun, hguess⟩ := ih _ _ cache _ value' entries' hinner
        refine ⟨hcache, ?_, ?_⟩
        · rw [mem_support_bind_iff]
          refine ⟨table coordinate, by simp [fixedCostP], ?_⟩
          rw [costRun_map, Functor.map_map, support_map]
          exact ⟨(value', entries'), hrun, rfl⟩
        · intro bytes hmem query hparse hmatch
          simp only [recorded, List.nil_append] at hmem
          refine reach_mono model ?_ ?_ (hguess bytes hmem query hparse hmatch)
          · intro other value hother
            by_cases heq : other = coordinate
            · subst other
              exact .reveal _ (by simp [revealed])
            · rw [QueryCache.cacheQuery_of_ne _ _ heq] at hother
              exact .known _ _ hother
          · intro other hmem'
            exact .reveal _ (by simp [revealed, hmem'])
      · -- virtual tick
        change some _ ∈ support (HiddenOutside.stopped model table (pure () >>= _) known cache) at h
        rw [pure_bind, outside_stopped_map] at h
        obtain ⟨⟨⟨value', entries'⟩, cacheF'⟩, hinner, heq⟩ := mem_support_option_map _ _ _ h
        simp only [Prod.mk.injEq] at heq
        obtain ⟨⟨rfl, rfl⟩, rfl⟩ := heq
        obtain ⟨hcache, hrun, hguess⟩ := ih () known cache _ value' entries' hinner
        refine ⟨hcache, ?_, ?_⟩
        · rw [mem_support_bind_iff]
          refine ⟨(), by simp [fixedCostP], ?_⟩
          rw [costRun_map, Functor.map_map, support_map]
          exact ⟨(value', entries'), hrun, rfl⟩
        · intro bytes hmem query hparse hmatch
          simp only [recorded, List.singleton_append, List.mem_cons, reduceCtorEq, false_or] at hmem
          exact hguess bytes hmem query hparse hmatch

/-- Queried inputs other than canonical row inputs are in the final outside cache. -/
def CachedQueries (cacheF : QueryCache HashSpec) (entries : List (Entry HashInput)) : Prop :=
  ∀ bytes, Sum.inl bytes ∈ entries →
    (∀ query, model.parse bytes = some query → ¬query.2 = table (model.incoming query.1)) →
      cacheF bytes ≠ none

theorem lazy_cached {β : Type} (computation : OracleComp CostSpec β) :
    ∀ (known : HiddenReveal.Knowledge HiddenGraph.Coordinate) (cache cacheF : QueryCache HashSpec)
      (value : β × List HiddenGraph.Coordinate) (entries : List (Entry HashInput)),
      some ((value, entries), cacheF) ∈ support
        (HiddenOutside.stopped model table (erase (trace (withReveals computation))) known cache) →
      (∀ input answer, cache input = some answer → cacheF input = some answer) ∧
      CachedQueries model table cacheF entries := by
  induction computation using OracleComp.inductionOn with
  | pure result =>
      intro known cache cacheF value entries h
      change some ((value, entries), cacheF) ∈ support
        (pure (some (((result, []), []), cache)) : ProbComp _) at h
      rw [support_pure, Set.mem_singleton_iff, Option.some.injEq, Prod.mk.injEq, Prod.mk.injEq] at h
      obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h
      exact ⟨fun _ _ hc => hc, fun _ hmem => by simp at hmem⟩
  | query_bind input next ih =>
      intro known cache cacheF value entries h
      rw [erase_trace_withReveals_query_bind] at h
      rcases input with (draw | (bytes | coordinate)) | amount
      · change some _ ∈ support (HiddenOutside.stopped model table
          (liftM ((HiddenRows.SourceSpec HashInput HashOutput HiddenGraph.Coordinate).query (.inl draw)) >>= _)
          known cache) at h
        rw [outside_stopped_private, mem_support_bind_iff] at h
        obtain ⟨sample, -, h⟩ := h
        rw [outside_stopped_map] at h
        obtain ⟨⟨⟨value', entries'⟩, cacheF'⟩, hinner, heq⟩ := mem_support_option_map _ _ _ h
        simp only [Prod.mk.injEq] at heq
        obtain ⟨⟨rfl, rfl⟩, rfl⟩ := heq
        obtain ⟨hcache, hcached⟩ := ih sample known cache _ value' entries' hinner
        refine ⟨hcache, fun bytes hmem => ?_⟩
        simp only [recorded, List.nil_append] at hmem
        exact hcached bytes hmem
      · change some _ ∈ support (HiddenOutside.stopped model table
          (liftM ((HiddenRows.SourceSpec HashInput HashOutput HiddenGraph.Coordinate).query
            (.inr (.inl bytes))) >>= _) known cache) at h
        rw [outside_stopped_hash] at h
        simp only [revealed, recorded, List.nil_append, List.singleton_append] at h ⊢
        -- shared outside-read branch
        have hreadCase : some ((value, entries), cacheF) ∈ support
            (HiddenOutside.outsideRead bytes cache >>= fun result =>
              HiddenOutside.stopped model table
                ((fun result => ((result.1.1, result.1.2), Sum.inl bytes :: result.2)) <$>
                  erase (trace (withReveals (next result.1)))) known result.2) →
            (∀ input answer, cache input = some answer → cacheF input = some answer) ∧
            CachedQueries model table cacheF entries := by
          intro h
          rw [mem_support_bind_iff] at h
          obtain ⟨read, hread, h⟩ := h
          rw [outside_stopped_map] at h
          obtain ⟨⟨⟨value', entries'⟩, cacheF'⟩, hinner, heq⟩ := mem_support_option_map _ _ _ h
          simp only [Prod.mk.injEq] at heq
          obtain ⟨⟨rfl, rfl⟩, rfl⟩ := heq
          obtain ⟨hcache, hcached⟩ := ih read.1 known read.2 _ value' entries' hinner
          obtain ⟨hbytes, hgrow⟩ := outsideRead_support bytes cache read hread
          refine ⟨fun input answer hc => hcache _ _ (hgrow _ _ hc), fun other hmem hnot => ?_⟩
          rcases List.mem_cons.mp hmem with heq | hmem
          · cases heq
            rw [hcache _ _ hbytes]
            exact Option.some_ne_none _
          · exact hcached other hmem hnot
        cases hp : model.parse bytes with
        | none =>
            simp only [hp] at h
            exact hreadCase h
        | some query =>
            simp only [hp] at h
            by_cases hstop : known (model.incoming query.1) = none ∧ query.2 = table (model.incoming query.1)
            · rw [if_pos hstop] at h
              simp at h
            · rw [if_neg hstop] at h
              by_cases hmatch : query.2 = table (model.incoming query.1)
              · rw [if_pos hmatch, outside_stopped_map] at h
                obtain ⟨⟨⟨value', entries'⟩, cacheF'⟩, hinner, heq⟩ := mem_support_option_map _ _ _ h
                simp only [Prod.mk.injEq] at heq
                obtain ⟨⟨rfl, rfl⟩, rfl⟩ := heq
                obtain ⟨hcache, hcached⟩ := ih _ _ cache _ value' entries' hinner
                refine ⟨hcache, fun other hmem hnot => ?_⟩
                rcases List.mem_cons.mp hmem with heq | hmem
                · cases heq
                  exact absurd hmatch (hnot query hp)
                · exact hcached other hmem hnot
              · rw [if_neg hmatch] at h
                exact hreadCase h
      · change some _ ∈ support (HiddenOutside.stopped model table
          (liftM ((HiddenRows.SourceSpec HashInput HashOutput HiddenGraph.Coordinate).query
            (.inr (.inr coordinate))) >>= _) known cache) at h
        rw [outside_stopped_reveal, outside_stopped_map] at h
        obtain ⟨⟨⟨value', entries'⟩, cacheF'⟩, hinner, heq⟩ := mem_support_option_map _ _ _ h
        simp only [Prod.mk.injEq] at heq
        obtain ⟨⟨rfl, rfl⟩, rfl⟩ := heq
        obtain ⟨hcache, hcached⟩ := ih _ _ cache _ value' entries' hinner
        refine ⟨hcache, fun bytes hmem => ?_⟩
        simp only [recorded, List.nil_append] at hmem
        exact hcached bytes hmem
      · change some _ ∈ support (HiddenOutside.stopped model table (pure () >>= _) known cache) at h
        rw [pure_bind, outside_stopped_map] at h
        obtain ⟨⟨⟨value', entries'⟩, cacheF'⟩, hinner, heq⟩ := mem_support_option_map _ _ _ h
        simp only [Prod.mk.injEq] at heq
        obtain ⟨⟨rfl, rfl⟩, rfl⟩ := heq
        obtain ⟨hcache, hcached⟩ := ih () known cache _ value' entries' hinner
        refine ⟨hcache, fun bytes hmem => ?_⟩
        simp only [recorded, List.singleton_append, List.mem_cons, reduceCtorEq, false_or] at hmem
        exact hcached bytes hmem

end Support

end SphincsFors.Security.HiddenBridge
