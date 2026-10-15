import SphincsFors.BridgeEncodingPrep
import SphincsFors.SecurityHiddenOutside
import SphincsFors.SecurityHiddenCost
import SphincsFors.SecuritySeedGuess
import SphincsFors.SecurityHiddenGraph

/-! The forced-failure comparison as a stateful simulation that records every guess made at an
unexposed coordinate. A stopped run either stops at a correct guess or coincides with the
comparison, so "stop or bad" is bounded by "some recorded guess is correct or bad" on the
comparison. Correct guesses are not charged here: they remain events of the joint law, so a
later potential can compose them multiplicatively with other first-hit events. -/

open OracleComp OracleSpec ENNReal

namespace SphincsFors.Security.HiddenDebt

open HiddenOutside HiddenReveal

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
attribute [local instance] Classical.propDecidable

variable {D R A ι : Type} [Fintype ι] [SampleableType R]
noncomputable local instance hiddenDebtDecEqInput : DecidableEq D := Classical.decEq _
noncomputable local instance hiddenDebtDecEqCoordinate : DecidableEq ι := Classical.decEq _

/-- Exposed coordinates, the outside cache, and the guesses made at unexposed coordinates. -/
structure DebtState (D R ι : Type) where
  known : Knowledge ι
  cache : Cache D R
  guesses : List (ι × Digest)

/-- Exposing a coordinate with a given value. -/
noncomputable def DebtState.expose (state : DebtState D R ι) (coordinate : ι) (value : Digest) : DebtState D R ι :=
  { state with known := state.known.cacheQuery coordinate value }

/-- Recording a guess. -/
def DebtState.record (state : DebtState D R ι) (guess : ι × Digest) : DebtState D R ι :=
  { state with guesses := guess :: state.guesses }

/-- An ordinary outside read from a debt state. -/
noncomputable def readOutside (bytes : D) (state : DebtState D R ι) : ProbComp (R × DebtState D R ι) :=
  (fun result => (result.1, { state with cache := result.2 })) <$> outsideRead bytes state.cache

/-- The comparison step with a fixed hidden table: reveals and canonical row continuations read
the table, while a row query at an unexposed coordinate records its guess and is answered by a
fresh outside read, whether or not the guess is correct. -/
noncomputable def fixedStep (model : HiddenRows.Model D R A ι) (table : ι → Digest) :
    QueryImpl (HiddenRows.SourceSpec D R ι) (StateT (DebtState D R ι) ProbComp)
  | .inl draw => fun state => (fun value => (value, state)) <$> (liftM (unifSpec.query draw) : ProbComp _)
  | .inr (.inr coordinate) => fun state =>
      pure (table coordinate, state.expose coordinate (table coordinate))
  | .inr (.inl bytes) => fun state =>
      match model.parse bytes with
      | none => readOutside bytes state
      | some query => match state.known (model.incoming query.1) with
        | none => readOutside bytes (state.record (model.incoming query.1, query.2))
        | some canonical =>
            if query.2 = canonical then
              pure (model.combine query.1 (table (model.outgoing query.1)),
                state.expose (model.outgoing query.1) (table (model.outgoing query.1)))
            else readOutside bytes state

noncomputable def fixedRun {α : Type} (model : HiddenRows.Model D R A ι) (table : ι → Digest)
    (computation : OracleComp (HiddenRows.SourceSpec D R ι) α) (state : DebtState D R ι) :
    ProbComp (α × DebtState D R ι) :=
  (simulateQ (fixedStep model table) computation).run state

omit [Fintype ι] in
theorem fixedRun_pure {α : Type} (model : HiddenRows.Model D R A ι) (table : ι → Digest) (value : α)
    (state : DebtState D R ι) : fixedRun model table (pure value) state = pure (value, state) := rfl

omit [Fintype ι] in
theorem fixedRun_query_bind {α : Type} (model : HiddenRows.Model D R A ι) (table : ι → Digest)
    (input : (HiddenRows.SourceSpec D R ι).Domain)
    (next : (HiddenRows.SourceSpec D R ι).Range input → OracleComp (HiddenRows.SourceSpec D R ι) α)
    (state : DebtState D R ι) :
    fixedRun model table (liftM ((HiddenRows.SourceSpec D R ι).query input) >>= next) state =
      (fixedStep model table input).run state >>= fun result => fixedRun model table (next result.1) result.2 := by
  simp only [fixedRun, simulateQ_bind, simulateQ_spec_query, StateT.run_bind]

omit [Fintype ι] in
theorem fixedStep_unparsed (model : HiddenRows.Model D R A ι) (table : ι → Digest) (bytes : D)
    (state : DebtState D R ι) (hp : model.parse bytes = none) :
    (fixedStep model table (.inr (.inl bytes))).run state = readOutside bytes state := by
  simp only [fixedStep, StateT.run, hp]

omit [Fintype ι] in
theorem fixedStep_guess (model : HiddenRows.Model D R A ι) (table : ι → Digest) (bytes : D)
    (state : DebtState D R ι) (query : A × Digest) (hp : model.parse bytes = some query)
    (hk : state.known (model.incoming query.1) = none) :
    (fixedStep model table (.inr (.inl bytes))).run state =
      readOutside bytes (state.record (model.incoming query.1, query.2)) := by
  simp only [fixedStep, StateT.run, hp, hk]

omit [Fintype ι] in
theorem fixedStep_canonical (model : HiddenRows.Model D R A ι) (table : ι → Digest) (bytes : D)
    (state : DebtState D R ι) (query : A × Digest) (hp : model.parse bytes = some query)
    (canonical : Digest) (hk : state.known (model.incoming query.1) = some canonical)
    (heq : query.2 = canonical) :
    (fixedStep model table (.inr (.inl bytes))).run state =
      pure (model.combine query.1 (table (model.outgoing query.1)),
        state.expose (model.outgoing query.1) (table (model.outgoing query.1))) := by
  simp only [fixedStep, StateT.run, hp, hk, heq, if_true]

omit [Fintype ι] in
theorem fixedStep_other (model : HiddenRows.Model D R A ι) (table : ι → Digest) (bytes : D)
    (state : DebtState D R ι) (query : A × Digest) (hp : model.parse bytes = some query)
    (canonical : Digest) (hk : state.known (model.incoming query.1) = some canonical)
    (hne : query.2 ≠ canonical) :
    (fixedStep model table (.inr (.inl bytes))).run state = readOutside bytes state := by
  simp only [fixedStep, StateT.run, hp, hk, hne, if_false]

omit [Fintype ι] in
theorem fixedStep_draw (model : HiddenRows.Model D R A ι) (table : ι → Digest) (draw : unifSpec.Domain)
    (state : DebtState D R ι) :
    (fixedStep model table (.inl draw)).run state =
      (fun value => (value, state)) <$> (liftM (unifSpec.query draw) : ProbComp _) := rfl

omit [Fintype ι] in
theorem fixedStep_reveal (model : HiddenRows.Model D R A ι) (table : ι → Digest) (coordinate : ι)
    (state : DebtState D R ι) :
    (fixedStep model table (.inr (.inr coordinate))).run state =
      pure (table coordinate, state.expose coordinate (table coordinate)) := rfl

/-- Some recorded guess names the table's value. -/
def CorrectGuess (table : ι → Digest) (state : DebtState D R ι) : Prop :=
  ∃ guess ∈ state.guesses, table guess.1 = guess.2

/-- The table extends the exposed coordinates. -/
def Agrees (known : Knowledge ι) (table : ι → Digest) : Prop :=
  ∀ coordinate value, known coordinate = some value → table coordinate = value

omit [Fintype ι] in
theorem Agrees.cacheQuery {known : Knowledge ι} {table : ι → Digest} (h : Agrees known table)
    (coordinate : ι) : Agrees (known.cacheQuery coordinate (table coordinate)) table := by
  intro other value hother
  by_cases heq : other = coordinate
  · subst other
    rw [QueryCache.cacheQuery_self] at hother
    exact Option.some.inj hother
  · rw [QueryCache.cacheQuery_of_ne _ _ heq] at hother
    exact h other value hother

omit [Fintype ι] in
theorem stopped_query_bind {α : Type} (model : HiddenRows.Model D R A ι) (table : ι → Digest)
    (input : (HiddenRows.SourceSpec D R ι).Domain)
    (next : (HiddenRows.SourceSpec D R ι).Range input → OracleComp (HiddenRows.SourceSpec D R ι) α)
    (known : Knowledge ι) (cache : Cache D R) :
    stopped model table (liftM ((HiddenRows.SourceSpec D R ι).query input) >>= next) known cache =
      stoppedStep model table input (fun value => stopped model table (next value)) known cache := by
  unfold stopped
  rw [OracleComp.construct_query_bind]

omit [Fintype ι] in
theorem stoppedStep_unparsed {α : Type} (model : HiddenRows.Model D R A ι) (table : ι → Digest) (bytes : D)
    (next : R → Knowledge ι → Cache D R → ProbComp (Option (α × Cache D R)))
    (known : Knowledge ι) (cache : Cache D R) (hp : model.parse bytes = none) :
    stoppedStep model table (.inr (.inl bytes)) next known cache =
      outsideRead bytes cache >>= fun result => next result.1 known result.2 := by
  simp only [stoppedStep, hp]

omit [Fintype ι] in
theorem stoppedStep_stop {α : Type} (model : HiddenRows.Model D R A ι) (table : ι → Digest) (bytes : D)
    (next : R → Knowledge ι → Cache D R → ProbComp (Option (α × Cache D R)))
    (known : Knowledge ι) (cache : Cache D R) (query : A × Digest) (hp : model.parse bytes = some query)
    (hstop : known (model.incoming query.1) = none ∧ query.2 = table (model.incoming query.1)) :
    stoppedStep model table (.inr (.inl bytes)) next known cache = pure none := by
  simp only [stoppedStep, hp]
  rw [if_pos hstop]

omit [Fintype ι] in
theorem stoppedStep_miss {α : Type} (model : HiddenRows.Model D R A ι) (table : ι → Digest) (bytes : D)
    (next : R → Knowledge ι → Cache D R → ProbComp (Option (α × Cache D R)))
    (known : Knowledge ι) (cache : Cache D R) (query : A × Digest) (hp : model.parse bytes = some query)
    (hmiss : query.2 ≠ table (model.incoming query.1)) :
    stoppedStep model table (.inr (.inl bytes)) next known cache =
      outsideRead bytes cache >>= fun result => next result.1 known result.2 := by
  simp only [stoppedStep, hp]
  rw [if_neg (fun h => hmiss h.2), if_neg hmiss]

omit [Fintype ι] in
theorem stoppedStep_canonical {α : Type} (model : HiddenRows.Model D R A ι) (table : ι → Digest) (bytes : D)
    (next : R → Knowledge ι → Cache D R → ProbComp (Option (α × Cache D R)))
    (known : Knowledge ι) (cache : Cache D R) (query : A × Digest) (hp : model.parse bytes = some query)
    (hknown : known (model.incoming query.1) ≠ none) (hhit : query.2 = table (model.incoming query.1)) :
    stoppedStep model table (.inr (.inl bytes)) next known cache =
      next (model.combine query.1 (table (model.outgoing query.1)))
        (known.cacheQuery (model.outgoing query.1) (table (model.outgoing query.1))) cache := by
  simp only [stoppedStep, hp]
  rw [if_neg (fun h => hknown h.1), if_pos hhit]

omit [Fintype ι] in
/-- Recorded guesses are never forgotten. -/
theorem fixedRun_guesses_mono {α : Type} (model : HiddenRows.Model D R A ι) (table : ι → Digest)
    (computation : OracleComp (HiddenRows.SourceSpec D R ι) α) (state : DebtState D R ι)
    (result : α × DebtState D R ι) (hresult : result ∈ support (fixedRun model table computation state)) :
    ∀ guess ∈ state.guesses, guess ∈ result.2.guesses := by
  induction computation using OracleComp.inductionOn generalizing state with
  | pure value =>
      rw [fixedRun_pure, support_pure, Set.mem_singleton_iff] at hresult
      subst result
      exact fun _ h => h
  | query_bind input next ih =>
      rw [fixedRun_query_bind, mem_support_bind_iff] at hresult
      obtain ⟨first, hfirst, hrest⟩ := hresult
      intro guess hguess
      refine ih first.1 first.2 hrest guess ?_
      rcases input with draw | (bytes | coordinate)
      · rw [fixedStep_draw, support_map, Set.mem_image] at hfirst
        obtain ⟨_, _, rfl⟩ := hfirst
        exact hguess
      · have hread : ∀ base : DebtState D R ι,
            first ∈ support (readOutside bytes base) → first.2.guesses = base.guesses := by
          intro base h
          simp only [readOutside, support_map, Set.mem_image] at h
          obtain ⟨_, _, rfl⟩ := h
          rfl
        cases hp : model.parse bytes with
        | none =>
            rw [fixedStep_unparsed model table bytes state hp] at hfirst
            rw [hread _ hfirst]
            exact hguess
        | some query =>
            cases hk : state.known (model.incoming query.1) with
            | none =>
                rw [fixedStep_guess model table bytes state query hp hk] at hfirst
                rw [hread _ hfirst]
                exact List.mem_cons_of_mem _ hguess
            | some canonical =>
                by_cases heq : query.2 = canonical
                · rw [fixedStep_canonical model table bytes state query hp canonical hk heq, support_pure,
                    Set.mem_singleton_iff] at hfirst
                  subst first
                  exact hguess
                · rw [fixedStep_other model table bytes state query hp canonical hk heq] at hfirst
                  rw [hread _ hfirst]
                  exact hguess
      · rw [fixedStep_reveal, support_pure, Set.mem_singleton_iff] at hfirst
        subst first
        exact hguess

omit [Fintype ι] in
/-- **Stopping coupling.** A stopped run stops or produces a bad result only if the guess-recording
comparison records a correct guess or produces the same bad result. -/
theorem stopped_le_fixedRun {α : Type} (model : HiddenRows.Model D R A ι) (table : ι → Digest)
    (computation : OracleComp (HiddenRows.SourceSpec D R ι) α) (bad : α × Cache D R → Prop)
    (state : DebtState D R ι) (hagree : Agrees state.known table) :
    Pr[StopOr bad | stopped model table computation state.known state.cache] ≤
      Pr[fun result => CorrectGuess table result.2 ∨ bad (result.1, result.2.cache) |
        fixedRun model table computation state] := by
  induction computation using OracleComp.inductionOn generalizing state with
  | pure value =>
      simp only [stopped, OracleComp.construct_pure, fixedRun_pure, probEvent_pure, StopOr]
      split_ifs <;> simp_all
  | query_bind input next ih =>
      rw [stopped_query_bind, fixedRun_query_bind]
      rcases input with draw | (bytes | coordinate)
      · rw [fixedStep_draw]
        simp only [stoppedStep, bind_map_left, probEvent_bind_eq_tsum]
        refine ENNReal.tsum_le_tsum fun value => mul_le_mul' le_rfl ?_
        exact ih value state hagree
      · have hreadStep : ∀ base : DebtState D R ι, base.known = state.known → base.cache = state.cache →
            Pr[StopOr bad | outsideRead bytes state.cache >>= fun result =>
              stopped model table (next result.1) state.known result.2] ≤
            Pr[fun result => CorrectGuess table result.2 ∨ bad (result.1, result.2.cache) |
              readOutside bytes base >>= fun result => fixedRun model table (next result.1) result.2] := by
          intro base hknown hcache
          simp only [readOutside, bind_map_left, probEvent_bind_eq_tsum, hcache]
          refine ENNReal.tsum_le_tsum fun result => mul_le_mul' le_rfl ?_
          have h := ih result.1 { base with cache := result.2 } (by simpa [hknown] using hagree)
          simpa [hknown] using h
        cases hp : model.parse bytes with
        | none =>
            rw [fixedStep_unparsed model table bytes state hp, stoppedStep_unparsed model table bytes _ _ _ hp]
            exact hreadStep state rfl rfl
        | some query =>
            cases hk : state.known (model.incoming query.1) with
            | none =>
                rw [fixedStep_guess model table bytes state query hp hk]
                by_cases hguess : query.2 = table (model.incoming query.1)
                · rw [stoppedStep_stop model table bytes _ _ _ query hp ⟨hk, hguess⟩, probEvent_pure]
                  simp only [StopOr, if_true]
                  refine le_of_eq (Eq.symm ?_)
                  rw [probEvent_eq_one_iff]
                  refine ⟨probFailure_eq_zero, fun result hresult => Or.inl ?_⟩
                  rw [mem_support_bind_iff] at hresult
                  obtain ⟨first, hfirst, hrest⟩ := hresult
                  have hstate : first.2.guesses = (model.incoming query.1, query.2) :: state.guesses := by
                    simp only [readOutside, support_map, Set.mem_image] at hfirst
                    obtain ⟨read, _, hread⟩ := hfirst
                    rw [← hread]
                    rfl
                  have hkeep := fixedRun_guesses_mono model table _ first.2 result hrest
                  exact ⟨_, hkeep _ (by rw [hstate]; exact List.mem_cons_self), hguess.symm⟩
                · rw [stoppedStep_miss model table bytes _ _ _ query hp hguess]
                  exact hreadStep _ rfl rfl
            | some canonical =>
                have hcanon : table (model.incoming query.1) = canonical := hagree _ _ hk
                by_cases heq : query.2 = canonical
                · rw [fixedStep_canonical model table bytes state query hp canonical hk heq, pure_bind,
                    stoppedStep_canonical model table bytes _ _ _ query hp (by simp [hk]) (heq.trans hcanon.symm)]
                  exact ih _ (state.expose (model.outgoing query.1) (table (model.outgoing query.1)))
                    (hagree.cacheQuery _)
                · rw [fixedStep_other model table bytes state query hp canonical hk heq,
                    stoppedStep_miss model table bytes _ _ _ query hp (fun h => heq (h.trans hcanon))]
                  exact hreadStep state rfl rfl
      · rw [fixedStep_reveal, pure_bind]
        simp only [stoppedStep]
        exact ih _ (state.expose coordinate (table coordinate)) (hagree.cacheQuery coordinate)

/-! ### Deferred sampling: lazy reveals -/

/-- Lazily sample a coordinate into the exposed cache of a debt state. -/
noncomputable def sampleCoordinate (coordinate : ι) (state : DebtState D R ι) :
    ProbComp (Digest × DebtState D R ι) :=
  (fun result => (result.1, { state with known := result.2 })) <$>
    (randomOracle (spec := ι →ₒ Digest) coordinate).run state.known

/-- The comparison with lazily sampled reveals. Guesses are recorded and never checked. -/
noncomputable def lazyStep (model : HiddenRows.Model D R A ι) :
    QueryImpl (HiddenRows.SourceSpec D R ι) (StateT (DebtState D R ι) ProbComp)
  | .inl draw => fun state => (fun value => (value, state)) <$> (liftM (unifSpec.query draw) : ProbComp _)
  | .inr (.inr coordinate) => fun state => sampleCoordinate coordinate state
  | .inr (.inl bytes) => fun state =>
      match model.parse bytes with
      | none => readOutside bytes state
      | some query => match state.known (model.incoming query.1) with
        | none => readOutside bytes (state.record (model.incoming query.1, query.2))
        | some canonical =>
            if query.2 = canonical then
              (fun result => (model.combine query.1 result.1, result.2)) <$>
                sampleCoordinate (model.outgoing query.1) state
            else readOutside bytes state

noncomputable def lazyRun {α : Type} (model : HiddenRows.Model D R A ι)
    (computation : OracleComp (HiddenRows.SourceSpec D R ι) α) (state : DebtState D R ι) :
    ProbComp (α × DebtState D R ι) :=
  (simulateQ (lazyStep model) computation).run state

omit [Fintype ι] in
theorem lazyRun_pure {α : Type} (model : HiddenRows.Model D R A ι) (value : α) (state : DebtState D R ι) :
    lazyRun model (pure value) state = pure (value, state) := rfl

omit [Fintype ι] in
theorem lazyRun_query_bind {α : Type} (model : HiddenRows.Model D R A ι)
    (input : (HiddenRows.SourceSpec D R ι).Domain)
    (next : (HiddenRows.SourceSpec D R ι).Range input → OracleComp (HiddenRows.SourceSpec D R ι) α)
    (state : DebtState D R ι) :
    lazyRun model (liftM ((HiddenRows.SourceSpec D R ι).query input) >>= next) state =
      (lazyStep model input).run state >>= fun result => lazyRun model (next result.1) result.2 := by
  simp only [lazyRun, simulateQ_bind, simulateQ_spec_query, StateT.run_bind]

omit [Fintype ι] in
theorem lazyStep_draw (model : HiddenRows.Model D R A ι) (draw : unifSpec.Domain) (state : DebtState D R ι) :
    (lazyStep model (.inl draw)).run state =
      (fun value => (value, state)) <$> (liftM (unifSpec.query draw) : ProbComp _) := rfl

omit [Fintype ι] in
theorem lazyStep_reveal (model : HiddenRows.Model D R A ι) (coordinate : ι) (state : DebtState D R ι) :
    (lazyStep model (.inr (.inr coordinate))).run state = sampleCoordinate coordinate state := rfl

omit [Fintype ι] in
theorem lazyStep_unparsed (model : HiddenRows.Model D R A ι) (bytes : D) (state : DebtState D R ι)
    (hp : model.parse bytes = none) :
    (lazyStep model (.inr (.inl bytes))).run state = readOutside bytes state := by
  simp only [lazyStep, StateT.run, hp]

omit [Fintype ι] in
theorem lazyStep_guess (model : HiddenRows.Model D R A ι) (bytes : D) (state : DebtState D R ι)
    (query : A × Digest) (hp : model.parse bytes = some query)
    (hk : state.known (model.incoming query.1) = none) :
    (lazyStep model (.inr (.inl bytes))).run state =
      readOutside bytes (state.record (model.incoming query.1, query.2)) := by
  simp only [lazyStep, StateT.run, hp, hk]

omit [Fintype ι] in
theorem lazyStep_canonical (model : HiddenRows.Model D R A ι) (bytes : D) (state : DebtState D R ι)
    (query : A × Digest) (hp : model.parse bytes = some query) (canonical : Digest)
    (hk : state.known (model.incoming query.1) = some canonical) (heq : query.2 = canonical) :
    (lazyStep model (.inr (.inl bytes))).run state =
      (fun result => (model.combine query.1 result.1, result.2)) <$>
        sampleCoordinate (model.outgoing query.1) state := by
  simp only [lazyStep, StateT.run, hp, hk, heq, if_true]

omit [Fintype ι] in
theorem lazyStep_other (model : HiddenRows.Model D R A ι) (bytes : D) (state : DebtState D R ι)
    (query : A × Digest) (hp : model.parse bytes = some query) (canonical : Digest)
    (hk : state.known (model.incoming query.1) = some canonical) (hne : query.2 ≠ canonical) :
    (lazyStep model (.inr (.inl bytes))).run state = readOutside bytes state := by
  simp only [lazyStep, StateT.run, hp, hk, hne, if_false]

/-- Joint law of the completed table and a run. -/
noncomputable def withTable {α : Type} (run : (ι → Digest) → ProbComp α) (known : Knowledge ι) :
    ProbComp ((ι → Digest) × α) :=
  completion known >>= fun table => (fun result => (table, result)) <$> run table

omit [Fintype ι] [SampleableType R] in
theorem sampleCoordinate_expose (coordinate : ι) (state : DebtState D R ι) (result : Digest × DebtState D R ι)
    (hresult : result ∈ support (sampleCoordinate coordinate state)) :
    result.2 = state.expose coordinate result.1 := by
  simp only [sampleCoordinate, support_map, Set.mem_image] at hresult
  obtain ⟨sample, hsample, rfl⟩ := hresult
  cases hc : state.known coordinate with
  | none =>
      rw [QueryImpl.withCaching_run_none _ hc, support_map] at hsample
      obtain ⟨value, _, rfl⟩ := hsample
      rfl
  | some value =>
      rw [QueryImpl.withCaching_run_some _ hc, support_pure, Set.mem_singleton_iff] at hsample
      subst sample
      simp only [DebtState.expose]
      congr 1
      apply QueryCache.ext
      intro other
      by_cases heq : other = coordinate
      · subst other
        rw [QueryCache.cacheQuery_self, hc]
      · rw [QueryCache.cacheQuery_of_ne _ _ heq]

omit [Fintype ι] in
theorem randomOracle_known_support (known : Knowledge ι) (coordinate : ι) (result : Digest × Knowledge ι)
    (hresult : result ∈ support ((randomOracle (spec := ι →ₒ Digest) coordinate).run known)) :
    result.2 = known.cacheQuery coordinate result.1 := by
  cases hc : known coordinate with
  | none =>
      rw [QueryImpl.withCaching_run_none _ hc, support_map] at hresult
      obtain ⟨value, _, rfl⟩ := hresult
      rfl
  | some value =>
      rw [QueryImpl.withCaching_run_some _ hc, support_pure, Set.mem_singleton_iff] at hresult
      subst result
      apply QueryCache.ext
      intro other
      by_cases heq : other = coordinate
      · subst other
        simp only [QueryCache.cacheQuery_self, hc]
      · simp only [QueryCache.cacheQuery_of_ne _ _ heq]

omit [SampleableType R] in
/-- A reveal commutes with completion: the table value at a sampled coordinate. -/
theorem withTable_reveal {β : Type} (coordinate : ι) (state : DebtState D R ι)
    (continuation : Digest → DebtState D R ι → (ι → Digest) → ProbComp β) :
    𝒟[completion state.known >>= fun table =>
        continuation (table coordinate) (state.expose coordinate (table coordinate)) table] =
      𝒟[sampleCoordinate coordinate state >>= fun result =>
        completion result.2.known >>= continuation result.1 result.2] := by
  rw [completion_reveal state.known coordinate
    (fun value table => continuation value (state.expose coordinate value) table)]
  simp only [sampleCoordinate, bind_map_left]
  congr 1
  apply bind_congr_of_forall_mem_support
  intro sample hsample
  have hcache := randomOracle_known_support state.known coordinate sample hsample
  simp only [DebtState.expose, ← hcache]

omit [SampleableType R] in
/-- Steps that leave the exposed coordinates unchanged commute with completion. -/
theorem withTable_swap {β Y : Type} (step : ProbComp (Y × DebtState D R ι)) (state : DebtState D R ι)
    (hknown : ∀ result ∈ support step, result.2.known = state.known)
    (continuation : Y → DebtState D R ι → (ι → Digest) → ProbComp β) :
    𝒟[completion state.known >>= fun table => step >>= fun result => continuation result.1 result.2 table] =
      𝒟[step >>= fun result => completion result.2.known >>= continuation result.1 result.2] := by
  rw [evalDist_bind_bind_swap]
  congr 1
  apply bind_congr_of_forall_mem_support
  intro result hresult
  rw [hknown result hresult]

omit [Fintype ι] in
theorem readOutside_known (bytes : D) (state : DebtState D R ι) :
    ∀ result ∈ support (readOutside bytes state), result.2.known = state.known := by
  intro result hresult
  simp only [readOutside, support_map, Set.mem_image] at hresult
  obtain ⟨_, _, rfl⟩ := hresult
  rfl

/-- **Deferred sampling.** Completing the table first and running the fixed comparison has the
same joint law as the lazy comparison followed by completion of what remains unexposed. -/
theorem withTable_fixedRun {α : Type} (model : HiddenRows.Model D R A ι)
    (computation : OracleComp (HiddenRows.SourceSpec D R ι) α) (state : DebtState D R ι) :
    𝒟[withTable (fun table => fixedRun model table computation state) state.known] =
      𝒟[lazyRun model computation state >>= fun result =>
        (fun table => (table, result)) <$> completion result.2.known] := by
  induction computation using OracleComp.inductionOn generalizing state with
  | pure value =>
      simp only [withTable, fixedRun_pure, lazyRun_pure, map_pure, pure_bind]
      rw [map_eq_bind_pure_comp]
      rfl
  | query_bind input next ih =>
      simp only [withTable, fixedRun_query_bind, lazyRun_query_bind, map_bind]
      have hstep : ∀ (step : ProbComp ((HiddenRows.SourceSpec D R ι).Range input × DebtState D R ι)),
          (∀ result ∈ support step, result.2.known = state.known) →
          𝒟[completion state.known >>= fun table => step >>= fun result =>
              (fun r => (table, r)) <$> fixedRun model table (next result.1) result.2] =
            𝒟[step >>= fun result => lazyRun model (next result.1) result.2 >>= fun r =>
              (fun table => (table, r)) <$> completion r.2.known] := by
        intro step hknown
        refine (withTable_swap step state hknown
          (fun value after table => (fun r => (table, r)) <$> fixedRun model table (next value) after)).trans ?_
        apply evalDist_bind_congr'
        intro result
        exact ih result.1 result.2
      have hreveal : ∀ (coordinate : ι) (label : Digest → (HiddenRows.SourceSpec D R ι).Range input),
          𝒟[completion state.known >>= fun table =>
              (fun r => (table, r)) <$> fixedRun model table (next (label (table coordinate)))
                (state.expose coordinate (table coordinate))] =
            𝒟[sampleCoordinate coordinate state >>= fun result =>
              lazyRun model (next (label result.1)) result.2 >>= fun r =>
                (fun table => (table, r)) <$> completion r.2.known] := by
        intro coordinate label
        refine (withTable_reveal coordinate state
          (fun value after table => (fun r => (table, r)) <$> fixedRun model table (next (label value)) after)).trans ?_
        apply evalDist_bind_congr'
        intro result
        exact ih (label result.1) result.2
      rcases input with draw | (bytes | coordinate)
      · simp only [fixedStep_draw, lazyStep_draw]
        apply hstep
        intro result hresult
        rw [support_map, Set.mem_image] at hresult
        obtain ⟨_, _, rfl⟩ := hresult
        rfl
      · cases hp : model.parse bytes with
        | none =>
            simp only [fixedStep_unparsed (model := model) (bytes := bytes) (state := state) (hp := hp),
              lazyStep_unparsed model bytes state hp, bind_assoc]
            exact hstep _ (readOutside_known bytes state)
        | some query =>
            cases hk : state.known (model.incoming query.1) with
            | none =>
                simp only [fixedStep_guess (model := model) (bytes := bytes) (state := state) (query := query)
                  (hp := hp) (hk := hk), lazyStep_guess model bytes state query hp hk, bind_assoc]
                exact hstep _ (readOutside_known bytes _)
            | some canonical =>
                by_cases heq : query.2 = canonical
                · simp only [fixedStep_canonical (model := model) (bytes := bytes) (state := state)
                    (query := query) (hp := hp) (canonical := canonical) (hk := hk) (heq := heq), pure_bind,
                    lazyStep_canonical model bytes state query hp canonical hk heq, bind_map_left, bind_assoc]
                  exact hreveal (model.outgoing query.1) (model.combine query.1)
                · simp only [fixedStep_other (model := model) (bytes := bytes) (state := state) (query := query)
                    (hp := hp) (canonical := canonical) (hk := hk) (hne := heq),
                    lazyStep_other model bytes state query hp canonical hk heq, bind_assoc]
                  exact hstep _ (readOutside_known bytes state)
      · simp only [fixedStep_reveal, pure_bind, lazyStep_reveal, bind_assoc]
        exact hreveal coordinate id

end SphincsFors.Security.HiddenDebt
