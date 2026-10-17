import Sphincs.BridgeInterp

/-! Fixing the answer to an untargeted, unparsed outside input in advance commutes with the
interpreted lazy comparison: the lazy oracle would draw the same uniform value on first use.
The FORS potentials use this to treat the unknown blocks of partially queried digest pairs as
already sampled. -/

open OracleComp OracleSpec ENNReal

namespace Sphincs.Security.HiddenDebt

open HiddenCost HiddenBridge HiddenOutside HiddenReveal

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
attribute [local instance] Classical.propDecidable

variable {D R A ι : Type} [Fintype ι] [SampleableType R]
attribute [local instance] saturationDecEqInput saturationDecEqCoordinate
variable (tg : Targeting D R ι) (initial : Cache D R) (model : HiddenRows.Model D R A ι)

/-- Fix the answer to an outside input in advance. -/
noncomputable def presample (x : D) (state : DebtState D R ι) : ProbComp (DebtState D R ι) :=
  match state.cache x with
  | some _ => pure state
  | none => (fun u => state.store x u) <$> ($ᵗ R : ProbComp R)

omit [Fintype ι] in
theorem presample_cached (x : D) (state : DebtState D R ι) (v : R) (hc : state.cache x = some v) :
    presample x state = pure state := by
  simp only [presample, hc]

omit [Fintype ι] in
theorem presample_fresh (x : D) (state : DebtState D R ι) (hc : state.cache x = none) :
    presample x state = (fun u => state.store x u) <$> ($ᵗ R : ProbComp R) := by
  simp only [presample, hc]

omit [Fintype ι] [SampleableType R] in
theorem store_comm (state : DebtState D R ι) (x y : D) (hxy : x ≠ y) (u v : R) :
    (state.store x u).store y v = (state.store y v).store x u := by
  simp only [DebtState.store]
  congr 1
  exact Function.update_comm hxy _ _ _

omit [Fintype ι] [SampleableType R] in
theorem store_cache_ne (state : DebtState D R ι) (x y : D) (hxy : y ≠ x) (u : R) :
    (state.store x u).cache y = state.cache y := by
  simp only [DebtState.store, QueryCache.cacheQuery_of_ne _ _ hxy]

omit [Fintype ι] in
/-- Presampling commutes with an outside read. -/
theorem presample_readOutside {γ : Type} (x y : D) (state : DebtState D R ι)
    (next : R × DebtState D R ι → ProbComp γ) :
    𝒟[presample x state >>= fun s => readOutside y s >>= next] =
      𝒟[readOutside y state >>= fun r => presample x r.2 >>= fun s => next (r.1, s)] := by
  by_cases hxy : y = x
  · subst hxy
    cases hc : state.cache y with
    | some v =>
        simp only [presample_cached y state v hc, readOutside_cached y state v hc, pure_bind]
    | none =>
        rw [presample_fresh y state hc, readOutside_fresh y state hc, bind_map_left, bind_map_left]
        congr 1
        refine bind_congr fun u => ?_
        have hst : (state.store y u).cache y = some u := by simp [DebtState.store]
        simp only [readOutside_cached y _ u hst, presample_cached y _ u hst, pure_bind]
  · cases hcx : state.cache x with
    | some v =>
        rw [presample_cached x state v hcx, pure_bind]
        congr 1
        apply bind_congr_of_forall_mem_support
        intro r hr
        rcases readOutside_support y state r hr with h | ⟨_, h⟩
        · obtain ⟨a, b⟩ := r
          simp only at h
          subst h
          simp only [presample_cached x _ v hcx, pure_bind]
        · obtain ⟨a, b⟩ := r
          simp only at h
          subst h
          rw [presample_cached x _ v (by rw [store_cache_ne state y x (Ne.symm hxy) a]; exact hcx), pure_bind]
    | none =>
        rw [presample_fresh x state hcx, bind_map_left]
        cases hcy : state.cache y with
        | some v =>
            rw [readOutside_cached y state v hcy, pure_bind, presample_fresh x state hcx, bind_map_left]
            congr 1
            refine bind_congr fun u => ?_
            rw [readOutside_cached y _ v (by rw [store_cache_ne state x y hxy u]; exact hcy), pure_bind]
        | none =>
            rw [readOutside_fresh y state hcy, bind_map_left]
            have hL : ∀ u, readOutside y (state.store x u) =
                (fun v => (v, (state.store x u).store y v)) <$> ($ᵗ R : ProbComp R) := fun u =>
              readOutside_fresh y _ (by rw [store_cache_ne state x y hxy u]; exact hcy)
            simp only [hL, bind_map_left]
            rw [evalDist_bind_bind_swap]
            congr 1
            refine bind_congr fun v => ?_
            rw [presample_fresh x _ (by rw [store_cache_ne state y x (Ne.symm hxy) v]; exact hcx), bind_map_left]
            refine bind_congr fun u => ?_
            rw [store_comm state x y (Ne.symm hxy) u v]

/-! ### Untargeted inputs do not change the hit state -/

omit [Fintype ι] [SampleableType R] in
theorem debts_store_untargeted (state : DebtState D R ι) (x : D) (u : R) (hk : tg.kind x = .none)
    (coordinate : ι) : debts tg initial (state.store x u) coordinate = debts tg initial state coordinate := by
  ext value
  simp only [debts, DebtState.store, Set.mem_union, Set.mem_setOf_eq]
  refine or_congr Iff.rfl ⟨?_, ?_⟩
  · rintro ⟨input, out, hcache, hinit, hkind, htrunc⟩
    have hne : input ≠ x := by rintro rfl; rw [hk] at hkind; cases hkind
    exact ⟨input, out, by rwa [QueryCache.cacheQuery_of_ne _ _ hne] at hcache, hinit, hkind, htrunc⟩
  · rintro ⟨input, out, hcache, hinit, hkind, htrunc⟩
    have hne : input ≠ x := by rintro rfl; rw [hk] at hkind; cases hkind
    exact ⟨input, out, by rwa [QueryCache.cacheQuery_of_ne _ _ hne], hinit, hkind, htrunc⟩

omit [Fintype ι] [SampleableType R] in
theorem realized_store_untargeted (state : DebtState D R ι) (x : D) (u : R) (hk : tg.kind x = .none) :
    Realized tg initial (state.store x u) ↔ Realized tg initial state := by
  have hknown : (state.store x u).known = state.known := rfl
  unfold Realized
  simp only [debts_store_untargeted tg initial state x u hk, hknown]
  refine or_congr ⟨?_, ?_⟩ Iff.rfl
  · rintro ⟨input, out, value, hcache, hinit, hkind, htrunc⟩
    have hne : input ≠ x := by rintro rfl; rw [hk] at hkind; cases hkind
    exact ⟨input, out, value, by simpa [DebtState.store, QueryCache.cacheQuery_of_ne _ _ hne] using hcache,
      hinit, hkind, htrunc⟩
  · rintro ⟨input, out, value, hcache, hinit, hkind, htrunc⟩
    have hne : input ≠ x := by rintro rfl; rw [hk] at hkind; cases hkind
    exact ⟨input, out, value, by simpa [DebtState.store, QueryCache.cacheQuery_of_ne _ _ hne] using hcache,
      hinit, hkind, htrunc⟩

omit [Fintype ι] in
theorem realized_presample (x : D) (hk : tg.kind x = .none) (state : DebtState D R ι) :
    ∀ s ∈ support (presample x state), Realized tg initial s ↔ Realized tg initial state := by
  intro s hs
  cases hc : state.cache x with
  | some v =>
      rw [presample_cached x state v hc, support_pure, Set.mem_singleton_iff] at hs
      rw [hs]
  | none =>
      rw [presample_fresh x state hc, support_map] at hs
      obtain ⟨u, _, rfl⟩ := hs
      exact realized_store_untargeted tg initial state x u hk

/-! ### Commuting with every comparison step -/

omit [Fintype ι] in
theorem presample_known (x : D) (state : DebtState D R ι) :
    ∀ s ∈ support (presample x state), s.known = state.known ∧ s.guesses = state.guesses := by
  intro s hs
  cases hc : state.cache x with
  | some v =>
      rw [presample_cached x state v hc, support_pure, Set.mem_singleton_iff] at hs
      rw [hs]
      exact ⟨rfl, rfl⟩
  | none =>
      rw [presample_fresh x state hc, support_map] at hs
      obtain ⟨u, _, rfl⟩ := hs
      exact ⟨rfl, rfl⟩

omit [Fintype ι] in
theorem presample_record (x : D) (state : DebtState D R ι) (guess : ι × Digest) :
    presample x (state.record guess) = (fun s => s.record guess) <$> presample x state := by
  cases hc : state.cache x with
  | some v =>
      rw [presample_cached x (state.record guess) v hc, presample_cached x state v hc, map_pure]
  | none =>
      rw [presample_fresh x (state.record guess) hc, presample_fresh x state hc, Functor.map_map]
      rfl

omit [Fintype ι] in
theorem presample_setKnown (x : D) (state : DebtState D R ι) (known : Knowledge ι) :
    presample x { state with known := known } = (fun s => { s with known := known }) <$> presample x state := by
  cases hc : state.cache x with
  | some v =>
      rw [presample_cached x { state with known := known } v hc, presample_cached x state v hc, map_pure]
  | none =>
      rw [presample_fresh x { state with known := known } hc, presample_fresh x state hc, Functor.map_map]
      rfl

omit [Fintype ι] in
theorem presample_sampleCoordinate {γ : Type} (x : D) (coordinate : ι) (state : DebtState D R ι)
    (next : Digest × DebtState D R ι → ProbComp γ) :
    𝒟[presample x state >>= fun s => sampleCoordinate coordinate s >>= next] =
      𝒟[sampleCoordinate coordinate state >>= fun r => presample x r.2 >>= fun s => next (r.1, s)] := by
  have hstep : ∀ s ∈ support (presample x state), sampleCoordinate coordinate s =
      (fun r => (r.1, { s with known := r.2 })) <$>
        (randomOracle (spec := ι →ₒ Digest) coordinate).run state.known := by
    intro s hs
    rw [sampleCoordinate, (presample_known x state s hs).1]
  have hcongr : (presample x state >>= fun s => sampleCoordinate coordinate s >>= next) =
      (presample x state >>= fun s => ((fun r => (r.1, { s with known := r.2 })) <$>
        (randomOracle (spec := ι →ₒ Digest) coordinate).run state.known) >>= next) :=
    bind_congr_of_forall_mem_support _ fun s hs => by rw [hstep s hs]
  rw [hcongr]
  simp only [sampleCoordinate, bind_map_left]
  rw [evalDist_bind_bind_swap]
  congr 1
  refine bind_congr fun r => ?_
  rw [presample_setKnown x state r.2, bind_map_left]

omit [Fintype ι] in
/-- Presampling commutes with an outside read after a deterministic update of the guesses. -/
theorem presample_readOutside_record {γ : Type} (x bytes : D) (state : DebtState D R ι) (guess : ι × Digest)
    (next : R × DebtState D R ι → ProbComp γ) :
    𝒟[presample x state >>= fun s => readOutside bytes (s.record guess) >>= next] =
      𝒟[readOutside bytes (state.record guess) >>= fun r => presample x r.2 >>= fun s => next (r.1, s)] := by
  rw [← presample_readOutside x bytes (state.record guess) next, presample_record, bind_map_left]

/-- The ordinary-query step, read off the exposed coordinates. -/
noncomputable def ordinaryStep (bytes : D) (known : Knowledge ι) (state : DebtState D R ι) :
    ProbComp (R × DebtState D R ι) :=
  match model.parse bytes with
  | none => readOutside bytes state
  | some query => match known (model.incoming query.1) with
    | none => readOutside bytes (state.record (model.incoming query.1, query.2))
    | some canonical =>
        if query.2 = canonical then
          (fun result => (model.combine query.1 result.1, result.2)) <$>
            sampleCoordinate (model.outgoing query.1) state
        else readOutside bytes state

omit [Fintype ι] in
theorem costStep_ordinary (bytes : D) (state : DebtState D R ι) :
    (costStep model (.inl (.inr (.inl bytes))) state : ProbComp (R × DebtState D R ι)) =
      ordinaryStep model bytes state.known state := by
  rw [costStep_inl]
  cases hp : model.parse bytes with
  | none =>
      simp only [ordinaryStep, hp]
      exact lazyStep_unparsed model bytes state hp
  | some query =>
      cases hk : state.known (model.incoming query.1) with
      | none =>
          simp only [ordinaryStep, hp, hk]
          exact lazyStep_guess model bytes state query hp hk
      | some canonical =>
          by_cases heq : query.2 = canonical
          · simp only [ordinaryStep, hp, hk, if_pos heq]
            exact lazyStep_canonical model bytes state query hp canonical hk heq
          · simp only [ordinaryStep, hp, hk, if_neg heq]
            exact lazyStep_other model bytes state query hp canonical hk heq

omit [Fintype ι] in
theorem presample_ordinaryStep {γ : Type} (x bytes : D) (state : DebtState D R ι)
    (next : R × DebtState D R ι → ProbComp γ) :
    𝒟[presample x state >>= fun s => ordinaryStep model bytes state.known s >>= next] =
      𝒟[ordinaryStep model bytes state.known state >>= fun r => presample x r.2 >>= fun s => next (r.1, s)] := by
  cases hp : model.parse bytes with
  | none =>
      simp only [ordinaryStep, hp]
      exact presample_readOutside x bytes state next
  | some query =>
      cases hk : state.known (model.incoming query.1) with
      | none =>
          simp only [ordinaryStep, hp, hk]
          exact presample_readOutside_record x bytes state _ next
      | some canonical =>
          by_cases heq : query.2 = canonical
          · simp only [ordinaryStep, hp, hk, if_pos heq, bind_map_left]
            exact presample_sampleCoordinate x _ state _
          · simp only [ordinaryStep, hp, hk, if_neg heq]
            exact presample_readOutside x bytes state next

omit [Fintype ι] in
theorem presample_indep {T γ : Type} (x : D) (state : DebtState D R ι) (query : ProbComp T)
    (next : T × DebtState D R ι → ProbComp γ) :
    𝒟[presample x state >>= fun s => ((fun v => (v, s)) <$> query) >>= next] =
      𝒟[((fun v => (v, state)) <$> query) >>= fun r => presample x r.2 >>= fun s => next (r.1, s)] := by
  simp only [bind_map_left]
  exact evalDist_bind_bind_swap _ _ _

omit [Fintype ι] in
theorem presample_costStep {γ : Type} (x : D) (input : (SourceCostSpec D R ι).Domain) (state : DebtState D R ι)
    (next : (SourceCostSpec D R ι).Range input × DebtState D R ι → ProbComp γ) :
    𝒟[presample x state >>= fun s => costStep model input s >>= next] =
      𝒟[costStep model input state >>= fun r => presample x r.2 >>= fun s => next (r.1, s)] := by
  rcases input with (draw | (bytes | coordinate)) | amount
  · exact presample_indep x state (liftM (unifSpec.query draw) : ProbComp _) next
  · have hcongr : (presample x state >>= fun s => costStep model (.inl (.inr (.inl bytes))) s >>= next) =
        (presample x state >>= fun s => ordinaryStep model bytes state.known s >>= next) :=
      bind_congr_of_forall_mem_support _ fun s hs => by
        rw [costStep_ordinary, (presample_known x state s hs).1]
    rw [hcongr, costStep_ordinary]
    exact presample_ordinaryStep model x bytes state next
  · change 𝒟[presample x state >>= fun s => sampleCoordinate coordinate s >>= next] =
      𝒟[sampleCoordinate coordinate state >>= fun r => presample x r.2 >>= fun s => next (r.1, s)]
    exact presample_sampleCoordinate x coordinate state next
  · change 𝒟[presample x state >>= fun s => (pure ((), s) : ProbComp _) >>= next] =
      𝒟[(pure ((), state) : ProbComp _) >>= fun r => presample x r.2 >>= fun s => next (r.1, s)]
    simp only [pure_bind]

omit [Fintype ι] in
/-- **Presampling an untargeted input commutes with the interpreter.** -/
theorem presample_interp (x : D) (hk : tg.kind x = .none) {α : Type}
    (computation : OracleComp (SourceCostSpec D R ι) α) :
    ∀ budget state, 𝒟[presample x state >>= fun s => interp tg initial model computation budget s] =
      𝒟[interp tg initial model computation budget state >>= fun out =>
        (fun s => (out.1, s)) <$> presample x out.2] := by
  induction computation using OracleComp.inductionOn with
  | pure value =>
      intro budget state
      simp only [interp_pure, pure_bind]
      rw [map_eq_bind_pure_comp]
      rfl
  | query_bind input next ih =>
      intro budget state
      simp only [interp_query_bind]
      split_ifs with hcost
      · set φ : Run D ι α → Run D ι α := fun run => (run.1, revealed input ++ run.2.1,
          recorded input ++ run.2.2.1, touch tg initial state input ++ run.2.2.2) with hφ
        have htouch : ∀ s ∈ support (presample x state),
            touch tg initial s input = touch tg initial state input := by
          intro s hs
          rcases input with (draw | (bytes | coordinate)) | amount
          · rfl
          · simp only [touch, realized_presample tg initial x hk state s hs]
          · rfl
          · rfl
        have hcongr : (presample x state >>= fun s => costStep model input s >>= fun result =>
            (fun out => ((out.1.1, revealed input ++ out.1.2.1, recorded input ++ out.1.2.2.1,
              touch tg initial s input ++ out.1.2.2.2), out.2)) <$>
                interp tg initial model (next result.1) (budget - sourceCost input) result.2) =
            (presample x state >>= fun s => costStep model input s >>= fun result =>
              (fun out => (φ out.1, out.2)) <$>
                interp tg initial model (next result.1) (budget - sourceCost input) result.2) :=
          bind_congr_of_forall_mem_support _ fun s hs => by rw [htouch s hs]
        rw [hcongr, presample_costStep model x input state, bind_assoc, evalDist_bind, evalDist_bind]
        congr 1
        funext result
        have hih := ih result.1 (budget - sourceCost input) result.2
        calc 𝒟[presample x result.2 >>= fun s => (fun out => (φ out.1, out.2)) <$>
              interp tg initial model (next result.1) (budget - sourceCost input) s]
            = (fun out => (φ out.1, out.2)) <$> 𝒟[presample x result.2 >>= fun s =>
                interp tg initial model (next result.1) (budget - sourceCost input) s] := by
              rw [← evalDist_map, map_bind]
          _ = (fun out => (φ out.1, out.2)) <$> 𝒟[interp tg initial model (next result.1)
                (budget - sourceCost input) result.2 >>= fun out => (fun s => (out.1, s)) <$> presample x out.2] := by
              rw [hih]
          _ = _ := by
              rw [← evalDist_map, map_bind, bind_map_left]
              simp only [Functor.map_map]
              rfl
      · simp only [pure_bind]
        rw [map_eq_bind_pure_comp]
        rfl

end Sphincs.Security.HiddenDebt
