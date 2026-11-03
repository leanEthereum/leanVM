import FORS.LazyRun.Presample

/-! Fixing the answer to an untargeted, unparsed outside input in advance commutes with the
interpreted lazy comparison: the lazy oracle would draw the same uniform value on first use. So
presampling such an input can only help a final value that is monotone in the cache. The
potentials use this for the digest calls of a pair: a query of one call of a new pair is treated as
a query of all its calls (`storeAll`, `interp_presample_new`). -/

open OracleComp OracleSpec ENNReal

namespace FORS.Security.HiddenDebt

variable [Params]

open HiddenCost HiddenBridge HiddenOutside HiddenReveal

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
attribute [local instance] Classical.propDecidable

variable {D R A ι : Type} [Fintype ι] [SampleableType R]
attribute [local instance] saturationDecEqCoordinate
variable (tg : Targeting D R ι) (initial : Cache D R) (model : HiddenRows.Model D R A ι)

/-- Fix the answer to an outside input in advance. -/
noncomputable def presample (x : D) (state : DebtState D R ι) : ProbComp (DebtState D R ι) :=
  match state.cache x with
  | some _ => pure state
  | none => (fun u => state.store x u) <$> ($ᵗ R : ProbComp R)

omit [Params] [Fintype ι] in
theorem presample_cached (x : D) (state : DebtState D R ι) (v : R) (hc : state.cache x = some v) :
    presample x state = pure state := by
  simp only [presample, hc]

omit [Params] [Fintype ι] in
theorem presample_fresh (x : D) (state : DebtState D R ι) (hc : state.cache x = none) :
    presample x state = (fun u => state.store x u) <$> ($ᵗ R : ProbComp R) := by
  simp only [presample, hc]

omit [Params] [Fintype ι] [SampleableType R] in
theorem store_comm (state : DebtState D R ι) (x y : D) (hxy : x ≠ y) (u v : R) :
    (state.store x u).store y v = (state.store y v).store x u := by
  simp only [DebtState.store]
  congr 1
  exact Function.update_comm hxy _ _ _

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

omit [Params] [Fintype ι] in
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

omit [Params] [Fintype ι] in
theorem presample_record (x : D) (state : DebtState D R ι) (guess : ι × Digest) :
    presample x (state.record guess) = (fun s => s.record guess) <$> presample x state := by
  cases hc : state.cache x with
  | some v =>
      rw [presample_cached x (state.record guess) v hc, presample_cached x state v hc, map_pure]
  | none =>
      rw [presample_fresh x (state.record guess) hc, presample_fresh x state hc, Functor.map_map]
      rfl

omit [Params] [Fintype ι] in
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

omit [Params] [Fintype ι] in
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

/-! ### Presampling only helps monotone final values -/

omit [Params] [Fintype ι] in
theorem presample_mass (x : D) (state : DebtState D R ι) :
    ∑' s, Pr[= s | presample x state] = 1 := by
  refine tsum_probOutput_eq_one' ?_
  cases hc : state.cache x with
  | some v => rw [presample_cached x state v hc]; simp
  | none => rw [presample_fresh x state hc]; simp

omit [Fintype ι] in
/-- A final value that can only grow when an untargeted input is presampled at the end. -/
theorem interp_presample_le (x : D) (hk : tg.kind x = .none) {α : Type}
    (computation : OracleComp (SourceCostSpec D R ι) α) (budget : ℕ) (state : DebtState D R ι)
    (F : Run D ι α × DebtState D R ι → ℝ≥0∞)
    (hF : ∀ out (s : DebtState D R ι), s ∈ support (presample x out.2) → F out ≤ F (out.1, s)) :
    ∑' out, Pr[= out | interp tg initial model computation budget state] * F out ≤
      ∑' s, Pr[= s | presample x state] *
        ∑' out, Pr[= out | interp tg initial model computation budget s] * F out := by
  have heq : ∑' s, Pr[= s | presample x state] *
      ∑' out, Pr[= out | interp tg initial model computation budget s] * F out =
      ∑' out, Pr[= out | interp tg initial model computation budget state >>= fun out =>
        (fun s => (out.1, s)) <$> presample x out.2] * F out := by
    rw [← tsum_probOutput_bind_mul]
    exact tsum_congr fun out => congrArg (· * _) (probOutput_congr rfl
      (presample_interp tg initial model x hk computation budget state))
  rw [heq, tsum_probOutput_bind_mul]
  refine ENNReal.tsum_le_tsum fun out => ?_
  by_cases hout : out ∈ support (interp tg initial model computation budget state)
  · refine mul_le_mul_right ?_ _
    rw [tsum_probOutput_map_mul]
    calc F out = ∑' s, Pr[= s | presample x out.2] * F out := by
          rw [ENNReal.tsum_mul_right, presample_mass, one_mul]
      _ ≤ _ := ENNReal.tsum_le_tsum fun s => by
          by_cases hs : s ∈ support (presample x out.2)
          · exact mul_le_mul_right (hF out s hs) _
          · rw [probOutput_eq_zero_of_not_mem_support hs, zero_mul, zero_mul]
  · rw [probOutput_eq_zero_of_not_mem_support hout, zero_mul, zero_mul]

omit [Fintype ι] in
/-- A value of the run alone is unchanged by presampling. -/
theorem interp_presample_eq (x : D) (hk : tg.kind x = .none) {α : Type}
    (computation : OracleComp (SourceCostSpec D R ι) α) (budget : ℕ) (state : DebtState D R ι)
    (F : Run D ι α → ℝ≥0∞) :
    ∑' s, Pr[= s | presample x state] *
        ∑' out, Pr[= out | interp tg initial model computation budget s] * F out.1 =
      ∑' out, Pr[= out | interp tg initial model computation budget state] * F out.1 := by
  have heq : ∑' s, Pr[= s | presample x state] *
      ∑' out, Pr[= out | interp tg initial model computation budget s] * F out.1 =
      ∑' out, Pr[= out | interp tg initial model computation budget state >>= fun out =>
        (fun s => (out.1, s)) <$> presample x out.2] * F out.1 := by
    rw [← tsum_probOutput_bind_mul]
    exact tsum_congr fun out => congrArg (· * _) (probOutput_congr rfl
      (presample_interp tg initial model x hk computation budget state))
  rw [heq, tsum_probOutput_bind_mul]
  refine tsum_congr fun out => ?_
  rw [tsum_probOutput_map_mul]
  simp only
  rw [ENNReal.tsum_mul_right, presample_mass, one_mul]

/-! ### Storing a family of inputs -/

/-- Store the answers `u` at the inputs `x`, in the order of the index. -/
noncomputable def storeAll : {n : ℕ} → (Fin n → D) → (Fin n → R) → DebtState D R ι → DebtState D R ι
  | 0, _, _, state => state
  | _ + 1, x, u, state => storeAll (Fin.tail x) (Fin.tail u) (state.store (x 0) (u 0))

omit [Params] [Fintype ι] [SampleableType R] in
theorem storeAll_succ {n : ℕ} (x : Fin (n + 1) → D) (u : Fin (n + 1) → R) (state : DebtState D R ι) :
    storeAll x u state = storeAll (Fin.tail x) (Fin.tail u) (state.store (x 0) (u 0)) := rfl

omit [Params] [Fintype ι] [SampleableType R] in
theorem storeAll_known : ∀ {n : ℕ} (x : Fin n → D) (u : Fin n → R) (state : DebtState D R ι),
    (storeAll x u state).known = state.known ∧ (storeAll x u state).guesses = state.guesses
  | 0, _, _, _ => ⟨rfl, rfl⟩
  | _ + 1, x, u, state => storeAll_known (Fin.tail x) (Fin.tail u) (state.store (x 0) (u 0))

omit [Params] [Fintype ι] [SampleableType R] in
/-- An input outside the family keeps its cache entry. -/
theorem storeAll_cache_other : ∀ {n : ℕ} (x : Fin n → D) (u : Fin n → R) (state : DebtState D R ι) (y : D),
    (∀ i, x i ≠ y) → (storeAll x u state).cache y = state.cache y
  | 0, _, _, _, _, _ => rfl
  | _ + 1, x, u, state, y, h => by
      have hne : y ≠ x 0 := fun e => h 0 e.symm
      rw [storeAll_succ, storeAll_cache_other (Fin.tail x) (Fin.tail u) _ y fun i => h i.succ]
      simp only [DebtState.store, QueryCache.cacheQuery_of_ne _ _ hne]

omit [Params] [Fintype ι] [SampleableType R] in
/-- An input of an injective family holds its answer. -/
theorem storeAll_cache_self : ∀ {n : ℕ} (x : Fin n → D), Function.Injective x → ∀ (u : Fin n → R)
    (state : DebtState D R ι) (i : Fin n), (storeAll x u state).cache (x i) = some (u i)
  | 0, _, _, _, _, i => i.elim0
  | _ + 1, x, hx, u, state, i => by
      rw [storeAll_succ]
      cases i using Fin.cases with
      | zero =>
          rw [storeAll_cache_other (Fin.tail x) (Fin.tail u) _ (x 0) fun j e => Fin.succ_ne_zero j (hx e)]
          simp [DebtState.store]
      | succ j =>
          exact storeAll_cache_self (Fin.tail x) (fun a b e => Fin.succ_injective _ (hx e)) (Fin.tail u) _ j

omit [Params] [Fintype ι] [SampleableType R] in
/-- **The order of the stores does not matter.** -/
theorem storeAll_perm {n : ℕ} (x : Fin n → D) (hx : Function.Injective x) (u : Fin n → R)
    (σ : Equiv.Perm (Fin n)) (state : DebtState D R ι) :
    storeAll (x ∘ σ) (u ∘ σ) state = storeAll x u state := by
  have hx' : Function.Injective (x ∘ σ) := hx.comp σ.injective
  have hcache : (storeAll (x ∘ σ) (u ∘ σ) state).cache = (storeAll x u state).cache := by
    funext y
    by_cases hy : ∃ j, x (σ j) = y
    · obtain ⟨j, rfl⟩ := hy
      have h1 : (storeAll (x ∘ σ) (u ∘ σ) state).cache (x (σ j)) = some (u (σ j)) :=
        storeAll_cache_self (x ∘ σ) hx' (u ∘ σ) state j
      exact h1.trans (storeAll_cache_self x hx u state (σ j)).symm
    · push Not at hy
      have hy' : ∀ i, x i ≠ y := fun i => by
        have h := hy (σ.symm i)
        rwa [σ.apply_symm_apply] at h
      exact (storeAll_cache_other (x ∘ σ) (u ∘ σ) state y hy).trans
        (storeAll_cache_other x u state y hy').symm
  obtain ⟨hk1, hg1⟩ := storeAll_known (x ∘ σ) (u ∘ σ) state
  obtain ⟨hk2, hg2⟩ := storeAll_known x u state
  cases h1 : storeAll (x ∘ σ) (u ∘ σ) state
  cases h2 : storeAll x u state
  rw [h1, h2] at hcache
  rw [h1] at hk1 hg1
  rw [h2] at hk2 hg2
  simp only at hcache hk1 hg1 hk2 hg2
  rw [hcache, hk1, hk2, hg1, hg2]

/-! ### Presampling a family of inputs -/

variable [Fintype R]

omit [Fintype ι] in
/-- The mean against a uniform answer as a normalized finite sum. -/
theorem tsum_uniform_eq (G : R → ℝ≥0∞) :
    ∑' v, Pr[= v | ($ᵗ R : ProbComp R)] * G v = (Fintype.card R : ℝ≥0∞)⁻¹ * ∑ v, G v := by
  simp only [probOutput_uniformSample]
  rw [ENNReal.tsum_mul_left, tsum_fintype]

omit [Fintype ι] in
/-- Presampling one fresh untargeted input helps a final value monotone under fresh stores. -/
theorem interp_presample_fresh_le (x : D) (hk : tg.kind x = .none) {α : Type}
    (computation : OracleComp (SourceCostSpec D R ι) α) (budget : ℕ) (state : DebtState D R ι)
    (hx : state.cache x = none) (F : Run D ι α × DebtState D R ι → ℝ≥0∞)
    (hF : ∀ out (y : D) (v : R), out.2.cache y = none → F out ≤ F (out.1, out.2.store y v)) :
    ∑' out, Pr[= out | interp tg initial model computation budget state] * F out ≤
      (Fintype.card R : ℝ≥0∞)⁻¹ * ∑ v, ∑' out, Pr[= out | interp tg initial model computation budget
        (state.store x v)] * F out := by
  refine le_trans (interp_presample_le tg initial model x hk computation budget state F fun out s hs => ?_) ?_
  · cases hc : out.2.cache x with
    | some w =>
        rw [presample_cached x out.2 w hc, support_pure, Set.mem_singleton_iff] at hs
        rw [hs]
    | none =>
        rw [presample_fresh x out.2 hc, support_map] at hs
        obtain ⟨v, _, rfl⟩ := hs
        exact hF out x v hc
  · rw [presample_fresh x state hx, tsum_probOutput_map_mul, tsum_uniform_eq]

omit [Fintype ι] in
/-- **Presampling an injective family of fresh untargeted inputs** helps a final value monotone
under fresh stores. -/
theorem interp_presampleAll_le {α : Type} (computation : OracleComp (SourceCostSpec D R ι) α) (budget : ℕ)
    (F : Run D ι α × DebtState D R ι → ℝ≥0∞)
    (hF : ∀ out (y : D) (v : R), out.2.cache y = none → F out ≤ F (out.1, out.2.store y v)) :
    ∀ {n : ℕ} (x : Fin n → D), Function.Injective x → (∀ i, tg.kind (x i) = .none) →
      ∀ state : DebtState D R ι, (∀ i, state.cache (x i) = none) →
        ∑' out, Pr[= out | interp tg initial model computation budget state] * F out ≤
          ((Fintype.card R : ℝ≥0∞) ^ n)⁻¹ * ∑ u : Fin n → R,
            ∑' out, Pr[= out | interp tg initial model computation budget (storeAll x u state)] * F out
  | 0, x, _, _, state, _ => by
      simp only [pow_zero, inv_one, one_mul]
      rw [Fintype.sum_unique]
      rfl
  | n + 1, x, hx, hk, state, hfresh => by
      have hxt : Function.Injective (Fin.tail x) := fun a b e => Fin.succ_injective _ (hx e)
      refine le_trans (interp_presample_fresh_le tg initial model (x 0) (hk 0) computation budget state
        (hfresh 0) F hF) ?_
      have hrest : ∀ v, ∑' out, Pr[= out | interp tg initial model computation budget (state.store (x 0) v)] * F out ≤
          ((Fintype.card R : ℝ≥0∞) ^ n)⁻¹ * ∑ w : Fin n → R, ∑' out, Pr[= out | interp tg initial model
            computation budget (storeAll (Fin.tail x) w (state.store (x 0) v))] * F out := fun v =>
        interp_presampleAll_le computation budget F hF (Fin.tail x) hxt (fun i => hk i.succ) _ fun i => by
          show (state.store (x 0) v).cache (x i.succ) = none
          rw [store_cache_ne state (x 0) _ (fun e => Fin.succ_ne_zero i (hx e))]
          exact hfresh i.succ
      calc (Fintype.card R : ℝ≥0∞)⁻¹ * ∑ v, ∑' out, Pr[= out | interp tg initial model computation budget
              (state.store (x 0) v)] * F out
          ≤ (Fintype.card R : ℝ≥0∞)⁻¹ * ∑ v, (((Fintype.card R : ℝ≥0∞) ^ n)⁻¹ * ∑ w : Fin n → R,
              ∑' out, Pr[= out | interp tg initial model computation budget
                (storeAll (Fin.tail x) w (state.store (x 0) v))] * F out) := by
            gcongr with v
            exact hrest v
        _ = ((Fintype.card R : ℝ≥0∞) ^ (n + 1))⁻¹ * ∑ v, ∑ w : Fin n → R,
              ∑' out, Pr[= out | interp tg initial model computation budget
                (storeAll x (Fin.cons v w) state)] * F out := by
            rw [← Finset.mul_sum, ← mul_assoc, pow_succ', ENNReal.mul_inv (Or.inr (by simp))
              (Or.inl (ENNReal.natCast_ne_top _))]
            rfl
        _ = _ := by
            congr 1
            rw [← Fintype.sum_prod_type']
            exact Fintype.sum_equiv (Fin.consEquiv fun _ => R) _ _ fun p => rfl

omit [Fintype ι] in
/-- **A query of one input of a fresh family.** The uniform answer at input `c` followed by the
run is at most the run after storing uniform answers at the whole family, for a final value monotone
under fresh stores. -/
theorem interp_presample_new {α : Type} {n : ℕ} (x : Fin n → D) (hx : Function.Injective x)
    (hk : ∀ i, tg.kind (x i) = .none) (c : Fin n) (next : R → OracleComp (SourceCostSpec D R ι) α)
    (budget : ℕ) (state : DebtState D R ι) (hfresh : ∀ i, state.cache (x i) = none)
    (F : Run D ι α × DebtState D R ι → ℝ≥0∞)
    (hF : ∀ out (y : D) (v : R), out.2.cache y = none → F out ≤ F (out.1, out.2.store y v)) :
    ∑' v, Pr[= v | ($ᵗ R : ProbComp R)] *
        ∑' out, Pr[= out | interp tg initial model (next v) budget (state.store (x c) v)] * F out ≤
      ((Fintype.card R : ℝ≥0∞) ^ n)⁻¹ * ∑ u : Fin n → R,
        ∑' out, Pr[= out | interp tg initial model (next (u c)) budget (storeAll x u state)] * F out := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by have := c.isLt; omega⟩
  set σ : Equiv.Perm (Fin (m + 1)) := Equiv.swap 0 c with hσ
  set x' : Fin (m + 1) → D := x ∘ σ with hx'
  have hx'inj : Function.Injective x' := hx.comp σ.injective
  have hx'0 : x' 0 = x c := by simp [hx', hσ]
  have hxt : Function.Injective (Fin.tail x') := fun a b e => Fin.succ_injective _ (hx'inj e)
  have hrest : ∀ v, ∑' out, Pr[= out | interp tg initial model (next v) budget (state.store (x c) v)] * F out ≤
      ((Fintype.card R : ℝ≥0∞) ^ m)⁻¹ * ∑ w : Fin m → R, ∑' out, Pr[= out | interp tg initial model
        (next v) budget (storeAll x' (Fin.cons v w) state)] * F out := by
    intro v
    rw [← hx'0]
    exact interp_presampleAll_le tg initial model (next v) budget F hF (Fin.tail x') hxt (fun i => hk _) _
      fun i => by
        show (state.store (x' 0) v).cache (x' i.succ) = none
        rw [store_cache_ne state (x' 0) _ (fun e => Fin.succ_ne_zero i (hx'inj e))]
        exact hfresh _
  rw [tsum_uniform_eq]
  calc (Fintype.card R : ℝ≥0∞)⁻¹ * ∑ v, ∑' out, Pr[= out | interp tg initial model (next v) budget
          (state.store (x c) v)] * F out
      ≤ (Fintype.card R : ℝ≥0∞)⁻¹ * ∑ v, (((Fintype.card R : ℝ≥0∞) ^ m)⁻¹ * ∑ w : Fin m → R,
          ∑' out, Pr[= out | interp tg initial model (next v) budget (storeAll x' (Fin.cons v w) state)] * F out) := by
        gcongr with v
        exact hrest v
    _ = ((Fintype.card R : ℝ≥0∞) ^ (m + 1))⁻¹ * ∑ u' : Fin (m + 1) → R,
          ∑' out, Pr[= out | interp tg initial model (next (u' 0)) budget (storeAll x' u' state)] * F out := by
        rw [← Finset.mul_sum, ← mul_assoc, pow_succ', ENNReal.mul_inv (Or.inr (by simp))
          (Or.inl (ENNReal.natCast_ne_top _))]
        congr 1
        rw [← Fintype.sum_prod_type']
        exact Fintype.sum_equiv (Fin.consEquiv fun _ => R) _ _ fun p => rfl
    _ = _ := by
        congr 1
        refine Fintype.sum_equiv (σ.arrowCongr (Equiv.refl R)) _ _ fun u' => ?_
        have hu : (σ.arrowCongr (Equiv.refl R)) u' ∘ σ = u' := by
          funext i
          simp [Equiv.arrowCongr_apply, hσ, Equiv.swap_apply_self]
        conv_lhs => rw [← hu]
        rw [storeAll_perm x hx _ σ state]
        congr 3

omit [Fintype ι] in
/-- Presampling one fresh untargeted input keeps a value of the run alone. -/
theorem interp_presample_fresh_eq (x : D) (hk : tg.kind x = .none) {α : Type}
    (computation : OracleComp (SourceCostSpec D R ι) α) (budget : ℕ) (state : DebtState D R ι)
    (hx : state.cache x = none) (F : Run D ι α → ℝ≥0∞) :
    ∑' out, Pr[= out | interp tg initial model computation budget state] * F out.1 =
      (Fintype.card R : ℝ≥0∞)⁻¹ * ∑ v, ∑' out, Pr[= out | interp tg initial model computation budget
        (state.store x v)] * F out.1 := by
  rw [← interp_presample_eq tg initial model x hk computation budget state F,
    presample_fresh x state hx, tsum_probOutput_map_mul, tsum_uniform_eq]

omit [Fintype ι] in
/-- **Presampling an injective family of fresh untargeted inputs** keeps a value of the run alone. -/
theorem interp_presampleAll_eq {α : Type} (computation : OracleComp (SourceCostSpec D R ι) α) (budget : ℕ)
    (F : Run D ι α → ℝ≥0∞) :
    ∀ {n : ℕ} (x : Fin n → D), Function.Injective x → (∀ i, tg.kind (x i) = .none) →
      ∀ state : DebtState D R ι, (∀ i, state.cache (x i) = none) →
        ∑' out, Pr[= out | interp tg initial model computation budget state] * F out.1 =
          ((Fintype.card R : ℝ≥0∞) ^ n)⁻¹ * ∑ u : Fin n → R,
            ∑' out, Pr[= out | interp tg initial model computation budget (storeAll x u state)] * F out.1
  | 0, x, _, _, state, _ => by
      simp only [pow_zero, inv_one, one_mul]
      rw [Fintype.sum_unique]
      rfl
  | n + 1, x, hx, hk, state, hfresh => by
      have hxt : Function.Injective (Fin.tail x) := fun a b e => Fin.succ_injective _ (hx e)
      rw [interp_presample_fresh_eq tg initial model (x 0) (hk 0) computation budget state (hfresh 0) F]
      have hrest : ∀ v, ∑' out, Pr[= out | interp tg initial model computation budget (state.store (x 0) v)] * F out.1 =
          ((Fintype.card R : ℝ≥0∞) ^ n)⁻¹ * ∑ w : Fin n → R, ∑' out, Pr[= out | interp tg initial model
            computation budget (storeAll (Fin.tail x) w (state.store (x 0) v))] * F out.1 := fun v =>
        interp_presampleAll_eq computation budget F (Fin.tail x) hxt (fun i => hk i.succ) _ fun i => by
          show (state.store (x 0) v).cache (x i.succ) = none
          rw [store_cache_ne state (x 0) _ (fun e => Fin.succ_ne_zero i (hx e))]
          exact hfresh i.succ
      calc (Fintype.card R : ℝ≥0∞)⁻¹ * ∑ v, ∑' out, Pr[= out | interp tg initial model computation budget
              (state.store (x 0) v)] * F out.1
          = (Fintype.card R : ℝ≥0∞)⁻¹ * ∑ v, (((Fintype.card R : ℝ≥0∞) ^ n)⁻¹ * ∑ w : Fin n → R,
              ∑' out, Pr[= out | interp tg initial model computation budget
                (storeAll (Fin.tail x) w (state.store (x 0) v))] * F out.1) :=
            congrArg (fun A => (Fintype.card R : ℝ≥0∞)⁻¹ * A) (Finset.sum_congr rfl fun v _ => hrest v)
        _ = ((Fintype.card R : ℝ≥0∞) ^ (n + 1))⁻¹ * ∑ v, ∑ w : Fin n → R,
              ∑' out, Pr[= out | interp tg initial model computation budget
                (storeAll x (Fin.cons v w) state)] * F out.1 := by
            rw [← Finset.mul_sum, ← mul_assoc, pow_succ', ENNReal.mul_inv (Or.inr (by simp))
              (Or.inl (ENNReal.natCast_ne_top _))]
            rfl
        _ = _ := by
            congr 1
            rw [← Fintype.sum_prod_type']
            exact Fintype.sum_equiv (Fin.consEquiv fun _ => R) _ _ fun p => rfl

omit [Fintype ι] in
/-- **A query of one input of a fresh family**, for a value of the run alone: the uniform answer at
input `c` followed by the run has the same mean as the run after storing uniform answers at the
whole family. -/
theorem interp_presample_new_eq {α : Type} {n : ℕ} (x : Fin n → D) (hx : Function.Injective x)
    (hk : ∀ i, tg.kind (x i) = .none) (c : Fin n) (next : R → OracleComp (SourceCostSpec D R ι) α)
    (budget : ℕ) (state : DebtState D R ι) (hfresh : ∀ i, state.cache (x i) = none)
    (F : Run D ι α → ℝ≥0∞) :
    ∑' v, Pr[= v | ($ᵗ R : ProbComp R)] *
        ∑' out, Pr[= out | interp tg initial model (next v) budget (state.store (x c) v)] * F out.1 =
      ((Fintype.card R : ℝ≥0∞) ^ n)⁻¹ * ∑ u : Fin n → R,
        ∑' out, Pr[= out | interp tg initial model (next (u c)) budget (storeAll x u state)] * F out.1 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by have := c.isLt; omega⟩
  set σ : Equiv.Perm (Fin (m + 1)) := Equiv.swap 0 c with hσ
  set x' : Fin (m + 1) → D := x ∘ σ with hx'
  have hx'inj : Function.Injective x' := hx.comp σ.injective
  have hx'0 : x' 0 = x c := by simp [hx', hσ]
  have hxt : Function.Injective (Fin.tail x') := fun a b e => Fin.succ_injective _ (hx'inj e)
  have hrest : ∀ v, ∑' out, Pr[= out | interp tg initial model (next v) budget (state.store (x c) v)] * F out.1 =
      ((Fintype.card R : ℝ≥0∞) ^ m)⁻¹ * ∑ w : Fin m → R, ∑' out, Pr[= out | interp tg initial model
        (next v) budget (storeAll x' (Fin.cons v w) state)] * F out.1 := by
    intro v
    rw [← hx'0]
    exact interp_presampleAll_eq tg initial model (next v) budget F (Fin.tail x') hxt (fun i => hk _) _
      fun i => by
        show (state.store (x' 0) v).cache (x' i.succ) = none
        rw [store_cache_ne state (x' 0) _ (fun e => Fin.succ_ne_zero i (hx'inj e))]
        exact hfresh _
  rw [tsum_uniform_eq]
  calc (Fintype.card R : ℝ≥0∞)⁻¹ * ∑ v, ∑' out, Pr[= out | interp tg initial model (next v) budget
          (state.store (x c) v)] * F out.1
      = (Fintype.card R : ℝ≥0∞)⁻¹ * ∑ v, (((Fintype.card R : ℝ≥0∞) ^ m)⁻¹ * ∑ w : Fin m → R,
          ∑' out, Pr[= out | interp tg initial model (next v) budget (storeAll x' (Fin.cons v w) state)] * F out.1) :=
        congrArg (fun A => (Fintype.card R : ℝ≥0∞)⁻¹ * A) (Finset.sum_congr rfl fun v _ => hrest v)
    _ = ((Fintype.card R : ℝ≥0∞) ^ (m + 1))⁻¹ * ∑ u' : Fin (m + 1) → R,
          ∑' out, Pr[= out | interp tg initial model (next (u' 0)) budget (storeAll x' u' state)] * F out.1 := by
        rw [← Finset.mul_sum, ← mul_assoc, pow_succ', ENNReal.mul_inv (Or.inr (by simp))
          (Or.inl (ENNReal.natCast_ne_top _))]
        congr 1
        rw [← Fintype.sum_prod_type']
        exact Fintype.sum_equiv (Fin.consEquiv fun _ => R) _ _ fun p => rfl
    _ = _ := by
        congr 1
        refine Fintype.sum_equiv (σ.arrowCongr (Equiv.refl R)) _ _ fun u' => ?_
        have hu : (σ.arrowCongr (Equiv.refl R)) u' ∘ σ = u' := by
          funext i
          simp [Equiv.arrowCongr_apply, hσ, Equiv.swap_apply_self]
        conv_lhs => rw [← hu]
        rw [storeAll_perm x hx _ σ state]
        congr 3

end FORS.Security.HiddenDebt
