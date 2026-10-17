import SphincsFors.BridgeSigner

/-! Support facts for the interpreter: states only grow, a decided hit stays decided, reveals
follow the computation's reveal queries, and presampling an untargeted input can only help a
final value that is monotone in the cache. -/

open OracleComp OracleSpec ENNReal

namespace SphincsFors.Security.HiddenDebt

open HiddenCost HiddenBridge HiddenOutside HiddenReveal

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
attribute [local instance] Classical.propDecidable

variable {D R A ι : Type} [Fintype ι] [SampleableType R]
attribute [local instance] saturationDecEqInput saturationDecEqCoordinate
variable (tg : Targeting D R ι) (initial : Cache D R) (model : HiddenRows.Model D R A ι)

/-! ### Growth of states -/

/-- The later state keeps every cache entry, exposed coordinate and guess of the earlier one. -/
def Extends (before after : DebtState D R ι) : Prop :=
  (∀ x v, before.cache x = some v → after.cache x = some v) ∧
  (∀ c v, before.known c = some v → after.known c = some v) ∧
  (∀ g ∈ before.guesses, g ∈ after.guesses)

omit [Fintype ι] [SampleableType R] in
theorem Extends.refl (state : DebtState D R ι) : Extends state state :=
  ⟨fun _ _ h => h, fun _ _ h => h, fun _ h => h⟩

omit [Fintype ι] [SampleableType R] in
theorem Extends.trans {first second third : DebtState D R ι} (h : Extends first second)
    (h' : Extends second third) : Extends first third :=
  ⟨fun x v hx => h'.1 x v (h.1 x v hx), fun c v hc => h'.2.1 c v (h.2.1 c v hc),
    fun g hg => h'.2.2 g (h.2.2 g hg)⟩

omit [Fintype ι] [SampleableType R] in
theorem extends_store (state : DebtState D R ι) (x : D) (u : R) (hc : state.cache x = none) :
    Extends state (state.store x u) := by
  refine ⟨fun y v hy => ?_, fun _ _ h => h, fun _ h => h⟩
  by_cases hyx : y = x
  · subst hyx; rw [hc] at hy; cases hy
  · rw [store_cache_ne state x y hyx u]; exact hy

omit [Fintype ι] [SampleableType R] in
theorem extends_record (state : DebtState D R ι) (guess : ι × Digest) :
    Extends state (state.record guess) :=
  ⟨fun _ _ h => h, fun _ _ h => h, fun _ hg => List.mem_cons_of_mem _ hg⟩

omit [Fintype ι] [SampleableType R] in
theorem extends_expose (state : DebtState D R ι) (coordinate : ι) (value : Digest)
    (hc : state.known coordinate = none) : Extends state (state.expose coordinate value) := by
  refine ⟨fun _ _ h => h, fun c v hcv => ?_, fun _ h => h⟩
  by_cases hcc : c = coordinate
  · subst hcc; rw [hc] at hcv; cases hcv
  · simp only [DebtState.expose, QueryCache.cacheQuery_of_ne _ _ hcc]; exact hcv

omit [Fintype ι] in
theorem extends_readOutside (bytes : D) (state : DebtState D R ι) :
    ∀ r ∈ support (readOutside bytes state), Extends state r.2 := by
  intro r hr
  rcases readOutside_support bytes state r hr with h | ⟨hc, h⟩
  · rw [h]; exact Extends.refl state
  · rw [h]; exact extends_store state bytes r.1 hc

omit [Fintype ι] [SampleableType R] in
theorem extends_sampleCoordinate (coordinate : ι) (state : DebtState D R ι) :
    ∀ r ∈ support (sampleCoordinate coordinate state), Extends state r.2 := by
  intro r hr
  cases hc : state.known coordinate with
  | none =>
      rw [sampleCoordinate_expose coordinate state r hr]
      exact extends_expose state coordinate r.1 hc
  | some v =>
      rw [sampleCoordinate_known coordinate state v hc, support_pure, Set.mem_singleton_iff] at hr
      rw [hr]
      exact Extends.refl state

omit [Fintype ι] in
theorem extends_costStep (input : (SourceCostSpec D R ι).Domain) (state : DebtState D R ι) :
    ∀ r ∈ support (costStep model input state), Extends state r.2 := by
  intro r hr
  rcases input with (draw | (bytes | coordinate)) | amount
  · change r ∈ support ((fun v => (v, state)) <$> (liftM (unifSpec.query draw) : ProbComp _)) at hr
    rw [support_map] at hr
    obtain ⟨v, _, rfl⟩ := hr
    exact Extends.refl state
  · rw [costStep_ordinary] at hr
    unfold ordinaryStep at hr
    split at hr
    · exact extends_readOutside bytes state r hr
    · split at hr
      · exact (extends_record state _).trans (extends_readOutside bytes _ r hr)
      · split at hr
        · rw [support_map] at hr
          obtain ⟨r', hr', rfl⟩ := hr
          exact extends_sampleCoordinate _ state r' hr'
        · exact extends_readOutside bytes state r hr
  · exact extends_sampleCoordinate coordinate state r hr
  · change r ∈ support (pure ((), state) : ProbComp _) at hr
    rw [support_pure, Set.mem_singleton_iff] at hr
    rw [hr]
    exact Extends.refl state

omit [Fintype ι] in
/-- Interpreted runs only grow the state. -/
theorem interp_extends {α : Type} (computation : OracleComp (SourceCostSpec D R ι) α) :
    ∀ budget (state : DebtState D R ι), ∀ out ∈ support (interp tg initial model computation budget state),
      Extends state out.2 := by
  induction computation using OracleComp.inductionOn with
  | pure value =>
      intro budget state out hout
      rw [interp_pure, support_pure, Set.mem_singleton_iff] at hout
      rw [hout]
      exact Extends.refl state
  | query_bind input next ih =>
      intro budget state out hout
      rw [interp_query_bind] at hout
      split_ifs at hout with hcost
      · rw [support_bind] at hout
        simp only [Set.mem_iUnion, support_map, Set.mem_image] at hout
        obtain ⟨result, hresult, inner, hinner, rfl⟩ := hout
        exact (extends_costStep model input state result hresult).trans
          (ih result.1 _ result.2 inner hinner)
      · rw [support_pure, Set.mem_singleton_iff] at hout
        rw [hout]
        exact Extends.refl state

omit [Fintype ι] [SampleableType R] in
theorem debts_mono {before after : DebtState D R ι} (h : Extends before after) (coordinate : ι) :
    debts tg initial before coordinate ⊆ debts tg initial after coordinate := by
  intro value hv
  rcases hv with hg | ⟨input, output, hc, hi, hk, ht⟩
  · exact Or.inl (h.2.2 _ hg)
  · exact Or.inr ⟨input, output, h.1 input output hc, hi, hk, ht⟩

omit [Fintype ι] [SampleableType R] in
/-- A decided hit stays decided. -/
theorem realized_of_extends {before after : DebtState D R ι} (h : Extends before after)
    (hr : Realized tg initial before) : Realized tg initial after := by
  rcases hr with ⟨input, output, value, hc, hi, hk, ht⟩ | ⟨coordinate, value, hk, hv⟩
  · exact Or.inl ⟨input, output, value, h.1 input output hc, hi, hk, ht⟩
  · exact Or.inr ⟨coordinate, value, h.2.1 coordinate value hk, debts_mono tg initial h coordinate hv⟩

/-! ### Reveals follow the reveal queries -/

/-- Every reveal query of the computation satisfies `allowed`. -/
def RevealsIn (allowed : ι → Prop) {α : Type} (computation : OracleComp (SourceCostSpec D R ι) α) : Prop :=
  OracleComp.construct (fun _ => True)
    (fun input _ next => (∀ c, input = .inl (.inr (.inr c)) → allowed c) ∧ ∀ value, next value)
    computation

omit [Fintype ι] [SampleableType R] in
theorem revealsIn_pure (allowed : ι → Prop) {α : Type} (value : α) :
    RevealsIn allowed (pure value : OracleComp (SourceCostSpec D R ι) α) := trivial

omit [Fintype ι] [SampleableType R] in
theorem revealsIn_query_bind (allowed : ι → Prop) {α : Type} (input : (SourceCostSpec D R ι).Domain)
    (next : (SourceCostSpec D R ι).Range input → OracleComp (SourceCostSpec D R ι) α) :
    RevealsIn allowed (liftM ((SourceCostSpec D R ι).query input) >>= next) ↔
      (∀ c, input = .inl (.inr (.inr c)) → allowed c) ∧ ∀ value, RevealsIn allowed (next value) :=
  Iff.rfl

omit [Fintype ι] [SampleableType R] in
theorem revealsIn_bind (allowed : ι → Prop) {α β : Type} {first : OracleComp (SourceCostSpec D R ι) α}
    {next : α → OracleComp (SourceCostSpec D R ι) β} (hfirst : RevealsIn allowed first)
    (hnext : ∀ value, RevealsIn allowed (next value)) : RevealsIn allowed (first >>= next) := by
  induction first using OracleComp.inductionOn with
  | pure value => simpa only [pure_bind] using hnext value
  | query_bind input rest ih =>
      rw [bind_assoc, revealsIn_query_bind]
      obtain ⟨hin, hrest⟩ := (revealsIn_query_bind allowed input rest).1 hfirst
      exact ⟨hin, fun value => ih value (hrest value)⟩

omit [Fintype ι] [SampleableType R] in
theorem revealsIn_tick (allowed : ι → Prop) (amount : ℕ) :
    RevealsIn allowed (tick (D := D) (R := R) (ι := ι) amount) := by
  unfold tick
  rw [← bind_pure (liftM ((SourceCostSpec D R ι).query (.inr amount)))]
  exact (revealsIn_query_bind allowed _ _).2 ⟨fun c h => (by cases h), fun _ => trivial⟩

omit [Fintype ι] [SampleableType R] in
theorem revealsIn_reveal (allowed : ι → Prop) (coordinate : ι) (h : allowed coordinate) :
    RevealsIn allowed (reveal (D := D) (R := R) coordinate) := by
  unfold reveal
  rw [← bind_pure (liftM ((SourceCostSpec D R ι).query (.inl (.inr (.inr coordinate)))))]
  refine (revealsIn_query_bind allowed _ _).2 ⟨fun c hc => ?_, fun _ => trivial⟩
  cases hc
  exact h

omit [Fintype ι] [SampleableType R] in
theorem revealsIn_liftHash (allowed : ι → Prop) {α : Type} (computation : OracleComp (D →ₒ R) α) :
    RevealsIn allowed (liftM computation : OracleComp (SourceCostSpec D R ι) α) := by
  induction computation using OracleComp.inductionOn with
  | pure value => exact revealsIn_pure allowed value
  | query_bind query rest ih =>
      rw [liftM_bind]
      exact (revealsIn_query_bind allowed (.inl (.inr (.inl query))) _).2 ⟨fun c h => (by cases h), ih⟩

omit [Fintype ι] [SampleableType R] in
theorem revealsIn_sequenceFin (allowed : ι → Prop) {α : Type} :
    ∀ {n : ℕ} (computation : Fin n → OracleComp (SourceCostSpec D R ι) α),
      (∀ i, RevealsIn allowed (computation i)) → RevealsIn allowed (Concrete.sequenceFin computation)
  | 0, _, _ => revealsIn_pure allowed _
  | n + 1, computation, h => by
      unfold Concrete.sequenceFin
      exact revealsIn_bind allowed (h 0) fun _ =>
        revealsIn_bind allowed (revealsIn_sequenceFin allowed (fun i : Fin n => computation i.succ)
          fun i => h i.succ) fun _ => revealsIn_pure allowed _

omit [Fintype ι] in
/-- Interpreted reveals are reveal queries of the computation. -/
theorem interp_reveals {allowed : ι → Prop} {α : Type} (computation : OracleComp (SourceCostSpec D R ι) α)
    (h : RevealsIn allowed computation) :
    ∀ budget (state : DebtState D R ι), ∀ out ∈ support (interp tg initial model computation budget state),
      ∀ c ∈ out.1.2.1, allowed c := by
  induction computation using OracleComp.inductionOn with
  | pure value =>
      intro budget state out hout c hc
      rw [interp_pure, support_pure, Set.mem_singleton_iff] at hout
      rw [hout] at hc
      cases hc
  | query_bind input next ih =>
      intro budget state out hout c hc
      obtain ⟨hin, hnext⟩ := (revealsIn_query_bind allowed input next).1 h
      rw [interp_query_bind] at hout
      split_ifs at hout with hcost
      · rw [support_bind] at hout
        simp only [Set.mem_iUnion, support_map, Set.mem_image] at hout
        obtain ⟨result, _, inner, hinner, rfl⟩ := hout
        rcases List.mem_append.1 hc with hc | hc
        · rcases input with (draw | (bytes | coordinate)) | amount
          · cases hc
          · cases hc
          · simp only [revealed, List.mem_singleton] at hc
            subst hc
            exact hin _ rfl
          · cases hc
        · exact ih result.1 (hnext result.1) _ result.2 inner hinner c hc
      · rw [support_pure, Set.mem_singleton_iff] at hout
        rw [hout] at hc
        cases hc

/-! ### Presampling only helps monotone final values -/

omit [Fintype ι] in
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

/-! ### Decomposing a sequential run -/

omit [Fintype ι] in
theorem interp_bind_mem {α β : Type} (first : OracleComp (SourceCostSpec D R ι) α)
    (next : α → OracleComp (SourceCostSpec D R ι) β) (budget : ℕ) (state : DebtState D R ι)
    (out : Run D ι β × DebtState D R ι)
    (hout : out ∈ support (interp tg initial model (first >>= next) budget state)) :
    ∃ o1 ∈ support (interp tg initial model first budget state),
      (o1.1.1 = none ∧ out.1.1 = none ∧ out.1.2.1 = o1.1.2.1 ∧ out.2 = o1.2) ∨
      ∃ v, o1.1.1 = some v ∧ ∃ o2 ∈ support (interp tg initial model (next v)
        (budget - traceCost o1.1.2.2.1) o1.2),
        out.1.1 = o2.1.1 ∧ out.1.2.1 = o1.1.2.1 ++ o2.1.2.1 ∧ out.2 = o2.2 := by
  rw [interp_bind, support_bind] at hout
  obtain ⟨o1, ho1, hout⟩ := Set.mem_iUnion₂.1 hout
  refine ⟨o1, ho1, ?_⟩
  unfold interpThen at hout
  cases hv : o1.1.1 with
  | none =>
      simp only [hv, support_pure, Set.mem_singleton_iff] at hout
      exact Or.inl ⟨rfl, by rw [hout], by rw [hout], by rw [hout]⟩
  | some v =>
      simp only [hv, support_map, Set.mem_image] at hout
      obtain ⟨o2, ho2, rfl⟩ := hout
      exact Or.inr ⟨v, rfl, o2, ho2, rfl, rfl, rfl⟩

/-! ### Costs and cache growth -/

omit [Fintype ι] in
theorem interp_traceCost_le {α : Type} (computation : OracleComp (SourceCostSpec D R ι) α) :
    ∀ budget (state : DebtState D R ι), ∀ out ∈ support (interp tg initial model computation budget state),
      traceCost out.1.2.2.1 ≤ budget := by
  induction computation using OracleComp.inductionOn with
  | pure value =>
      intro budget state out hout
      rw [interp_pure, support_pure, Set.mem_singleton_iff] at hout
      rw [hout]; simp [traceCost]
  | query_bind input next ih =>
      intro budget state out hout
      rw [interp_query_bind] at hout
      split_ifs at hout with hcost
      · rw [support_bind] at hout
        simp only [Set.mem_iUnion, support_map, Set.mem_image] at hout
        obtain ⟨result, _, inner, hinner, rfl⟩ := hout
        simp only [traceCost_append, recorded_cost]
        have := ih result.1 _ result.2 inner hinner
        omega
      · rw [support_pure, Set.mem_singleton_iff] at hout
        rw [hout]; simp [traceCost]

omit [Fintype ι] [SampleableType R] in
theorem card_filter_store_le (T : Finset D) (state : DebtState D R ι) (x : D) (u : R) :
    (T.filter fun y => (state.store x u).cache y ≠ none).card ≤ (T.filter fun y => state.cache y ≠ none).card + 1 := by
  calc (T.filter fun y => (state.store x u).cache y ≠ none).card
      ≤ (insert x (T.filter fun y => state.cache y ≠ none)).card := by
        refine Finset.card_le_card fun y hy => ?_
        rw [Finset.mem_filter] at hy
        rw [Finset.mem_insert, Finset.mem_filter]
        by_cases h : y = x
        · exact Or.inl h
        · exact Or.inr ⟨hy.1, by rw [store_cache_ne state x y h u] at hy; exact hy.2⟩
    _ ≤ _ := Finset.card_insert_le _ _

omit [Fintype ι] in
theorem costStep_card_le (T : Finset D) (input : (SourceCostSpec D R ι).Domain) (state : DebtState D R ι) :
    ∀ r ∈ support (costStep model input state),
      (T.filter fun y => r.2.cache y ≠ none).card ≤ (T.filter fun y => state.cache y ≠ none).card + sourceCost input := by
  intro r hr
  have hread : ∀ (bytes : D) (s' : DebtState D R ι), s'.cache = state.cache → ∀ r ∈ support (readOutside bytes s'),
      (T.filter fun y => r.2.cache y ≠ none).card ≤ (T.filter fun y => state.cache y ≠ none).card + 1 := by
    intro bytes s' hs' r hr
    rcases readOutside_support bytes s' r hr with h | ⟨_, h⟩
    · rw [h, hs']; exact Nat.le_succ _
    · rw [h]
      have := card_filter_store_le T s' bytes r.1
      rw [hs'] at this
      exact this
  rcases input with (draw | (bytes | coordinate)) | amount
  · change r ∈ support ((fun v => (v, state)) <$> (liftM (unifSpec.query draw) : ProbComp _)) at hr
    rw [support_map] at hr
    obtain ⟨v, _, rfl⟩ := hr
    exact Nat.le_add_right _ _
  · rw [costStep_ordinary] at hr
    unfold ordinaryStep at hr
    change _ ≤ _ + 1
    split at hr
    · exact hread bytes state rfl r hr
    · split at hr
      · exact hread bytes (state.record _) rfl r hr
      · split at hr
        · rw [support_map] at hr
          obtain ⟨r', hr', rfl⟩ := hr
          rw [sampleCoordinate_expose _ state r' hr']
          exact Nat.le_succ _
        · exact hread bytes state rfl r hr
  · change r ∈ support (sampleCoordinate coordinate state) at hr
    rw [sampleCoordinate_expose _ state r hr]
    exact Nat.le_add_right _ _
  · change r ∈ support (pure ((), state) : ProbComp _) at hr
    rw [support_pure, Set.mem_singleton_iff] at hr
    rw [hr]
    exact Nat.le_add_right _ _

omit [Fintype ι] in
/-- Each unit of cost adds at most one cache entry. -/
theorem interp_card_le (T : Finset D) {α : Type} (computation : OracleComp (SourceCostSpec D R ι) α) :
    ∀ budget (state : DebtState D R ι), ∀ out ∈ support (interp tg initial model computation budget state),
      (T.filter fun y => out.2.cache y ≠ none).card ≤
        (T.filter fun y => state.cache y ≠ none).card + traceCost out.1.2.2.1 := by
  induction computation using OracleComp.inductionOn with
  | pure value =>
      intro budget state out hout
      rw [interp_pure, support_pure, Set.mem_singleton_iff] at hout
      rw [hout]; simp [traceCost]
  | query_bind input next ih =>
      intro budget state out hout
      rw [interp_query_bind] at hout
      split_ifs at hout with hcost
      · rw [support_bind] at hout
        simp only [Set.mem_iUnion, support_map, Set.mem_image] at hout
        obtain ⟨result, hresult, inner, hinner, rfl⟩ := hout
        simp only [traceCost_append, recorded_cost]
        have h1 := ih result.1 _ result.2 inner hinner
        have h2 := costStep_card_le model T input state result hresult
        omega
      · rw [support_pure, Set.mem_singleton_iff] at hout
        rw [hout]; simp [traceCost]

end SphincsFors.Security.HiddenDebt
