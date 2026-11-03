import FORS.LazyRun.Interpreter

/-! Storing the answer to an untargeted, unparsed outside input changes neither the debts nor the
realized values of the interpreted lazy comparison (`debts_store_untargeted`,
`realized_store_untargeted`), and the cost of one ordinary step (`ordinaryStep`,
`costStep_ordinary`). -/

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

omit [Fintype ι] [SampleableType R] in
theorem store_cache_ne (state : DebtState D R ι) (x y : D) (hxy : y ≠ x) (u : R) :
    (state.store x u).cache y = state.cache y := by
  simp only [DebtState.store, QueryCache.cacheQuery_of_ne _ _ hxy]

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

/-! ### The ordinary step -/

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

end FORS.Security.HiddenDebt
