import Sphincs.BridgePresample
import Sphincs.BridgeForestPrice

/-! The signer inside the interpreted lazy comparison. Lifted private randomness is drawn as is;
lifted hash computations that avoid a set of inputs leave the cache unchanged there. These are
the ingredients of the fair-share bound for the grinding signer. -/

open OracleComp OracleSpec ENNReal

namespace Sphincs.Security.HiddenDebt

open HiddenCost HiddenBridge HiddenOutside HiddenReveal

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
attribute [local instance] Classical.propDecidable

variable {D R A ι : Type} [Fintype ι] [SampleableType R]
attribute [local instance] saturationDecEqInput saturationDecEqCoordinate
variable (tg : Targeting D R ι) (initial : Cache D R) (model : HiddenRows.Model D R A ι)

omit [Fintype ι] in
/-- A private draw is drawn directly and changes nothing else. -/
theorem interp_draw {β : Type} (draw : ℕ)
    (next : Fin (draw + 1) → OracleComp (SourceCostSpec D R ι) β) (budget : ℕ) (state : DebtState D R ι) :
    interp tg initial model (liftM ((SourceCostSpec D R ι).query (.inl (.inl draw))) >>= next) budget state =
      (liftM (unifSpec.query draw) : ProbComp (Fin (draw + 1))) >>= fun value =>
        interp tg initial model (next value) budget state := by
  rw [interp_query_bind]
  split_ifs with h
  · change ((fun v => (v, state)) <$> (liftM (unifSpec.query draw) : ProbComp (Fin (draw + 1)))) >>=
        (fun result => (fun out : Run D ι β × DebtState D R ι => ((out.1.1, [] ++ out.1.2.1, [] ++ out.1.2.2.1,
          [] ++ out.1.2.2.2), out.2)) <$> interp tg initial model (next result.1) (budget - 0) result.2) = _
    rw [bind_map_left]
    refine bind_congr fun value => ?_
    simp only [List.nil_append, Nat.sub_zero]
    rw [show (fun out : Run D ι β × DebtState D R ι =>
        ((out.1.1, out.1.2.1, out.1.2.2.1, out.1.2.2.2), out.2)) = id from rfl, id_map]
  · exact absurd (Nat.zero_le budget) h

omit [Fintype ι] in
/-- Lifted private randomness is drawn directly and changes nothing else. -/
theorem interp_liftProb_bind {α β : Type} (sample : ProbComp α)
    (next : α → OracleComp (SourceCostSpec D R ι) β) (budget : ℕ) (state : DebtState D R ι) :
    interp tg initial model ((liftM sample : OracleComp (SourceCostSpec D R ι) α) >>= next) budget state =
      sample >>= fun value => interp tg initial model (next value) budget state := by
  induction sample using OracleComp.inductionOn with
  | pure value => simp only [liftM_pure, pure_bind]
  | query_bind query rest ih =>
      rw [liftM_bind, bind_assoc]
      exact (interp_draw tg initial model query _ budget state).trans
        (by rw [bind_assoc]; exact bind_congr fun value => ih value)

/-! ### Computations that avoid a set of outside inputs -/

/-- No ordinary query of the computation lies in `avoid`. -/
def Avoids (avoid : D → Prop) {α : Type} (computation : OracleComp (SourceCostSpec D R ι) α) : Prop :=
  OracleComp.construct (fun _ => True)
    (fun input _ next => (∀ bytes, input = .inl (.inr (.inl bytes)) → ¬avoid bytes) ∧ ∀ value, next value)
    computation

omit [Fintype ι] [SampleableType R] in
theorem avoids_pure (avoid : D → Prop) {α : Type} (value : α) :
    Avoids avoid (pure value : OracleComp (SourceCostSpec D R ι) α) := trivial

omit [Fintype ι] [SampleableType R] in
theorem avoids_query_bind (avoid : D → Prop) {α : Type} (input : (SourceCostSpec D R ι).Domain)
    (next : (SourceCostSpec D R ι).Range input → OracleComp (SourceCostSpec D R ι) α) :
    Avoids avoid (liftM ((SourceCostSpec D R ι).query input) >>= next) ↔
      (∀ bytes, input = .inl (.inr (.inl bytes)) → ¬avoid bytes) ∧ ∀ value, Avoids avoid (next value) :=
  Iff.rfl

omit [Fintype ι] [SampleableType R] in
theorem avoids_bind (avoid : D → Prop) {α β : Type} {first : OracleComp (SourceCostSpec D R ι) α}
    {next : α → OracleComp (SourceCostSpec D R ι) β} (hfirst : Avoids avoid first)
    (hnext : ∀ value, Avoids avoid (next value)) : Avoids avoid (first >>= next) := by
  induction first using OracleComp.inductionOn with
  | pure value => simpa only [pure_bind] using hnext value
  | query_bind input rest ih =>
      rw [bind_assoc, avoids_query_bind]
      obtain ⟨hin, hrest⟩ := (avoids_query_bind avoid input rest).1 hfirst
      exact ⟨hin, fun value => ih value (hrest value)⟩

omit [Fintype ι] [SampleableType R] in
theorem avoids_tick (avoid : D → Prop) (amount : ℕ) :
    Avoids avoid (tick (D := D) (R := R) (ι := ι) amount) := by
  unfold tick
  rw [← bind_pure (liftM ((SourceCostSpec D R ι).query (.inr amount)))]
  exact (avoids_query_bind avoid _ _).2 ⟨fun bytes h => (by cases h), fun _ => trivial⟩

omit [Fintype ι] [SampleableType R] in
theorem avoids_reveal (avoid : D → Prop) (coordinate : ι) :
    Avoids avoid (reveal (D := D) (R := R) coordinate) := by
  unfold reveal
  rw [← bind_pure (liftM ((SourceCostSpec D R ι).query (.inl (.inr (.inr coordinate)))))]
  exact (avoids_query_bind avoid _ _).2 ⟨fun bytes h => (by cases h), fun _ => trivial⟩

omit [Fintype ι] [SampleableType R] in
theorem avoids_liftProb (avoid : D → Prop) {α : Type} (sample : ProbComp α) :
    Avoids avoid (liftM sample : OracleComp (SourceCostSpec D R ι) α) := by
  induction sample using OracleComp.inductionOn with
  | pure value => exact avoids_pure avoid value
  | query_bind query rest ih =>
      rw [liftM_bind]
      exact (avoids_query_bind avoid (.inl (.inl query)) _).2 ⟨fun bytes h => (by cases h), ih⟩

omit [Fintype ι] [SampleableType R] in
/-- A hash computation lifted into the cost interface avoids every input it never queries. -/
theorem avoids_liftHash (avoid : D → Prop) {α : Type} (computation : OracleComp (D →ₒ R) α)
    (h : computation.IsQueryBoundP avoid 0) :
    Avoids avoid (liftM computation : OracleComp (SourceCostSpec D R ι) α) := by
  induction computation using OracleComp.inductionOn with
  | pure value => exact avoids_pure avoid value
  | query_bind query rest ih =>
      rw [isQueryBoundP_query_bind_iff] at h
      rw [liftM_bind]
      refine (avoids_query_bind avoid (.inl (.inr (.inl query))) _).2 ⟨?_, fun value => ih value ?_⟩
      · intro bytes hb
        cases hb
        rcases h.1 with hnot | hpos
        · exact hnot
        · exact absurd hpos (lt_irrefl 0)
      · have := h.2 value
        split_ifs at this with hq
        · rcases h.1 with hnot | hpos
          · exact absurd hq hnot
          · exact absurd hpos (lt_irrefl 0)
        · exact this

omit [Fintype ι] in
/-- Avoided inputs keep their cache entries through the interpreter. -/
theorem interp_avoids_cache (avoid : D → Prop) {α : Type} (computation : OracleComp (SourceCostSpec D R ι) α)
    (h : Avoids avoid computation) :
    ∀ budget (state : DebtState D R ι), ∀ out ∈ support (interp tg initial model computation budget state),
      ∀ x, avoid x → out.2.cache x = state.cache x := by
  induction computation using OracleComp.inductionOn with
  | pure value =>
      intro budget state out hout x _
      rw [interp_pure, support_pure, Set.mem_singleton_iff] at hout
      rw [hout]
  | query_bind input next ih =>
      intro budget state out hout x hx
      obtain ⟨hin, hnext⟩ := (avoids_query_bind avoid input next).1 h
      rw [interp_query_bind] at hout
      split_ifs at hout with hcost
      · rw [support_bind] at hout
        simp only [Set.mem_iUnion, support_map, Set.mem_image] at hout
        obtain ⟨result, hresult, inner, hinner, rfl⟩ := hout
        rw [ih result.1 (hnext result.1) _ result.2 inner hinner x hx]
        -- one step keeps the avoided entry
        rcases input with (draw | (bytes | coordinate)) | amount
        · change result ∈ support ((fun v => (v, state)) <$> (liftM (unifSpec.query draw) : ProbComp _)) at hresult
          rw [support_map] at hresult
          obtain ⟨v, _, rfl⟩ := hresult
          rfl
        · have hne : x ≠ bytes := fun heq => hin bytes rfl (heq ▸ hx)
          rw [costStep_ordinary] at hresult
          unfold ordinaryStep at hresult
          have hread : ∀ (s' : DebtState D R ι) (r : R × DebtState D R ι), r ∈ support (readOutside bytes s') →
              r.2.cache x = s'.cache x := by
            intro s' r hr
            rcases readOutside_support bytes s' r hr with h' | ⟨_, h'⟩
            · rw [h']
            · rw [h']
              exact store_cache_ne s' bytes x hne r.1
          split at hresult
          · exact hread _ result hresult
          · split at hresult
            · exact hread (state.record _) result hresult
            · split at hresult
              · rw [support_map] at hresult
                obtain ⟨r, hr, rfl⟩ := hresult
                rw [sampleCoordinate_expose _ state r hr]
                rfl
              · exact hread _ result hresult
        · change result ∈ support (sampleCoordinate coordinate state) at hresult
          rw [sampleCoordinate_expose _ state result hresult]
          rfl
        · change result ∈ support (pure ((), state) : ProbComp _) at hresult
          rw [support_pure, Set.mem_singleton_iff] at hresult
          rw [hresult]
      · rw [support_pure, Set.mem_singleton_iff] at hout
        rw [hout]

/-! ### Reading untargeted inputs -/

omit [Fintype ι] in
/-- One ordinary query in the interpreter. -/
theorem interp_ordinary {β : Type} (x : D) (next : R → OracleComp (SourceCostSpec D R ι) β)
    (budget : ℕ) (state : DebtState D R ι) :
    interp tg initial model (liftM ((SourceCostSpec D R ι).query (.inl (.inr (.inl x)))) >>= next) budget state =
      if 1 ≤ budget then ordinaryStep model x state.known state >>= fun result =>
        (fun out => ((out.1.1, out.1.2.1, Sum.inl x :: out.1.2.2.1,
          touch tg initial state (.inl (.inr (.inl x))) ++ out.1.2.2.2), out.2)) <$>
            interp tg initial model (next result.1) (budget - 1) result.2
      else pure ((none, [], [], []), state) := by
  rw [interp_query_bind]
  rfl

omit [Fintype ι] [SampleableType R] in
theorem avoids_mono {avoid avoid' : D → Prop} (hsub : ∀ x, avoid' x → avoid x) {α : Type}
    {computation : OracleComp (SourceCostSpec D R ι) α} (h : Avoids avoid computation) :
    Avoids avoid' computation := by
  induction computation using OracleComp.inductionOn with
  | pure value => trivial
  | query_bind input next ih =>
      obtain ⟨hin, hnext⟩ := (avoids_query_bind avoid input next).1 h
      exact (avoids_query_bind avoid' input next).2
        ⟨fun bytes hb hav => hin bytes hb (hsub bytes hav), fun value => ih value (hnext value)⟩

omit [Fintype ι] [SampleableType R] in
theorem avoids_sequenceFin (avoid : D → Prop) {α : Type} :
    ∀ {n : ℕ} (computation : Fin n → OracleComp (SourceCostSpec D R ι) α),
      (∀ i, Avoids avoid (computation i)) → Avoids avoid (Concrete.sequenceFin computation)
  | 0, _, _ => avoids_pure avoid _
  | n + 1, computation, h => by
      unfold Concrete.sequenceFin
      exact avoids_bind avoid (h 0) fun _ =>
        avoids_bind avoid (avoids_sequenceFin avoid (fun i : Fin n => computation i.succ) fun i => h i.succ)
          fun _ => avoids_pure avoid _

omit [Fintype ι] in
/-- Interpreted results are possible results of the computation. -/
theorem interp_result_mem {α : Type} (computation : OracleComp (SourceCostSpec D R ι) α) :
    ∀ budget (state : DebtState D R ι), ∀ out ∈ support (interp tg initial model computation budget state),
      ∀ value, out.1.1 = some value → value ∈ support computation := by
  induction computation using OracleComp.inductionOn with
  | pure value =>
      intro budget state out hout v hv
      rw [interp_pure, support_pure, Set.mem_singleton_iff] at hout
      rw [hout] at hv
      cases hv
      exact (mem_support_pure_iff _ _).2 rfl
  | query_bind input next ih =>
      intro budget state out hout v hv
      rw [interp_query_bind] at hout
      split_ifs at hout with hcost
      · rw [support_bind] at hout
        simp only [Set.mem_iUnion, support_map, Set.mem_image] at hout
        obtain ⟨result, _, inner, hinner, rfl⟩ := hout
        have := ih result.1 _ result.2 inner hinner v hv
        rw [support_bind]
        exact Set.mem_iUnion₂.2 ⟨result.1, by simp, this⟩
      · rw [support_pure, Set.mem_singleton_iff] at hout
        rw [hout] at hv
        cases hv

omit [Fintype ι] in
/-- **Two reads, both entries kept.** -/
theorem two_reads_bound₂ {β : Type} (x0 x1 : D) (hne : x0 ≠ x1) (hp0 : model.parse x0 = none)
    (hp1 : model.parse x1 = none) (state : DebtState D R ι) (u0 : R) (hc0 : state.cache x0 = some u0)
    (rest : R → R → OracleComp (SourceCostSpec D R ι) β)
    (havoid : ∀ a b, Avoids (fun x => x = x0 ∨ x = x1) (rest a b)) (g : R → R → ℝ≥0∞) (budget : ℕ) :
    ∑' out, Pr{let x ← (interp tg initial model
        (liftM ((SourceCostSpec D R ι).query (.inl (.inr (.inl x0)))) >>= fun a =>
          liftM ((SourceCostSpec D R ι).query (.inl (.inr (.inl x1)))) >>= fun b => rest a b) budget state)}[x = out] *
        (if out.1.1.isSome then (out.2.cache x0).elim 0 (fun a => (out.2.cache x1).elim 0 (g a)) else 0) ≤
      (state.cache x1).elim (∑' u, Pr{let x ← ($ᵗ R : ProbComp R)}[x = u] * g u0 u) (g u0) := by
  have hinner : ∀ a b (s : DebtState D R ι) b', s.cache x0 = some u0 → s.cache x1 = some b →
      ∑' out, Pr{let x ← interp tg initial model (rest a b) b' s}[x = out] *
        (if out.1.1.isSome then (out.2.cache x0).elim 0 (fun a => (out.2.cache x1).elim 0 (g a)) else 0) ≤
          g u0 b := by
    intro a b s b' hs0 hs1
    calc _ ≤ ∑' out, Pr{let x ← interp tg initial model (rest a b) b' s}[x = out] * g u0 b := by
          refine ENNReal.tsum_le_tsum fun out => ?_
          by_cases hout : out ∈ support (interp tg initial model (rest a b) b' s)
          · have hk0 := interp_avoids_cache tg initial model _ (rest a b) (havoid a b) b' s out hout x0 (Or.inl rfl)
            have hk1 := interp_avoids_cache tg initial model _ (rest a b) (havoid a b) b' s out hout x1 (Or.inr rfl)
            gcongr
            split_ifs
            · rw [hk0, hs0, hk1, hs1]
              rfl
            · exact bot_le
          · rw [(prEvent_eq_zero_of_not_mem_support _) hout, zero_mul, zero_mul]
      _ ≤ g u0 b := by
          rw [ENNReal.tsum_mul_right]
          exact mul_le_of_le_one_left' (OracleComp.tsum_prEvent_le_one _)
  rw [interp_ordinary]
  split_ifs with h0
  · rw [ordinaryStep, hp0]
    simp only
    rw [readOutside_cached x0 state u0 hc0, pure_bind, OracleComp.tsum_prEvent_map_mul]
    simp only
    rw [interp_ordinary]
    split_ifs with h1
    · rw [ordinaryStep, hp1]
      simp only
      cases hc1 : state.cache x1 with
      | some u1 =>
          rw [readOutside_cached x1 state u1 hc1, pure_bind, OracleComp.tsum_prEvent_map_mul]
          exact hinner u0 u1 state _ hc0 hc1
      | none =>
          simp only [Option.elim]
          rw [readOutside_fresh x1 state hc1, bind_map_left, OracleComp.tsum_prEvent_bind_mul]
          refine ENNReal.tsum_le_tsum fun u => ?_
          gcongr
          rw [OracleComp.tsum_prEvent_map_mul]
          exact hinner u0 u (state.store x1 u) _ (by rw [store_cache_ne state x1 x0 hne u]; exact hc0)
            (by simp [DebtState.store])
    · rw [OracleComp.tsum_prEvent_pure_mul]
      simp
  · rw [OracleComp.tsum_prEvent_pure_mul]
    simp

end Sphincs.Security.HiddenDebt
