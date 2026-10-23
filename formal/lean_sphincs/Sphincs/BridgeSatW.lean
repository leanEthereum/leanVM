import Sphincs.BridgeInterpSupport

/-! Weighted saturation payments. A digest query pays the baseline times the current survival
weight instead of the baseline whenever no hit is decided. The saturation step then frees exactly
the budget decrement times the weight, so the payment no longer needs the worst-case lower bound
`1 - 2p/N` of the weight. The survival weight is a supermartingale of the interpreted run: untargeted
reads keep it, fresh answers and guesses only lower it, and exposures keep it in expectation. -/

open OracleComp OracleSpec ENNReal

namespace Sphincs.Security.HiddenDebt

open HiddenCost HiddenBridge HiddenOutside HiddenReveal

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false
attribute [local instance] Classical.propDecidable

variable {D R A ι : Type} [Fintype ι] [SampleableType R]
attribute [local instance] saturationDecEqInput saturationDecEqCoordinate
variable (tg : Targeting D R ι) (initial : Cache D R) (model : HiddenRows.Model D R A ι)

/-! ### The survival weight is a supermartingale -/

theorem debts_finiteW (state : DebtState D R ι) (coordinate : ι) :
    (debts tg initial state coordinate).Finite := Set.toFinite _

theorem survival_le_of_extendsW {state state' : DebtState D R ι} (h : Extends state state')
    (hknown : state'.known = state.known) :
    survival tg initial state' ≤ survival tg initial state := by
  unfold survival
  rw [hknown]
  refine Finset.prod_le_prod fun coordinate _ => ?_
  split_ifs
  · refine tsub_le_tsub_left (ENNReal.div_le_div_right ?_ _) _
    exact ENat.toENNReal_le.mpr (Set.encard_le_encard (debts_mono tg initial h coordinate))
  · exact le_rfl

/-- Growing the cache or the guesses, with the same exposed coordinates, can only lower the weight. -/
theorem weight_le_of_extendsW {state state' : DebtState D R ι} (h : Extends state state')
    (hknown : state'.known = state.known) :
    weight tg initial state' ≤ weight tg initial state := by
  unfold weight
  by_cases hr : Realized tg initial state
  · rw [ite_eq_left (realized_of_extends tg initial h hr), ite_eq_left hr]
  · rw [ite_eq_right hr]
    split_ifs
    · exact bot_le
    · exact survival_le_of_extendsW tg initial h hknown

/-- An untargeted answer keeps the weight. -/
theorem weight_store_untargetedW (state : DebtState D R ι) (x : D) (u : R) (hk : tg.kind x = .none) :
    weight tg initial (state.store x u) = weight tg initial state := by
  have hknown : (state.store x u).known = state.known := rfl
  unfold weight survival
  simp only [realized_store_untargeted tg initial state x u hk, debts_store_untargeted tg initial state x u hk,
    hknown]

theorem weight_presampleW (x : D) (hk : tg.kind x = .none) (state : DebtState D R ι) :
    ∀ s ∈ support (presample x state), weight tg initial s = weight tg initial state := by
  intro s hs
  cases hc : state.cache x with
  | some v =>
      rw [presample_cached x state v hc, support_pure, Set.mem_singleton_iff] at hs
      rw [hs]
  | none =>
      rw [presample_fresh x state hc, support_map] at hs
      obtain ⟨u, _, rfl⟩ := hs
      exact weight_store_untargetedW tg initial state x u hk

theorem meanWeight_le_of_supportW {β : Type} (step : ProbComp (β × DebtState D R ι)) (c : ℝ≥0∞)
    (h : ∀ r ∈ support step, weight tg initial r.2 ≤ c) : meanWeight tg initial step ≤ c := by
  unfold meanWeight
  calc ∑' r, Pr{let x ← step}[x = r] * weight tg initial r.2 ≤ ∑' r, Pr{let x ← step}[x = r] * c := by
        refine ENNReal.tsum_le_tsum fun r => ?_
        by_cases hr : r ∈ support step
        · exact mul_le_mul_right (h r hr) _
        · rw [(prEvent_eq_zero_of_not_mem_support _) hr, zero_mul, zero_mul]
    _ ≤ c := by
        rw [ENNReal.tsum_mul_right]
        exact mul_le_of_le_one_left' (OracleComp.tsum_prEvent_le_one _)

theorem readOutside_weight_leW (bytes : D) (state : DebtState D R ι) :
    ∀ r ∈ support (readOutside bytes state), weight tg initial r.2 ≤ weight tg initial state := by
  intro r hr
  rcases readOutside_support bytes state r hr with h | ⟨hc, h⟩
  · rw [h]
  · rw [h]
    exact weight_le_of_extendsW tg initial (extends_store state bytes r.1 hc) rfl

/-- **One step.** The mean weight after any comparison step is at most the weight before it. -/
theorem meanWeight_costStep_leW (input : (SourceCostSpec D R ι).Domain) (state : DebtState D R ι) :
    meanWeight tg initial (costStep model input state) ≤ weight tg initial state := by
  rcases input with (draw | (bytes | coordinate)) | amount
  · refine meanWeight_le_of_supportW tg initial _ _ fun r hr => ?_
    change r ∈ support ((fun v => (v, state)) <$> (liftM (unifSpec.query draw) : ProbComp _)) at hr
    rw [support_map] at hr
    obtain ⟨v, _, rfl⟩ := hr
    exact le_rfl
  · rw [costStep_ordinary]
    unfold ordinaryStep
    split
    · exact meanWeight_le_of_supportW tg initial _ _ (readOutside_weight_leW tg initial bytes state)
    · split
      · refine meanWeight_le_of_supportW tg initial _ _ fun r hr => ?_
        rcases readOutside_support bytes _ r hr with h | ⟨hc, h⟩
        · rw [h]
          exact weight_le_of_extendsW tg initial (extends_record state _) rfl
        · rw [h]
          exact weight_le_of_extendsW tg initial
            ((extends_record state _).trans (extends_store _ bytes r.1 hc)) rfl
      · split
        · rw [meanWeight_map, meanWeight_sample tg initial _ state (debts_finiteW tg initial state _)]
        · exact meanWeight_le_of_supportW tg initial _ _ (readOutside_weight_leW tg initial bytes state)
  · change meanWeight tg initial (sampleCoordinate coordinate state) ≤ _
    rw [meanWeight_sample tg initial coordinate state (debts_finiteW tg initial state _)]
  · change meanWeight tg initial (pure ((), state) : ProbComp _) ≤ _
    rw [meanWeight, OracleComp.tsum_prEvent_pure_mul]

/-- **Supermartingale.** The expected final weight of an interpreted run is at most the initial
weight. -/
theorem interp_weight_leW {α : Type} (computation : OracleComp (SourceCostSpec D R ι) α) :
    ∀ budget (state : DebtState D R ι),
      ∑' out, Pr{let x ← interp tg initial model computation budget state}[x = out] * weight tg initial out.2 ≤
        weight tg initial state := by
  induction computation using OracleComp.inductionOn with
  | pure value =>
      intro budget state
      rw [interp_pure, OracleComp.tsum_prEvent_pure_mul]
  | query_bind input next ih =>
      intro budget state
      rw [interp_query_bind]
      split_ifs with hcost
      · rw [OracleComp.tsum_prEvent_bind_mul]
        simp only [OracleComp.tsum_prEvent_map_mul]
        calc _ ≤ ∑' r, Pr{let x ← costStep model input state}[x = r] * weight tg initial r.2 :=
              ENNReal.tsum_le_tsum fun r => mul_le_mul_right (ih r.1 _ r.2) _
          _ ≤ _ := meanWeight_costStep_leW tg initial model input state
      · rw [OracleComp.tsum_prEvent_pure_mul]

/-- A pointwise bound on the support turns into the bound times the initial weight. -/
theorem interp_weight_mul_leW {α : Type} (computation : OracleComp (SourceCostSpec D R ι) α) (budget : ℕ)
    (state : DebtState D R ι) (G : Run D ι α × DebtState D R ι → ℝ≥0∞) (K : ℝ≥0∞)
    (hG : ∀ out ∈ support (interp tg initial model computation budget state), G out ≤ K) :
    ∑' out, Pr{let x ← interp tg initial model computation budget state}[x = out] * (weight tg initial out.2 * G out) ≤
      weight tg initial state * K := by
  calc _ ≤ ∑' out, Pr{let x ← interp tg initial model computation budget state}[x = out] *
        (weight tg initial out.2 * K) := by
        refine ENNReal.tsum_le_tsum fun out => ?_
        by_cases hout : out ∈ support (interp tg initial model computation budget state)
        · exact mul_le_mul_right (mul_le_mul_right (hG out hout) _) _
        · rw [(prEvent_eq_zero_of_not_mem_support _) hout, zero_mul, zero_mul]
    _ = (∑' out, Pr{let x ← interp tg initial model computation budget state}[x = out] * weight tg initial out.2) * K := by
        rw [← ENNReal.tsum_mul_right]
        exact tsum_congr fun out => by ring
    _ ≤ _ := mul_le_mul_left (interp_weight_leW tg initial model computation budget state) _

/-! ### Weighted payments -/

/-- A digest query pays the current survival weight. -/
noncomputable def wpays (state : DebtState D R ι) : (SourceCostSpec D R ι).Domain → ℝ≥0∞
  | .inl (.inr (.inl bytes)) => if tg.digest bytes then weight tg initial state else 0
  | _ => 0

/-- Expected weighted payments of an interpreted run. -/
noncomputable def wflag {α : Type} (computation : OracleComp (SourceCostSpec D R ι) α) :
    ℕ → DebtState D R ι → ℝ≥0∞ :=
  OracleComp.construct (C := fun _ => ℕ → DebtState D R ι → ℝ≥0∞) (fun _ _ _ => 0)
    (fun input _ next budget state =>
      if sourceCost input ≤ budget then
        ∑' result, Pr{let x ← costStep model input state}[x = result] *
          (wpays tg initial state input + next result.1 (budget - sourceCost input) result.2)
      else 0) computation

theorem wflag_pure {α : Type} (value : α) (budget : ℕ) (state : DebtState D R ι) :
    wflag tg initial model (pure value : OracleComp (SourceCostSpec D R ι) α) budget state = 0 := rfl

theorem wflag_query_bind {α : Type} (input : (SourceCostSpec D R ι).Domain)
    (next : (SourceCostSpec D R ι).Range input → OracleComp (SourceCostSpec D R ι) α)
    (budget : ℕ) (state : DebtState D R ι) :
    wflag tg initial model (liftM ((SourceCostSpec D R ι).query input) >>= next) budget state =
      if sourceCost input ≤ budget then
        ∑' result, Pr{let x ← costStep model input state}[x = result] *
          (wpays tg initial state input + wflag tg initial model (next result.1) (budget - sourceCost input) result.2)
      else 0 := rfl

theorem wpays_presampleW (x : D) (hk : tg.kind x = .none) (state : DebtState D R ι)
    (input : (SourceCostSpec D R ι).Domain) :
    ∀ s ∈ support (presample x state), wpays tg initial s input = wpays tg initial state input := by
  intro s hs
  rcases input with (draw | (bytes | coordinate)) | amount
  · rfl
  · change (if tg.digest bytes then weight tg initial s else 0) =
      (if tg.digest bytes then weight tg initial state else 0)
    rw [weight_presampleW tg initial x hk state s hs]
  · rfl
  · rfl

/-- The weighted payments of a sequential run split at the end of the first computation. -/
theorem wflag_bind {α β : Type} (first : OracleComp (SourceCostSpec D R ι) α)
    (next : α → OracleComp (SourceCostSpec D R ι) β) :
    ∀ budget (state : DebtState D R ι),
      wflag tg initial model (first >>= next) budget state =
        wflag tg initial model first budget state +
          ∑' o1, Pr{let x ← interp tg initial model first budget state}[x = o1] *
            o1.1.1.elim 0 (fun value => wflag tg initial model (next value) (budget - traceCost o1.1.2.2.1) o1.2) := by
  induction first using OracleComp.inductionOn with
  | pure value =>
      intro budget state
      rw [pure_bind, wflag_pure, interp_pure, OracleComp.tsum_prEvent_pure_mul, zero_add]
      simp only [Option.elim, traceCost, List.map_nil, List.sum_nil, Nat.sub_zero]
  | query_bind input rest ih =>
      intro budget state
      rw [bind_assoc, wflag_query_bind, wflag_query_bind, interp_query_bind]
      split_ifs with hcost
      · rw [OracleComp.tsum_prEvent_bind_mul, ← ENNReal.tsum_add]
        refine tsum_congr fun r => ?_
        rw [OracleComp.tsum_prEvent_map_mul, ih r.1 (budget - sourceCost input) r.2]
        simp only [traceCost_append, recorded_cost, Nat.sub_sub]
        ring
      · rw [OracleComp.tsum_prEvent_pure_mul]
        simp

/-- Presampling an untargeted input does not raise the expected weighted payments. -/
theorem wflag_presample_le (x : D) (hk : tg.kind x = .none) {α : Type}
    (computation : OracleComp (SourceCostSpec D R ι) α) :
    ∀ budget (state : DebtState D R ι),
      ∑' s, Pr{let y ← presample x state}[y = s] * wflag tg initial model computation budget s ≤
        wflag tg initial model computation budget state := by
  induction computation using OracleComp.inductionOn with
  | pure value =>
      intro budget state
      simp only [wflag_pure, mul_zero, tsum_zero, le_refl]
  | query_bind input next ih =>
      intro budget state
      simp only [wflag_query_bind]
      split_ifs with hcost
      · set f : (SourceCostSpec D R ι).Range input × DebtState D R ι → ℝ≥0∞ := fun r =>
          wpays tg initial state input + wflag tg initial model (next r.1) (budget - sourceCost input) r.2 with hf
        have hpay : ∀ s ∈ support (presample x state),
            ∑' r, Pr{let x ← costStep model input s}[x = r] *
              (wpays tg initial s input + wflag tg initial model (next r.1) (budget - sourceCost input) r.2) =
            ∑' r, Pr{let x ← costStep model input s}[x = r] * f r := by
          intro s hs
          rw [wpays_presampleW tg initial x hk state input s hs]
        have hstep : ∑' s, Pr{let y ← presample x state}[y = s] * ∑' r, Pr{let x ← costStep model input s}[x = r] * f r =
            ∑' r, Pr{let x ← costStep model input state}[x = r] *
              ∑' s, Pr{let y ← presample x r.2}[y = s] * f (r.1, s) := by
          have h := presample_costStep model x input state (pure : _ → ProbComp _)
          simp only [bind_pure] at h
          rw [← OracleComp.tsum_prEvent_bind_mul]
          refine (tsum_congr fun r => congrArg (· * f r) ((h).prEvent_eq _)).trans ?_
          rw [OracleComp.tsum_prEvent_bind_mul]
          refine tsum_congr fun r => ?_
          congr 1
          rw [OracleComp.tsum_prEvent_bind_mul]
          refine tsum_congr fun s => ?_
          rw [OracleComp.tsum_prEvent_pure_mul]
        calc _ = ∑' s, Pr{let y ← presample x state}[y = s] * ∑' r, Pr{let x ← costStep model input s}[x = r] * f r := by
              refine tsum_congr fun s => ?_
              by_cases hs : s ∈ support (presample x state)
              · rw [hpay s hs]
              · rw [(prEvent_eq_zero_of_not_mem_support _) hs, zero_mul, zero_mul]
          _ = _ := hstep
          _ ≤ _ := by
              refine ENNReal.tsum_le_tsum fun r => mul_le_mul_right ?_ _
              simp only [hf, mul_add, ENNReal.tsum_add, ENNReal.tsum_mul_right, presample_mass, one_mul]
              exact add_le_add le_rfl (ih r.1 (budget - sourceCost input) r.2)
      · simp only [mul_zero, tsum_zero, le_refl]

/-! ### Weighted saturation -/

section SatW

variable (hcompat : Compatible tg model) (htrunc : UniformTruncation (R := R) tg)
include hcompat htrunc

/-- One step of the weighted saturation: a digest query frees the budget decrement times the
current weight, which pays the weighted baseline. -/
theorem step_goodW (total : ℕ) (htotal : (total : ℝ) + 1 < spaceReal) (payment : ℝ≥0∞)
    (hpayment : ∀ probes remaining, probes + remaining + 1 ≤ total →
      payment ≤ budget probes remaining - budget probes (remaining + 1))
    (input : (SourceCostSpec D R ι).Domain) (state : DebtState D R ι) (probes remaining : ℕ)
    (hinv : Inv tg initial state probes) (hcost : sourceCost input ≤ remaining) (hsum : probes + remaining ≤ total) :
    ∃ probes', probes' + (remaining - sourceCost input) ≤ total ∧
      (∀ result ∈ support (costStep model input state), Inv tg initial result.2 probes') ∧
      budget probes remaining * weight tg initial state + payment * wpays tg initial state input ≤
        budget probes' (remaining - sourceCost input) * meanWeight tg initial (costStep model input state) := by
  have hreal : (probes + remaining : ℝ) + 1 < spaceReal := by
    have h : ((probes + remaining : ℕ) : ℝ) ≤ total := by exact_mod_cast hsum
    push_cast at h
    linarith
  cases input with
  | inr amount =>
      refine ⟨probes, by simp only [sourceCost]; omega, ?_, ?_⟩
      · intro result hresult
        change result ∈ support (pure ((), state) : ProbComp _) at hresult
        rw [support_pure, Set.mem_singleton_iff] at hresult
        subst hresult
        exact hinv
      · change _ + payment * 0 ≤ _ * meanWeight tg initial (pure ((), state) : ProbComp _)
        rw [meanWeight, OracleComp.tsum_prEvent_pure_mul, mul_zero, add_zero]
        gcongr
        exact budget_le_of_le probes _ _ (Nat.sub_le _ _) (by linarith)
  | inl input =>
      cases input with
      | inl draw =>
          refine ⟨probes, by simp only [sourceCost]; omega, ?_, ?_⟩
          · intro result hresult
            rw [costStep_inl, lazyStep_draw, support_map] at hresult
            obtain ⟨value, _, rfl⟩ := hresult
            exact hinv
          · change _ + payment * 0 ≤ _
            rw [costStep_inl, lazyStep_draw, meanWeight, OracleComp.tsum_prEvent_map_mul]
            dsimp only
            rw [ENNReal.tsum_mul_right, OracleComp.tsum_prEvent_eq_one _, one_mul,
              mul_zero, add_zero]
            simp only [sourceCost, Nat.sub_zero, le_refl]
      | inr input =>
          cases input with
          | inr coordinate =>
              refine ⟨probes, by simp only [sourceCost]; omega, ?_, ?_⟩
              · intro result hresult
                rw [costStep_inl, lazyStep_reveal] at hresult
                rw [sampleCoordinate_expose coordinate state result hresult]
                exact hinv.expose tg initial _ _
              · change _ + payment * 0 ≤ _
                rw [costStep_inl, lazyStep_reveal, meanWeight_sample tg initial coordinate state (hinv.finite _),
                  mul_zero, add_zero]
                simp only [sourceCost, Nat.sub_zero, le_refl]
          | inl bytes =>
              have hone : sourceCost (D := D) (R := R) (ι := ι) (.inl (.inr (.inl bytes))) = 1 := rfl
              rw [hone] at hcost ⊢
              obtain ⟨rest, rfl⟩ : ∃ rest, remaining = rest + 1 := ⟨remaining - 1, by omega⟩
              simp only [Nat.add_sub_cancel]
              have hpays : wpays tg initial state (.inl (.inr (.inl bytes))) =
                  if tg.digest bytes then weight tg initial state else 0 := rfl
              rw [hpays]
              have hbudget : (probes + rest + 1 : ℝ) < spaceReal := by push_cast at hreal; linarith
              by_cases hdigest : tg.digest bytes
              · have hp := hcompat.digestParse bytes hdigest
                have hk := hcompat.digestKind bytes hdigest
                refine ⟨probes, by omega, ?_, ?_⟩
                · intro result hresult
                  rw [costStep_inl, lazyStep_unparsed model bytes state hp] at hresult
                  exact inv_readOutside_none tg initial bytes state probes hinv hk result hresult
                · rw [costStep_inl, lazyStep_unparsed model bytes state hp,
                    meanWeight_readOutside_none tg initial bytes state hk hinv.prepared, ite_eq_left hdigest]
                  calc budget probes (rest + 1) * weight tg initial state + payment * weight tg initial state
                      ≤ budget probes (rest + 1) * weight tg initial state +
                          (budget probes rest - budget probes (rest + 1)) * weight tg initial state :=
                        add_le_add le_rfl (mul_le_mul_left (hpayment probes rest (by omega)) _)
                    _ = budget probes rest * weight tg initial state := by
                        rw [← add_mul, add_tsub_cancel_of_le (budget_succ_le probes rest (by linarith))]
              · rw [ite_eq_right hdigest, mul_zero, add_zero]
                cases hp : model.parse bytes with
                | none =>
                    refine ⟨probes + 1, by omega, ?_, ?_⟩
                    · intro result hresult
                      rw [costStep_inl, lazyStep_unparsed model bytes state hp] at hresult
                      exact inv_readOutside tg initial bytes state probes hinv result hresult
                    · rw [costStep_inl, lazyStep_unparsed model bytes state hp]
                      exact readOutside_step tg initial htrunc bytes state probes rest hinv hbudget
                | some query =>
                    cases hk : state.known (model.incoming query.1) with
                    | none =>
                        refine ⟨probes + 1, by omega, ?_, ?_⟩
                        · intro result hresult
                          rw [costStep_inl, lazyStep_guess model bytes state query hp hk] at hresult
                          exact inv_guess tg initial bytes state _ probes hinv (hcompat.row bytes query hp)
                            result hresult
                        · rw [costStep_inl, lazyStep_guess model bytes state query hp hk]
                          refine probe_inequality probes rest _ _ hbudget ?_
                          have hprobes : (probes : ℝ) < spaceReal := by
                            linarith [(Nat.cast_nonneg rest : (0 : ℝ) ≤ rest)]
                          have hrecord := weight_record tg initial state (model.incoming query.1, query.2) hk
                            (hinv.finite _) probes (hinv.bound _) hprobes
                          have hfinite : ∀ coordinate,
                              (debts tg initial (state.record (model.incoming query.1, query.2)) coordinate).Finite :=
                            fun coordinate => debts_finiteW tg initial _ coordinate
                          have hmean := weight_readOutside_mean tg initial htrunc bytes
                            (state.record (model.incoming query.1, query.2)) hinv.prepared hfinite
                          calc probeFactor probes ^ 2 * weight tg initial state
                              = probeFactor probes * (probeFactor probes * weight tg initial state) := by ring
                            _ ≤ (1 - 1 / space) *
                                weight tg initial (state.record (model.incoming query.1, query.2)) := by
                                gcongr
                                exact probeFactor_le_fresh probes hprobes
                            _ ≤ _ := hmean
                    | some canonical =>
                        by_cases heq : query.2 = canonical
                        · refine ⟨probes, by omega, ?_, ?_⟩
                          · intro result hresult
                            rw [costStep_inl, lazyStep_canonical model bytes state query hp canonical hk heq,
                              support_map] at hresult
                            obtain ⟨sample, hsample, rfl⟩ := hresult
                            rw [sampleCoordinate_expose _ state sample hsample]
                            exact hinv.expose tg initial _ _
                          · rw [costStep_inl, lazyStep_canonical model bytes state query hp canonical hk heq,
                              meanWeight_map, meanWeight_sample tg initial _ state (hinv.finite _)]
                            gcongr
                            exact budget_succ_le probes rest (by linarith)
                        · refine ⟨probes + 1, by omega, ?_, ?_⟩
                          · intro result hresult
                            rw [costStep_inl, lazyStep_other model bytes state query hp canonical hk heq] at hresult
                            exact inv_readOutside tg initial bytes state probes hinv result hresult
                          · rw [costStep_inl, lazyStep_other model bytes state query hp canonical hk heq]
                            exact readOutside_step tg initial htrunc bytes state probes rest hinv hbudget

/-- **Weighted saturation on the interpreter.** The budget-weighted survival weight plus the
weighted baseline payments never exceed the expected final survival weight. -/
theorem saturationW (total : ℕ) (htotal : (total : ℝ) + 1 < spaceReal) (payment : ℝ≥0∞)
    (hpayment : ∀ probes remaining, probes + remaining + 1 ≤ total →
      payment ≤ budget probes remaining - budget probes (remaining + 1))
    {α : Type} (computation : OracleComp (SourceCostSpec D R ι) α) :
    ∀ (remaining : ℕ) (state : DebtState D R ι) (probes : ℕ),
      Inv tg initial state probes → probes + remaining ≤ total →
      budget probes remaining * weight tg initial state +
          payment * wflag tg initial model computation remaining state ≤
        ∑' out, Pr{let x ← interp tg initial model computation remaining state}[x = out] * weight tg initial out.2 := by
  induction computation using OracleComp.inductionOn with
  | pure value =>
      intro remaining state probes _ hsum
      rw [wflag_pure, interp_pure, OracleComp.tsum_prEvent_pure_mul, mul_zero, add_zero]
      refine mul_le_of_le_one_left' (budget_le_one probes remaining ?_)
      have h : ((probes + remaining : ℕ) : ℝ) ≤ total := by exact_mod_cast hsum
      push_cast at h
      linarith
  | query_bind input next ih =>
      intro remaining state probes hinv hsum
      rw [wflag_query_bind, interp_query_bind]
      split_ifs with hcost
      · obtain ⟨probes', hsum', hsupport, hstep⟩ := step_goodW tg initial model hcompat htrunc total htotal
          payment hpayment input state probes remaining hinv hcost hsum
        rw [OracleComp.tsum_prEvent_bind_mul]
        simp only [OracleComp.tsum_prEvent_map_mul]
        exact combine (costStep model input state) (fun result => weight tg initial result.2)
          (fun result => wflag tg initial model (next result.1) (remaining - sourceCost input) result.2)
          (fun result => ∑' out, Pr{let x ← (interp tg initial model (next result.1)
            (remaining - sourceCost input) result.2)}[x = out] * weight tg initial out.2) _ payment _ _ hstep
          fun result hresult => ih result.1 _ result.2 probes' (hsupport result hresult) hsum'
      · rw [OracleComp.tsum_prEvent_pure_mul, mul_zero, add_zero]
        refine mul_le_of_le_one_left' (budget_le_one probes remaining ?_)
        have h : ((probes + remaining : ℕ) : ℝ) ≤ total := by exact_mod_cast hsum
        push_cast at h
        linarith

/-- **Weighted saturation from the start.** -/
theorem saturationW_start (total : ℕ) (htotal : (total : ℝ) + 1 < spaceReal) (payment : ℝ≥0∞)
    (hpayment : ∀ probes remaining, probes + remaining + 1 ≤ total →
      payment ≤ budget probes remaining - budget probes (remaining + 1))
    {α : Type} (computation : OracleComp (SourceCostSpec D R ι) α) (known : Knowledge ι) :
    budget 0 total + payment * wflag tg initial model computation total (DebtState.start initial known) ≤
      ∑' out, Pr{let x ← interp tg initial model computation total (DebtState.start initial known)}[x = out] *
        weight tg initial out.2 := by
  have h := saturationW tg initial model hcompat htrunc total htotal payment hpayment computation total
    (DebtState.start initial known) 0 (inv_start tg initial known) (by omega)
  rwa [weight_start, mul_one] at h

end SatW

/-! ### Two reads, weighted -/

/-- **Two reads, weighted.** As `two_reads_bound₂`, with the final survival weight in the
integrand: untargeted reads keep the weight, and the rest of the run lowers it in expectation. -/
theorem two_reads_bound₂W {β : Type} (x0 x1 : D) (hne : x0 ≠ x1) (hp0 : model.parse x0 = none)
    (hp1 : model.parse x1 = none) (hk1 : tg.kind x1 = .none) (state : DebtState D R ι) (u0 : R)
    (hc0 : state.cache x0 = some u0)
    (rest : R → R → OracleComp (SourceCostSpec D R ι) β)
    (havoid : ∀ a b, Avoids (fun x => x = x0 ∨ x = x1) (rest a b)) (g : R → R → ℝ≥0∞) (budget : ℕ) :
    ∑' out, Pr{let x ← (interp tg initial model
        (liftM ((SourceCostSpec D R ι).query (.inl (.inr (.inl x0)))) >>= fun a =>
          liftM ((SourceCostSpec D R ι).query (.inl (.inr (.inl x1)))) >>= fun b => rest a b) budget state)}[x = out] *
        (weight tg initial out.2 *
          (if out.1.1.isSome then (out.2.cache x0).elim 0 (fun a => (out.2.cache x1).elim 0 (g a)) else 0)) ≤
      weight tg initial state * (state.cache x1).elim (∑' u, Pr{let x ← ($ᵗ R : ProbComp R)}[x = u] * g u0 u) (g u0) := by
  have hinner : ∀ a b (s : DebtState D R ι) b', s.cache x0 = some u0 → s.cache x1 = some b →
      ∑' out, Pr{let x ← interp tg initial model (rest a b) b' s}[x = out] *
        (weight tg initial out.2 *
          (if out.1.1.isSome then (out.2.cache x0).elim 0 (fun a => (out.2.cache x1).elim 0 (g a)) else 0)) ≤
          weight tg initial s * g u0 b := by
    intro a b s b' hs0 hs1
    refine interp_weight_mul_leW tg initial model (rest a b) b' s _ _ fun out hout => ?_
    have hk0 := interp_avoids_cache tg initial model _ (rest a b) (havoid a b) b' s out hout x0 (Or.inl rfl)
    have hk1' := interp_avoids_cache tg initial model _ (rest a b) (havoid a b) b' s out hout x1 (Or.inr rfl)
    split_ifs
    · rw [hk0, hs0, hk1', hs1]
      rfl
    · exact bot_le
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
          rw [readOutside_fresh x1 state hc1, bind_map_left, OracleComp.tsum_prEvent_bind_mul, ← ENNReal.tsum_mul_left]
          refine ENNReal.tsum_le_tsum fun u => ?_
          rw [OracleComp.tsum_prEvent_map_mul, mul_left_comm]
          refine mul_le_mul_right ?_ _
          have h := hinner u0 u (state.store x1 u) (budget - 1 - 1) (by rw [store_cache_ne state x1 x0 hne u]; exact hc0)
            (by simp [DebtState.store])
          rwa [weight_store_untargetedW tg initial state x1 u hk1] at h
    · rw [OracleComp.tsum_prEvent_pure_mul]
      simp
  · rw [OracleComp.tsum_prEvent_pure_mul]
    simp

/-! ### The weighted baseline -/

/-- The weighted baseline payment per digest query for a total budget `q`:
`(2 (N - q) + 1) / N^2`, about `2^-127 (1 - x)` with `x = q / N`. -/
noncomputable def baselineW (total : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal ((2 * (spaceReal - total) + 1) / spaceReal ^ 2)

theorem baselineW_ne_top (total : ℕ) : baselineW total ≠ ⊤ := ENNReal.ofReal_ne_top

/-- The weighted baseline fits in every budget decrement. -/
theorem baselineW_payment (total : ℕ) (htotal : (total : ℝ) ≤ spaceReal) :
    ∀ probes remaining, probes + remaining + 1 ≤ total →
      baselineW total ≤ budget probes remaining - budget probes (remaining + 1) := by
  intro probes remaining hle
  have hN := spaceReal_pos
  have hreal : (probes : ℝ) + remaining + 1 ≤ total := by exact_mod_cast hle
  have hp : (0 : ℝ) ≤ probes := Nat.cast_nonneg _
  have hr : (0 : ℝ) ≤ remaining := Nat.cast_nonneg _
  have hden : 0 < spaceReal - probes := by linarith
  unfold baselineW
  rw [budget, budget, ← ENNReal.ofReal_sub _ (sq_nonneg _)]
  apply ENNReal.ofReal_le_ofReal
  have hdiff : ((spaceReal - probes - remaining) / (spaceReal - probes)) ^ 2 -
      ((spaceReal - probes - (remaining + 1 : ℕ)) / (spaceReal - probes)) ^ 2 =
      (2 * (spaceReal - probes - remaining) - 1) / (spaceReal - probes) ^ 2 := by
    push_cast
    field_simp
    ring
  rw [hdiff]
  have hnum : 2 * (spaceReal - total) + 1 ≤ 2 * (spaceReal - probes - remaining) - 1 := by linarith
  have hnum0 : 0 ≤ 2 * (spaceReal - total) + 1 := by linarith
  have hsq : (spaceReal - probes) ^ 2 ≤ spaceReal ^ 2 := by
    have : spaceReal - probes ≤ spaceReal := by linarith
    nlinarith
  calc (2 * (spaceReal - total) + 1) / spaceReal ^ 2 ≤ (2 * (spaceReal - total) + 1) / (spaceReal - probes) ^ 2 :=
        div_le_div_of_nonneg_left hnum0 (pow_pos hden 2) hsq
    _ ≤ _ := div_le_div_of_nonneg_right hnum (by positivity)

end Sphincs.Security.HiddenDebt
