import Sphincs.BridgeInterpSupport
import Sphincs.BridgeFleafLinear

/-! **An exposed value is uniform.** In an interpreted run started with coordinate `c` unexposed,
the final value of `c` equals a given digest `t0` with probability `2^-128` times the probability
that `c` is exposed at all: `c` is exposed by exactly one step, which samples it uniformly, and its
value never changes afterwards. Nothing is assumed about the computation. -/

open OracleComp OracleSpec ENNReal

namespace Sphincs.Security.HiddenDebt

open HiddenOutside HiddenCost HiddenReveal

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
attribute [local instance] Classical.propDecidable

variable {D R A ι : Type} [Fintype ι] [SampleableType R]
noncomputable local instance exposeMeanDecEqInput : DecidableEq D := Classical.decEq _
noncomputable local instance exposeMeanDecEqCoordinate : DecidableEq ι := Classical.decEq _

variable (tg : Targeting D R ι) (initial : Cache D R) (model : HiddenRows.Model D R A ι)

/-- One digest's share. -/
noncomputable def shareν : ℝ≥0∞ := ((2 : ℝ≥0∞) ^ 128)⁻¹

theorem sum_digest_eq (t0 : Digest) :
    ∑' v, Pr{let x ← ($ᵗ Digest : ProbComp Digest)}[x = v] * (if v = t0 then (1 : ℝ≥0∞) else 0) = shareν := by
  have h : ∀ v, Pr{let x ← ($ᵗ Digest : ProbComp Digest)}[x = v] = shareν := fun v => by
    rw [SampleableType.prEvent_uniformSample_eq_singleton, card_digest]
    simp [shareν]
    norm_num
  simp only [h, mul_ite, mul_one, mul_zero]
  rw [tsum_ite_eq]

theorem tsum_digest_one : ∑' v, Pr{let x ← ($ᵗ Digest : ProbComp Digest)}[x = v] = 1 :=
  OracleComp.tsum_prEvent_eq_one _

omit [Fintype ι] [SampleableType R] in
/-- Sampling a coordinate exposes the target value with its share. -/
theorem sample_value_le (c c' : ι) (s : DebtState D R ι) (hc : s.known c = none) (t0 : Digest) :
    ∑' r, Pr{let x ← sampleCoordinate c' s}[x = r] * (if r.2.known c = some t0 then (1 : ℝ≥0∞) else 0) ≤
      shareν * ∑' r, Pr{let x ← sampleCoordinate c' s}[x = r] * (if r.2.known c ≠ none then (1 : ℝ≥0∞) else 0) := by
  cases hk : s.known c' with
  | some w =>
      rw [sampleCoordinate_known c' s w hk, OracleComp.tsum_prEvent_pure_mul, OracleComp.tsum_prEvent_pure_mul]
      simp [hc]
  | none =>
      rw [sampleCoordinate_unknown c' s hk, OracleComp.tsum_prEvent_map_mul, OracleComp.tsum_prEvent_map_mul]
      by_cases hcc : c' = c
      · subst hcc
        have h1 : ∀ v : Digest, (s.expose c' v).known c' = some v := fun v => by
          simp [DebtState.expose, QueryCache.cacheQuery_self]
        simp only [h1, Option.some.injEq, ne_eq, reduceCtorEq, not_false_eq_true, ite_true, mul_one]
        rw [tsum_digest_one, mul_one, sum_digest_eq]
      · have h1 : ∀ v : Digest, (s.expose c' v).known c = s.known c := fun v => by
          simp only [DebtState.expose]
          exact QueryCache.cacheQuery_of_ne (cache := s.known) v (Ne.symm hcc)
        simp [h1, hc, -SampleableType.prEvent_uniformSample]

omit [Fintype ι] in
/-- **One step.** -/
theorem costStep_value_le (input : (SourceCostSpec D R ι).Domain) (s : DebtState D R ι) (c : ι)
    (hc : s.known c = none) (t0 : Digest) :
    ∑' r, Pr{let x ← costStep model input s}[x = r] * (if r.2.known c = some t0 then (1 : ℝ≥0∞) else 0) ≤
      shareν * ∑' r, Pr{let x ← costStep model input s}[x = r] * (if r.2.known c ≠ none then (1 : ℝ≥0∞) else 0) := by
  have hzero : ∀ (step : ProbComp ((SourceCostSpec D R ι).Range input × DebtState D R ι)),
      (∀ r ∈ support step, r.2.known c = s.known c) →
      ∑' r, Pr{let x ← step}[x = r] * (if r.2.known c = some t0 then (1 : ℝ≥0∞) else 0) = 0 := by
    intro step hstep
    refine ENNReal.tsum_eq_zero.2 fun r => ?_
    by_cases hr : r ∈ support step
    · rw [hstep r hr, hc]; simp
    · rw [(prEvent_eq_zero_of_not_mem_support _) hr, zero_mul]
  rcases input with (draw | (bytes | coordinate)) | amount
  · refine le_of_eq_of_le (hzero _ fun r hr => ?_) bot_le
    rw [costStep_inl, lazyStep_draw, support_map] at hr
    obtain ⟨_, _, rfl⟩ := hr
    rfl
  · rw [costStep_inl]
    cases hp : model.parse bytes with
    | none =>
        rw [lazyStep_unparsed model bytes s hp]
        exact le_of_eq_of_le (hzero _ fun r hr => congrFun (congrArg QueryCache.toFn (readOutside_known bytes s r hr)) c) bot_le
    | some q =>
        cases hk : s.known (model.incoming q.1) with
        | none =>
            rw [lazyStep_guess model bytes s q hp hk]
            exact le_of_eq_of_le (hzero _ fun r hr => congrFun (congrArg QueryCache.toFn (readOutside_known bytes _ r hr)) c) bot_le
        | some canonical =>
            by_cases heq : q.2 = canonical
            · rw [lazyStep_canonical model bytes s q hp canonical hk heq, OracleComp.tsum_prEvent_map_mul,
                OracleComp.tsum_prEvent_map_mul]
              exact sample_value_le c (model.outgoing q.1) s hc t0
            · rw [lazyStep_other model bytes s q hp canonical hk heq]
              exact le_of_eq_of_le (hzero _ fun r hr => congrFun (congrArg QueryCache.toFn (readOutside_known bytes s r hr)) c) bot_le
  · rw [costStep_inl, lazyStep_reveal]
    exact sample_value_le c coordinate s hc t0
  · refine le_of_eq_of_le (hzero _ fun r hr => ?_) bot_le
    change r ∈ support (pure ((), s) : ProbComp _) at hr
    rw [support_pure, Set.mem_singleton_iff] at hr
    rw [hr]

/-- **An exposed value is uniform**, over a whole interpreted run. -/
theorem interp_value_le {α : Type} (computation : OracleComp (SourceCostSpec D R ι) α) (c : ι) (t0 : Digest) :
    ∀ budget (s : DebtState D R ι), s.known c = none →
      ∑' out, Pr{let x ← interp tg initial model computation budget s}[x = out] *
          (if out.2.known c = some t0 then (1 : ℝ≥0∞) else 0) ≤
        shareν * ∑' out, Pr{let x ← interp tg initial model computation budget s}[x = out] *
          (if out.2.known c ≠ none then (1 : ℝ≥0∞) else 0) := by
  induction computation using OracleComp.inductionOn with
  | pure value =>
      intro budget s hc
      rw [interp_pure, OracleComp.tsum_prEvent_pure_mul, OracleComp.tsum_prEvent_pure_mul]
      simp [hc]
  | query_bind input next ih =>
      intro budget s hc
      rw [interp_query_bind]
      split_ifs with hcost
      swap
      · rw [OracleComp.tsum_prEvent_pure_mul, OracleComp.tsum_prEvent_pure_mul]
        simp [hc]
      rw [OracleComp.tsum_prEvent_bind_mul, OracleComp.tsum_prEvent_bind_mul]
      simp only [OracleComp.tsum_prEvent_map_mul]
      set E : (SourceCostSpec D R ι).Range input × DebtState D R ι → ℝ≥0∞ := fun r =>
        ∑' out, Pr{let x ← interp tg initial model (next r.1) (budget - sourceCost input) r.2}[x = out] *
          (if out.2.known c = some t0 then (1 : ℝ≥0∞) else 0) with hE
      set F : (SourceCostSpec D R ι).Range input × DebtState D R ι → ℝ≥0∞ := fun r =>
        ∑' out, Pr{let x ← interp tg initial model (next r.1) (budget - sourceCost input) r.2}[x = out] *
          (if out.2.known c ≠ none then (1 : ℝ≥0∞) else 0) with hF
      have hpt : ∀ r ∈ support (costStep model input s),
          E r ≤ (if r.2.known c = some t0 then 1 else 0) + shareν * (if r.2.known c = none then F r else 0) := by
        intro r _
        cases hrk : r.2.known c with
        | none =>
            simp only [reduceCtorEq, ite_false, ite_true, zero_add]
            exact ih r.1 _ r.2 hrk
        | some v =>
            simp only [reduceCtorEq, ite_false, add_zero, mul_zero]
            have hstay : ∀ out ∈ support (interp tg initial model (next r.1) (budget - sourceCost input) r.2),
                out.2.known c = some v := fun out hout =>
              (interp_extends tg initial model (next r.1) _ r.2 out hout).2.1 c v hrk
            calc E r ≤ ∑' out, Pr{let x ← interp tg initial model (next r.1) (budget - sourceCost input) r.2}[x = out] *
                  (if some v = some t0 then (1 : ℝ≥0∞) else 0) := by
                  refine ENNReal.tsum_le_tsum fun out => ?_
                  by_cases hout : out ∈ support (interp tg initial model (next r.1) (budget - sourceCost input) r.2)
                  · rw [hstay out hout]
                  · rw [(prEvent_eq_zero_of_not_mem_support _) hout, zero_mul, zero_mul]
              _ ≤ (if some v = some t0 then 1 else 0) := by
                  rw [ENNReal.tsum_mul_right]
                  exact mul_le_of_le_one_left' (OracleComp.tsum_prEvent_le_one _)
      have hFeq : ∀ r ∈ support (costStep model input s), r.2.known c ≠ none →
          F r = 1 := by
        intro r _ hr
        obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.1 hr
        have hstay : ∀ out ∈ support (interp tg initial model (next r.1) (budget - sourceCost input) r.2),
            out.2.known c ≠ none := fun out hout => by
          rw [(interp_extends tg initial model (next r.1) _ r.2 out hout).2.1 c v hv]
          exact Option.some_ne_none _
        calc F r = ∑' out, Pr{let x ← interp tg initial model (next r.1) (budget - sourceCost input) r.2}[x = out] := by
              refine tsum_congr fun out => ?_
              by_cases hout : out ∈ support (interp tg initial model (next r.1) (budget - sourceCost input) r.2)
              · rw [ite_eq_left (hstay out hout), mul_one]
              · rw [(prEvent_eq_zero_of_not_mem_support _) hout, zero_mul]
          _ = 1 := interp_mass tg initial model (next r.1) _ r.2
      calc ∑' r, Pr{let x ← costStep model input s}[x = r] * E r
          ≤ ∑' r, Pr{let x ← costStep model input s}[x = r] *
              ((if r.2.known c = some t0 then 1 else 0) + shareν * (if r.2.known c = none then F r else 0)) := by
            refine ENNReal.tsum_le_tsum fun r => ?_
            by_cases hr : r ∈ support (costStep model input s)
            · exact mul_le_mul_right (hpt r hr) _
            · rw [(prEvent_eq_zero_of_not_mem_support _) hr, zero_mul, zero_mul]
        _ = ∑' r, Pr{let x ← costStep model input s}[x = r] * (if r.2.known c = some t0 then 1 else 0) +
            shareν * ∑' r, Pr{let x ← costStep model input s}[x = r] * (if r.2.known c = none then F r else 0) := by
            simp only [mul_add, ENNReal.tsum_add]
            congr 1
            rw [← ENNReal.tsum_mul_left]
            exact tsum_congr fun r => by ring
        _ ≤ shareν * ∑' r, Pr{let x ← costStep model input s}[x = r] * (if r.2.known c ≠ none then 1 else 0) +
            shareν * ∑' r, Pr{let x ← costStep model input s}[x = r] * (if r.2.known c = none then F r else 0) :=
            add_le_add (costStep_value_le model input s c hc t0) le_rfl
        _ = shareν * ∑' r, Pr{let x ← costStep model input s}[x = r] * F r := by
            rw [← mul_add, ← ENNReal.tsum_add]
            congr 1
            refine tsum_congr fun r => ?_
            by_cases hr : r ∈ support (costStep model input s)
            · by_cases hn : r.2.known c = none
              · rw [ite_eq_right (fun h => h hn), ite_eq_left hn, mul_zero, zero_add]
              · rw [ite_eq_left hn, ite_eq_right hn, mul_zero, add_zero, hFeq r hr hn, mul_one]
            · rw [(prEvent_eq_zero_of_not_mem_support _) hr, zero_mul, zero_mul, zero_mul, add_zero]

end Sphincs.Security.HiddenDebt
