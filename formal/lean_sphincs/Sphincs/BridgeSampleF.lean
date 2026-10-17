import Sphincs.BridgeA4Final
import Sphincs.BridgeAssemblyA
import Sphincs.BridgeForsGameOnce
import Sphincs.BridgeForsAssemblyOnce
import Sphincs.H0NearOpt

/-! **One sample of the small-budget route.** On the stopped experiment with the above-word values
exposed, a correct guess or the refined bad event of a valid finished run is a payoff event of the
linear potential, the event of the contact bound A4 against the completed table, or a cover. The
linear potential leaves `(ρ - 1 - x) 2^-128` per forest step query unused; A4 takes
`2^-128 (N rate + 1 - κ)` of it, which fits once `κ ≥ 2 - ρ + x + N rate`. -/

open OracleComp OracleSpec ENNReal

namespace Sphincs.Security.ForsPotential

open Concrete HiddenGraph HiddenCost HiddenDebt GraphView Domination ForestPrice ForestSigner HiddenReveal
  SphincsFors.Security.Domination
open HiddenBridge PotentialA

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option linter.constructorNameAsVariable false
attribute [local instance] Classical.propDecidable

variable [Params]

open Completeness SeedModel Graph Assembly Reduce Internalize in
attribute [local instance] sampleCellFintypeInst sampleCellDecEq hiddenTableSampleable highsSampleable
  remainingSampleable

/-! ### Flagged touches are digest queries -/

section Flagged

variable {D R A ι : Type} [Fintype ι] [SampleableType R]
variable (tg : Targeting D R ι) (initial : HiddenOutside.Cache D R) (model : HiddenRows.Model D R A ι)

omit [Params] [Fintype ι] [SampleableType R] in
theorem flaggedCount_touch_leF (state : DebtState D R ι) (input : (SourceCostSpec D R ι).Domain) :
    flaggedCount tg (touch tg initial state input) ≤ digestCount tg (recorded input) := by
  rcases input with (draw | (bytes | coordinate)) | amount
  · simp [touch, flaggedCount, recorded, digestCount]
  · by_cases hd : tg.digest bytes
    · simp only [touch, flaggedCount, recorded, digestCount, hd, List.filter_cons, List.filter_nil]
      split_ifs <;> simp_all
    · simp [touch, flaggedCount, recorded, digestCount, hd]
  · simp [touch, flaggedCount, recorded, digestCount]
  · simp [touch, flaggedCount, recorded, digestCount]

omit [Params] [Fintype ι] in
theorem flagged_le_digestF {α : Type} (comp : OracleComp (SourceCostSpec D R ι) α) :
    ∀ budget s, ∀ out ∈ support (interp tg initial model comp budget s),
      flaggedCount tg out.1.2.2.2 ≤ digestCount tg out.1.2.2.1 := by
  induction comp using OracleComp.inductionOn with
  | pure value =>
      intro budget s out hout
      rw [interp_pure, support_pure, Set.mem_singleton_iff] at hout
      subst hout
      simp [flaggedCount, digestCount]
  | query_bind input next ih =>
      intro budget s out hout
      rw [interp_query_bind] at hout
      split_ifs at hout with hcost
      · rw [support_bind] at hout
        simp only [Set.mem_iUnion, support_map, Set.mem_image] at hout
        obtain ⟨result, hresult, inner, hinner, rfl⟩ := hout
        simp only [flaggedCount_append, digestCount_append]
        exact Nat.add_le_add (flaggedCount_touch_leF tg initial s input) (ih result.1 _ _ inner hinner)
      · rw [support_pure, Set.mem_singleton_iff] at hout
        subst hout
        simp [flaggedCount, digestCount]

omit [Params] [Fintype ι] in
theorem expectedFlagged_le_digestF {α : Type} (comp : OracleComp (SourceCostSpec D R ι) α) (budget : ℕ)
    (s : DebtState D R ι) :
    expectedFlagged tg initial model comp budget s ≤
      ∑' out, Pr[= out | interp tg initial model comp budget s] * (digestCount tg out.1.2.2.1 : ℝ≥0∞) := by
  unfold expectedFlagged
  refine ENNReal.tsum_le_tsum fun out => ?_
  by_cases hout : out ∈ support (interp tg initial model comp budget s)
  · exact mul_le_mul_right (by exact_mod_cast flagged_le_digestF tg initial model comp budget s out hout) _
  · rw [probOutput_eq_zero_of_not_mem_support hout, zero_mul, zero_mul]

end Flagged

/-! ### The pointwise split of the refined bad event -/

section Pointwise

open Completeness SeedModel Graph Assembly Reduce Internalize

variable (parameterOutput : HashOutput) (fixed : HiddenGraph.Table) (highs : CoordinateHighs)
  (remaining : RemainingOutputs) (prepared : (Index → Option (Counter × Encoding)) × QueryCache HashSpec)
  (hprepared : prepared ∈ support (preparation parameterOutput fixed highs remaining))
  (known : Knowledge Coordinate)
  (hk : known ∈ support (exposeR (aboveList (truncateHash parameterOutput) prepared.1)
    (knownOf (truncateHash parameterOutput) fixed)))
  (ρ : ℝ) (adversary : Adversary) (q : ℕ)

include hprepared hk in
/-- **Pointwise split.** A correct guess or the refined bad event of a valid finished run is a
payoff event of the linear potential, the contact event A4, or a cover without a decided hit. -/
theorem small_pointwiseF (out : Run HashInput Coordinate HiddenBridge.Outcome × State)
    (hout : out ∈ support (interp (targetingA parameterOutput fixed highs remaining prepared.1) prepared.2
      (sampleModel parameterOutput highs)
      (costGameX (truncateHash parameterOutput) (sampleData parameterOutput fixed highs remaining)
        (internalize adversary)) q (DebtState.start prepared.2 known)))
    (T : Coordinate → Digest) (hTe : tableExtending out.2.known T = T)
    (h : CorrectGuess T out.2 ∨ badAV parameterOutput fixed highs remaining prepared.1 T
      (((out.1.1, out.1.2.1), out.1.2.2.1), out.2.cache)) :
    payoffA parameterOutput fixed highs remaining prepared known ρ T out.2 = 1 ∨
      (∃ outcome, out.1.1 = some outcome ∧ SigningTranscript.Valid outcome.2.1 ∧
        A4ev (ctxA parameterOutput fixed highs remaining prepared known ρ)
          (sampleData parameterOutput fixed highs remaining).root T out.2 outcome out.1.2.1) ∨
      finalValue (truncateHash parameterOutput) (sampleData parameterOutput fixed highs remaining)
        (targetingA parameterOutput fixed highs remaining prepared.1) prepared.2 [] out = 1 := by
  set K := ctxA parameterOutput fixed highs remaining prepared known ρ with hK
  have hinv := inv_final parameterOutput fixed highs remaining prepared known ρ hk
    (targetingA parameterOutput fixed highs remaining prepared.1) _ q out hout
  have hfix := knownOf_extending_final (parameterOutput := parameterOutput) (fixed := fixed) (highs := highs)
    (prepared := prepared) (known := known) hk (tg := targetingA parameterOutput fixed highs remaining prepared.1)
    (comp := costGameX (truncateHash parameterOutput) (sampleData parameterOutput fixed highs remaining)
      (internalize adversary)) (total := q) out hout T hTe
  have hpay : Hit K.tg prepared.2 T out.2 → payoffA parameterOutput fixed highs remaining prepared known ρ T out.2 = 1 := by
    intro hh
    unfold payoffA Ctx.payoff
    exact if_pos (Or.inl hh)
  rcases h with hg | ⟨hbad, outcome, hres, hvalid⟩
  · exact Or.inl (hpay (hit_of_correctGuess parameterOutput fixed highs remaining prepared known ρ out.2 T hTe hg))
  · rcases badA_split parameterOutput fixed highs remaining prepared hprepared known ρ out.2 hinv T hTe hfix
      out.1.1 out.1.2.1 out.1.2.2.1 hbad with hp | ⟨index, c, sp, j, a, i, t, hrev, hrec⟩ | ⟨outcome', hres', hnear | hcov⟩
    · exact Or.inl hp
    · exact Or.inr (Or.inl ⟨outcome, hres, hvalid, Or.inl ⟨index, c, sp, j, a, i, t, hrev, hrec⟩⟩)
    · exact Or.inr (Or.inl ⟨outcome', hres', hnear.1, Or.inr hnear⟩)
    · by_cases hreal : Realized K.tg prepared.2 out.2
      · exact Or.inl (hpay (Or.inl hreal))
      · refine Or.inr (Or.inr ?_)
        unfold finalValue
        rw [hres']
        simp only [Option.elim, List.nil_append]
        exact if_pos ⟨hcov, hreal⟩

end Pointwise

/-! ### Helpers -/

section Helpers

open Completeness SeedModel Graph Assembly Reduce Internalize

theorem targetingA_msgF (parameterOutput : HashOutput) (fixed : HiddenGraph.Table) (highs : CoordinateHighs)
    (remaining : RemainingOutputs) (results : Index → Option (Counter × Encoding)) (x : HashInput)
    (h : IsMsgInput x) : (targetingA parameterOutput fixed highs remaining results).kind x = .none := by
  show (if SecondOrderInput (truncateHash parameterOutput) results x then .none
    else sampleKind parameterOutput fixed highs remaining results x) = .none
  split_ifs
  · rfl
  · exact sampleTargeting_msg parameterOutput fixed highs remaining results x h

omit [Params] in
theorem numeric_monoF {ρ x x' : ℝ} (h : Numeric ρ x) (hx : x' ≤ x) (_hx0 : 0 ≤ x') : Numeric ρ x' where
  low := h.low
  high := h.high
  enc := by
    have h1 := h.enc
    have h2 : 0 ≤ 2 - ρ := by linarith [h.high]
    have h3 : (2 - ρ) * x' ≤ (2 - ρ) * x := mul_le_mul_of_nonneg_left hx h2
    nlinarith
  contact := by have := h.contact; linarith
  small := by have := h.small; linarith

omit [Params] in
theorem probEvent_le_endValueF (payoff : (Coordinate → Digest) → State → ℝ≥0∞) (s : State)
    (E : (Coordinate → Digest) → Prop) (h : ∀ T, E T → payoff T s = 1) :
    Pr[E | completion s.known] ≤ endValue payoff s := by
  rw [probEvent_eq_tsum_ite]
  unfold endValue
  refine ENNReal.tsum_le_tsum fun T => ?_
  split_ifs with hT
  · rw [h T hT, mul_one]
  · exact bot_le

omit [Params] in
theorem digestCount_cons_inrF {D R ι : Type} (tg : Targeting D R ι) (amount : ℕ) (entries : List (Entry D)) :
    digestCount tg (.inr amount :: entries) = digestCount tg entries := by
  simp [digestCount]

/-- The reveal rate in real form. -/
theorem revRate_eq : revRate = ENNReal.ofReal (123 * ((2 : ℝ) ^ subtreeHeight * 2 ^ 15)⁻¹) := by
  unfold revRate
  rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat, ← ENNReal.ofReal_natCast,
    ENNReal.ofReal_inv_of_pos (by positivity)]
  push_cast
  norm_num

/-- One contact split between the A4 payment `(1 - κ) 2^-128` and `κ 2^-128`. -/
theorem arm_splitF (κ : ℝ) : ν ≤ ν * ENNReal.ofReal (1 - κ) + ENNReal.ofReal κ * ν :=
  calc ν = ν * ENNReal.ofReal ((1 - κ) + κ) := by rw [sub_add_cancel, ENNReal.ofReal_one, mul_one]
    _ ≤ ν * (ENNReal.ofReal (1 - κ) + ENNReal.ofReal κ) := mul_le_mul_right ENNReal.ofReal_add_le _
    _ = _ := by ring

/-- **The A4 payments per forest step query fit in the slack of the linear potential.** -/
theorem arm_paysF (ρ x κ : ℝ) (hκ1 : κ ≤ 1)
    (hκ : 2 - ρ + x + (signatureLimit : ℝ) * (123 * ((2 : ℝ) ^ subtreeHeight * 2 ^ 15)⁻¹) ≤ κ) :
    ν * ((signatureLimit : ℝ≥0∞) * revRate) + ν * ENNReal.ofReal (1 - κ) ≤
      ENNReal.ofReal ((ρ - 1 - x) / 2 ^ 128) := by
  have hm : (0 : ℝ) ≤ (signatureLimit : ℝ) * (123 * ((2 : ℝ) ^ subtreeHeight * 2 ^ 15)⁻¹) := by positivity
  have hν : (0 : ℝ) ≤ ((2 : ℝ) ^ 128)⁻¹ := by positivity
  have h1 : (0 : ℝ) ≤ 1 - κ := by linarith
  rw [ν_eq_ofReal, revRate_eq, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _),
    ← ENNReal.ofReal_mul hν, ← ENNReal.ofReal_mul hν, ← ENNReal.ofReal_add (mul_nonneg hν hm) (mul_nonneg hν h1)]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [div_eq_inv_mul, ← mul_add]
  exact mul_le_mul_of_nonneg_left (by linarith) hν

/-- The near forecast at the start grows with the number of future pairs. -/
theorem startNearF_mono {wbar : ℝ≥0∞} (hw : wbar ≤ 1) {j k : ℕ} (hjk : j ≤ k) :
    startNearF wbar j ≤ startNearF wbar k := by
  unfold startNearF
  exact creations_mono_count Finset.univ_nonempty landing_le_one
    (fun v I => virtualOnce_le_consM hw (excessW_props witnessNear_props ENNReal.zero_ne_top).1 signatureLimit I v 0)
    (fun _ _ h => virtualOnce_perm signatureLimit h 0) hjk []

/-- **The start sum.** With `startNear y ≤ 2h`, the near potentials at the levels below `y` sum
to at most `y (y (h + φ) + N φ)`. -/
theorem start_sum_leF {wbar : ℝ≥0∞} (hw : wbar ≤ 1) (y : ℕ) (φ h : ℝ≥0∞) (hh : startNearF wbar y ≤ 2 * h) :
    ∑ j ∈ Finset.range y, ((j : ℝ≥0∞) * (startNearF wbar j + φ) + signatureLimit * φ) ≤
      y * (y * (h + φ) + signatureLimit * φ) := by
  set T : ℝ≥0∞ := ∑ j ∈ Finset.range y, (j : ℝ≥0∞) with hTdef
  have hT : T * 2 ≤ (y : ℝ≥0∞) * y := by
    have h1 : (∑ j ∈ Finset.range y, j) * 2 ≤ y * y := by
      rw [Finset.sum_range_id_mul_two]
      exact Nat.mul_le_mul_left _ (Nat.sub_le y 1)
    have h2 : (((∑ j ∈ Finset.range y, j) * 2 : ℕ) : ℝ≥0∞) ≤ ((y * y : ℕ) : ℝ≥0∞) := Nat.cast_le.2 h1
    simpa only [hTdef, Nat.cast_mul, Nat.cast_sum, Nat.cast_ofNat] using h2
  calc ∑ j ∈ Finset.range y, ((j : ℝ≥0∞) * (startNearF wbar j + φ) + signatureLimit * φ)
      ≤ ∑ j ∈ Finset.range y, ((j : ℝ≥0∞) * (2 * h + φ) + signatureLimit * φ) := by
        refine Finset.sum_le_sum fun j hj => ?_
        gcongr
        exact le_trans (startNearF_mono hw (Finset.mem_range.1 hj).le) hh
    _ = T * 2 * h + T * φ + y * (signatureLimit * φ) := by
        rw [Finset.sum_add_distrib, ← Finset.sum_mul, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        ring
    _ ≤ y * y * h + y * y * φ + y * (signatureLimit * φ) := by
        gcongr
        exact le_trans (le_mul_of_one_le_right' one_le_two) hT
    _ = _ := by ring

/-- The creation rate of the scan signer in real form: `(2 − 1/M) / 2^128`, `M = scanM`. -/
theorem rateS_eqF : rateS = ENNReal.ofReal ((2 - 1 / (H0.scanM : ℝ)) / 2 ^ 128) := by
  have hM : (1 : ℝ) ≤ (H0.scanM : ℝ) := by exact_mod_cast H0.scanM_pos
  have h1M : (0 : ℝ) ≤ 1 - 1 / (H0.scanM : ℝ) := by
    rw [sub_nonneg, div_le_one (by linarith)]; exact hM
  have hc : (Fintype.card Randomness : ℝ≥0∞)⁻¹ = ENNReal.ofReal (1 / 2 ^ 128) := by
    rw [GraphView.card_randomness, one_div, ENNReal.ofReal_inv_of_pos (by positivity)]
    congr 1
    rw [← ENNReal.ofReal_natCast]
    congr 1
    norm_num
  have hl1 : (1 : ℝ≥0∞) - landing = ENNReal.ofReal (1 - 1 / (H0.scanM : ℝ)) := by
    rw [H0.landing_eq_M, ENNReal.ofReal_sub _ (by positivity), ENNReal.ofReal_one]
  unfold rateS
  rw [hc, hl1, ← ENNReal.ofReal_one, ← ENNReal.ofReal_add h1M (by norm_num),
    ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  ring

end Helpers

end Sphincs.Security.ForsPotential
