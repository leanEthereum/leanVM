import Sphincs.BridgeLinear

/-! A linear potential on the interpreted comparison with two payments: a fixed amount per
message-digest query, and a fixed amount per query whose input lies in a second class (later, the
FORS leaf inputs, counted whether fresh or cached). If every step keeps the potential in
expectation while making both payments, the potential at the start bounds the expected final
payoff plus all payments of the run. Interpreted runs have total mass one. -/

open OracleComp OracleSpec ENNReal

namespace Sphincs.Security.HiddenDebt

open HiddenCost HiddenBridge HiddenOutside HiddenReveal

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false
attribute [local instance] Classical.propDecidable

variable {D R A ι : Type} [Fintype ι] [SampleableType R]
variable (tg : Targeting D R ι) (initial : Cache D R) (model : HiddenRows.Model D R A ι)

/-- Number of queries of a trace whose input satisfies `IsFleaf`. -/
noncomputable def fleafCount (IsFleaf : D → Prop) (entries : List (Entry D)) : ℕ :=
  (entries.filter fun entry => match entry with
    | .inl input => decide (IsFleaf input)
    | .inr _ => false).length

theorem fleafCount_append (IsFleaf : D → Prop) (first second : List (Entry D)) :
    fleafCount IsFleaf (first ++ second) = fleafCount IsFleaf first + fleafCount IsFleaf second := by
  simp [fleafCount, List.filter_append]

@[simp]
theorem fleafCount_nil (IsFleaf : D → Prop) : fleafCount IsFleaf ([] : List (Entry D)) = 0 := rfl

@[simp]
theorem fleafCount_cons_inr (IsFleaf : D → Prop) (amount : ℕ) (entries : List (Entry D)) :
    fleafCount IsFleaf (.inr amount :: entries) = fleafCount IsFleaf entries := by
  simp [fleafCount]

theorem fleafCount_cons_inl (IsFleaf : D → Prop) (input : D) (entries : List (Entry D)) :
    (fleafCount IsFleaf (.inl input :: entries) : ℝ≥0∞) =
      (if IsFleaf input then 1 else 0) + fleafCount IsFleaf entries := by
  by_cases h : IsFleaf input
  · simp [fleafCount, h, add_comm]
  · simp [fleafCount, h]

theorem fleafCount_recorded_inl (IsFleaf : D → Prop) (input : D) :
    (fleafCount IsFleaf (recorded (D := D) (R := R) (ι := ι) (.inl (.inr (.inl input)))) : ℝ≥0∞) =
      if IsFleaf input then 1 else 0 := by
  change (fleafCount IsFleaf [.inl input] : ℝ≥0∞) = _
  have h := fleafCount_cons_inl IsFleaf input []
  simpa using h

/-- Steps other than ordinary queries record no input of the class. -/
theorem fleafCount_recorded_eq_zero (IsFleaf : D → Prop) (input : (SourceCostSpec D R ι).Domain)
    (h : ∀ bytes, input = .inl (.inr (.inl bytes)) → ¬IsFleaf bytes) :
    fleafCount IsFleaf (recorded input) = 0 := by
  rcases input with (draw | (bytes | coordinate)) | amount
  · rfl
  · have hb := h bytes rfl
    simp [fleafCount, recorded, hb]
  · rfl
  · simp [fleafCount, recorded]

/-- Interpreted runs lose no mass. -/
theorem interp_mass {α : Type} (computation : OracleComp (SourceCostSpec D R ι) α) (budget : ℕ)
    (state : DebtState D R ι) :
    ∑' out, Pr[= out | interp tg initial model computation budget state] = 1 := by
  simp

/-- **Linear potential with two payments on the interpreter.** -/
theorem interp_potential2 {α : Type} (IsFleaf : D → Prop) (Inv : DebtState D R ι → Prop)
    (Φ : ℕ → DebtState D R ι → ℝ≥0∞) (payoff : (ι → Digest) → DebtState D R ι → ℝ≥0∞) (pay pay2 : ℝ≥0∞)
    (hfinal : ∀ budget state, Inv state → endValue payoff state ≤ Φ budget state)
    (hstep : ∀ (input : (SourceCostSpec D R ι).Domain) budget state, Inv state → sourceCost input ≤ budget →
      ∑' result, Pr[= result | costStep model input state] * Φ (budget - sourceCost input) result.2 +
        pay * digestCount tg (recorded input) + pay2 * fleafCount IsFleaf (recorded input) ≤ Φ budget state)
    (hinv : ∀ input state, Inv state → ∀ result ∈ support (costStep model input state), Inv result.2)
    (computation : OracleComp (SourceCostSpec D R ι) α) :
    ∀ budget state, Inv state →
      ∑' out, Pr[= out | interp tg initial model computation budget state] *
        (endValue payoff out.2 + pay * digestCount tg out.1.2.2.1 + pay2 * fleafCount IsFleaf out.1.2.2.1) ≤
          Φ budget state := by
  induction computation using OracleComp.inductionOn with
  | pure value =>
      intro budget state hstate
      rw [interp_pure, tsum_probOutput_pure_mul]
      simpa [digestCount, fleafCount] using hfinal budget state hstate
  | query_bind input next ih =>
      intro budget state hstate
      rw [interp_query_bind]
      split_ifs with hcost
      · rw [tsum_probOutput_bind_mul]
        set c : ℝ≥0∞ := pay * digestCount tg (recorded input) + pay2 * fleafCount IsFleaf (recorded input)
          with hc
        calc ∑' result, Pr[= result | costStep model input state] *
              ∑' out, Pr[= out | (fun out => ((out.1.1, revealed input ++ out.1.2.1,
                  recorded input ++ out.1.2.2.1, touch tg initial state input ++ out.1.2.2.2), out.2)) <$>
                interp tg initial model (next result.1) (budget - sourceCost input) result.2] *
                (endValue payoff out.2 + pay * digestCount tg out.1.2.2.1 + pay2 * fleafCount IsFleaf out.1.2.2.1)
            ≤ ∑' result, Pr[= result | costStep model input state] *
                (Φ (budget - sourceCost input) result.2 + c) := by
              refine ENNReal.tsum_le_tsum fun result => ?_
              by_cases hr : result ∈ support (costStep model input state)
              · refine mul_le_mul_right ?_ _
                rw [tsum_probOutput_map_mul]
                simp only [digestCount_append, fleafCount_append, Nat.cast_add]
                calc ∑' out, Pr[= out | interp tg initial model (next result.1) (budget - sourceCost input)
                        result.2] *
                      (endValue payoff out.2 + pay * ((digestCount tg (recorded input) : ℝ≥0∞) +
                        digestCount tg out.1.2.2.1) + pay2 * ((fleafCount IsFleaf (recorded input) : ℝ≥0∞) +
                        fleafCount IsFleaf out.1.2.2.1))
                    = ∑' out, Pr[= out | interp tg initial model (next result.1) (budget - sourceCost input)
                          result.2] *
                        (endValue payoff out.2 + pay * digestCount tg out.1.2.2.1 +
                          pay2 * fleafCount IsFleaf out.1.2.2.1) +
                      (∑' out, Pr[= out | interp tg initial model (next result.1)
                        (budget - sourceCost input) result.2]) * c := by
                      rw [← ENNReal.tsum_mul_right, ← ENNReal.tsum_add]
                      refine tsum_congr fun out => ?_
                      rw [hc]
                      ring
                  _ ≤ Φ (budget - sourceCost input) result.2 + 1 * c :=
                      add_le_add (ih result.1 _ _ (hinv input state hstate result hr))
                        (mul_le_mul' tsum_probOutput_le_one le_rfl)
                  _ = _ := by rw [one_mul]
              · rw [probOutput_eq_zero_of_not_mem_support hr, zero_mul, zero_mul]
          _ = ∑' result, Pr[= result | costStep model input state] * Φ (budget - sourceCost input) result.2 +
                (∑' result, Pr[= result | costStep model input state]) * c := by
              rw [← ENNReal.tsum_mul_right, ← ENNReal.tsum_add]
              refine tsum_congr fun result => ?_
              ring
          _ ≤ ∑' result, Pr[= result | costStep model input state] * Φ (budget - sourceCost input) result.2 +
                1 * c := add_le_add le_rfl (mul_le_mul' tsum_probOutput_le_one le_rfl)
          _ ≤ _ := by
              rw [one_mul, hc, ← add_assoc]
              exact hstep input budget state hstate hcost
      · rw [tsum_probOutput_pure_mul]
        simpa [digestCount, fleafCount] using hfinal budget state hstate

end Sphincs.Security.HiddenDebt
