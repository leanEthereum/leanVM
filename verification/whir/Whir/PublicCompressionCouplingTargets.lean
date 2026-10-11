import Whir.PublicCompressionCouplingResidual

/-! Fresh-target probabilities for literal uniform finite tables and their
actual adaptive memo caches. In particular, these bounds apply to private
prefix inspection conditional on the entire public view. -/
namespace Whir.PublicCompressionCouplingTargets
open FiatShamirGame TypedOracleCompiler TypedFiatShamirGame RawOracleCoupling

variable {K R : Type} [DecidableEq K]
abbrev Computation (K R : Type) (n : Nat) := Sampling K (fun _ => Digest32) R n

noncomputable def alarm (table : K → Digest32) (targets : Finset Digest32) {n : Nat} :
    Computation K R n → (K → Option Digest32) → Bool
  | .ret _, _ => false
  | .draw key next, cache =>
    match cache key with
    | some answer => alarm table targets (next answer) cache
    | none => decide (table key ∈ targets) ||
      alarm table targets (next (table key)) (put cache key (table key))

noncomputable def risk (targets : Finset Digest32) {n : Nat} :
    Computation K R n → (K → Option Digest32) → ℚ
  | .ret _, _ => 0
  | .draw key next, cache =>
    match cache key with
    | some answer => risk targets (next answer) cache
    | none => average (fun answer : Digest32 => if answer ∈ targets then 1 else
      risk targets (next answer) (put cache key answer))

theorem risk_bound (targets : Finset Digest32) {n : Nat}
    (p : Computation K R n) (cache : K → Option Digest32) :
    risk targets p cache ≤ (n : ℚ)*targets.card/2^256 := by
  induction p generalizing cache with
  | ret r => simp only [risk]; positivity
  | @draw n key next ih =>
    cases hit : cache key with
    | some answer =>
      simp only [risk,hit]
      have h := ih answer cache
      have hn : (0 : ℚ) ≤ (targets.card : ℚ)/2^256 := by positivity
      push_cast
      linarith
    | none =>
      simp only [risk,hit]
      calc
        _ ≤ average (fun answer : Digest32 =>
          (if answer ∈ targets then (1:ℚ) else 0) + (n:ℚ)*targets.card/2^256) := by
          apply average_mono
          intro answer
          have ht := ih answer (put cache key answer)
          by_cases bad : answer ∈ targets
          · simp only [bad,↓reduceIte]
            have hn : (0:ℚ) ≤ (n:ℚ)*targets.card/2^256 := by positivity
            linarith
          · simpa only [bad,↓reduceIte,zero_add] using ht
        _ = (targets.card : ℚ)/2^256 + (n:ℚ)*targets.card/2^256 := by
          rw [average_add,PublicMerkleProbability.uniform_target_probability,average_const]
        _ = _ := by push_cast; ring

variable [Fintype K]

theorem table_alarm_eq_risk (targets : Finset Digest32) {n : Nat}
    (p : Computation K R n) (cache : K → Option Digest32) :
    average (fun table : K → Digest32 =>
      if alarm (overlay cache table) targets p cache then (1:ℚ) else 0) =
      risk targets p cache := by
  classical
  induction p generalizing cache with
  | ret r => simp [alarm,risk,average_const]
  | draw key next ih =>
    cases hit : cache key with
    | some answer => simp only [alarm,risk,hit]; exact ih answer cache
    | none =>
      rw [overlay_average cache key hit
        (fun table => if alarm table targets (.draw key next) cache then (1:ℚ) else 0)]
      simp only [risk,hit]
      apply congrArg average
      funext answer
      by_cases bad : answer ∈ targets
      · simp [alarm,hit,overlay,bad,average_const]
      · rw [← ih answer (put cache key answer)]
        simp only [bad,↓reduceIte]
        apply congrArg average
        funext table
        simp [alarm,hit,overlay,bad]

omit [DecidableEq K] [Fintype K] in
 theorem expectation_le_const {T : Type} {n : Nat}
    (p : Sampling K (fun _ => Digest32) T n) (payoff : T → ℚ) (bound : ℚ)
    (h : ∀ result, payoff result ≤ bound) : Sampling.expectation payoff p ≤ bound := by
  induction p with
  | ret r => exact h r
  | draw key next ih =>
    exact le_trans (average_mono (fun answer => ih answer)) (le_of_eq (average_const bound))

/-- Targets may depend on all public outputs, chosen inputs and the result.
Only the size cap is used, and inspection can branch on every private reply. -/
theorem adaptive_posthoc_bound {T : Type} {publicCap privateCap targetCap : Nat}
    (publicCalls : Computation K R publicCap)
    (privateCalls : R → Computation K T privateCap) (targets : R → Finset Digest32)
    (size : ∀ result, (targets result).card ≤ targetCap) :
    average (fun table : K → Digest32 =>
      let result := Sampling.eval table (memo publicCalls (fun _ => none))
      if alarm table (targets result.1) (privateCalls result.1) result.2 then (1:ℚ) else 0) ≤
      (privateCap:ℚ)*targetCap/2^256 := by
  have residual := PublicCompressionCouplingResidual.memo_residual publicCalls (fun _ => none)
    (fun result table => if alarm table (targets result.1) (privateCalls result.1)
      result.2 then (1:ℚ) else 0)
  simp only [overlay_empty] at residual
  dsimp only at residual ⊢
  apply le_trans residual.le
  apply expectation_le_const
  intro result
  rw [table_alarm_eq_risk]
  apply le_trans (risk_bound _ _ _)
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact mul_le_mul_of_nonneg_left (by exact_mod_cast size result.1) (by positivity)

#print axioms table_alarm_eq_risk
#print axioms adaptive_posthoc_bound
end Whir.PublicCompressionCouplingTargets
