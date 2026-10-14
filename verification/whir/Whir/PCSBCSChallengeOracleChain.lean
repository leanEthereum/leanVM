import Whir.PCSBCSChallengeOracle

/-! A separate 192-bit challenge-chain birthday calculation. It is not a
source-history collision estimate and is not charged by the 256-bit duplex
coupling theorem. It applies only when an actual compiler uses E-valued chaining
answers. Every adaptive request and repeated query is retained. -/
set_option autoImplicit false
namespace Whir.PCSBCSChallengeOracle
open Concrete FiatShamirGame TypedOracleCompiler
open scoped BigOperators

private theorem uniform_targets (seen : Finset E) :
    average (fun a : E => if a ∈ seen then (1:ℚ) else 0) = seen.card / (2^192 : ℚ) := by
  classical
  simp [average, FieldModel.card_E]
  norm_num

/-- Lazy chain collision monitor. Cache hits return the old answer; only a
fresh query can collide with an earlier distinct-input output. -/
noncomputable def chainRisk {K R : Type*} [DecidableEq K] {n : Nat} :
    Sampling K (fun _ => E) R n → (K → Option E) → Finset E → ℚ
  | .ret _, _, _ => 0
  | .draw key next, cache, seen =>
      match cache key with
      | some a => chainRisk (next a) cache seen
      | none => average (fun a : E => if a ∈ seen then 1
          else chainRisk (next a) (TypedFiatShamirGame.put cache key a) (insert a seen))

def chainLedger (remaining previous : Nat) : ℚ :=
  ((remaining : ℚ)*previous + remaining*(remaining-1)/2) / 2^192

private theorem chainLedger_nonneg (remaining previous : Nat) :
    0 ≤ chainLedger remaining previous := by
  cases remaining with
  | zero => simp [chainLedger]
  | succ n => unfold chainLedger; simp only [Nat.cast_add, Nat.cast_one, add_sub_cancel_right]; positivity

private theorem chainLedger_step (remaining previous : Nat) :
    chainLedger (remaining+1) previous =
      (previous : ℚ)/2^192 + chainLedger remaining (previous+1) := by
  unfold chainLedger
  push_cast
  ring

theorem chainRisk_bound {K R : Type*} [DecidableEq K] {n : Nat}
    (p : Sampling K (fun _ => E) R n) (cache : K → Option E) (seen : Finset E) :
    chainRisk p cache seen ≤ chainLedger n seen.card := by
  classical
  induction p generalizing cache seen with
  | ret value => exact chainLedger_nonneg _ _
  | @draw n key next ih =>
    cases hit : cache key with
    | some a =>
      simp only [chainRisk, hit]
      have step := chainLedger_step n seen.card
      have bound := ih a cache seen
      have mono : chainLedger n seen.card ≤ chainLedger n (seen.card+1) := by
        unfold chainLedger; push_cast; have hn : (0:ℚ) ≤ n := by positivity
        have hd : (0:ℚ) < 2^192 := by positivity
        apply (div_le_div_iff_of_pos_right hd).mpr
        nlinarith
      have positive : (0:ℚ) ≤ (seen.card:ℚ)/2^192 := by positivity
      rw [step]
      linarith
    | none =>
      simp only [chainRisk, hit]
      calc
        _ ≤ average (fun a : E => (if a ∈ seen then (1:ℚ) else 0) +
            chainLedger n (seen.card+1)) := by
          apply average_mono
          intro a
          by_cases bad : a ∈ seen
          · simp only [bad, ↓reduceIte]
            have nonneg := chainLedger_nonneg n (seen.card+1)
            linarith
          · have bound := ih a (TypedFiatShamirGame.put cache key a) (insert a seen)
            simpa only [bad, ↓reduceIte, zero_add, Finset.card_insert_of_notMem bad] using bound
        _ = (seen.card:ℚ)/2^192 + chainLedger n (seen.card+1) := by
          rw [average_add, uniform_targets, average_const]
        _ = _ := (chainLedger_step n seen.card).symm

/-- An actual Boolean event, not an assumed loss bound. -/
noncomputable def chainAlarm {K R : Type*} [DecidableEq K] {n : Nat} :
    (K → E) → Sampling K (fun _ => E) R n → (K → Option E) → Finset E → Bool
  | _, .ret _, _, _ => false
  | table, .draw key next, cache, seen =>
      match cache key with
      | some a => chainAlarm table (next a) cache seen
      | none => if table key ∈ seen then true else
          chainAlarm table (next (table key))
            (TypedFiatShamirGame.put cache key (table key)) (insert (table key) seen)

theorem chainAlarm_table_eq_risk {K R : Type*} [Fintype K] [DecidableEq K] {n : Nat}
    (p : Sampling K (fun _ => E) R n) (cache : K → Option E) (seen : Finset E) :
    average (fun table : K → E =>
      if chainAlarm (RawOracleCoupling.overlay cache table) p cache seen then (1:ℚ) else 0) =
      chainRisk p cache seen := by
  induction p generalizing cache seen with
  | ret value => simp [chainAlarm, chainRisk, average_const]
  | draw key next ih =>
    cases hit : cache key with
    | some a => simp [chainAlarm, chainRisk, hit, ih]
    | none =>
      rw [RawOracleCoupling.overlay_average cache key hit
        (fun table => if chainAlarm table (.draw key next) cache seen then (1:ℚ) else 0)]
      simp only [chainRisk, hit]
      apply congrArg average
      funext a
      by_cases bad : a ∈ seen
      · simp [chainAlarm, RawOracleCoupling.overlay, hit, bad, average_const]
      · rw [← ih a (TypedFiatShamirGame.put cache key a) (insert a seen)]
        simp only [bad, ↓reduceIte]
        apply congrArg average
        funext table
        simp [chainAlarm, RawOracleCoupling.overlay, TypedFiatShamirGame.put_self, hit, bad]

/-- Derived 192-bit term, deliberately separate from duplexModeLoss. The
sharper Q(Q-1)/2 term is proved en route; Q² is a conservative exact expression. -/
theorem actual_chain_collision_bound {K R : Type*} [Fintype K] [DecidableEq K] {Q : Nat}
    (p : Sampling K (fun _ => E) R Q) :
    average (fun table : K → E => if chainAlarm table p (fun _ => none) ∅ then (1:ℚ) else 0) ≤
      (Q:ℚ)^2 / 2^192 := by
  have exactRisk := chainAlarm_table_eq_risk p (fun _ => none) ∅
  simp only [RawOracleCoupling.overlay_empty] at exactRisk
  have bound := chainRisk_bound p (fun _ => none) ∅
  simp only [Finset.card_empty] at bound
  calc
    _ = chainRisk p (fun _ => none) ∅ := exactRisk
    _ ≤ chainLedger Q 0 := bound
    _ ≤ (Q:ℚ)^2/2^192 := by
      unfold chainLedger
      simp only [Nat.cast_zero, mul_zero, zero_add]
      apply (div_le_div_iff_of_pos_right (by positivity : (0:ℚ) < 2^192)).mpr
      have nonneg : (0:ℚ) ≤ Q := by positivity
      nlinarith

#print axioms chainAlarm_table_eq_risk
#print axioms actual_chain_collision_bound
end Whir.PCSBCSChallengeOracle
