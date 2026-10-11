import Whir.PublicCompressionCouplingTargets

/-! Birthday probabilities for all distinct coordinates of the actual mixed
seed/RO table, including adaptively selected private prefix coordinates. -/
namespace Whir.PublicCompressionCouplingBirthday
open FiatShamirGame TypedOracleCompiler TypedFiatShamirGame RawOracleCoupling
open PublicCompressionCoupling (collisionLedger)
variable {K R : Type} [DecidableEq K]
abbrev Computation (K R : Type) (n : Nat) := Sampling K (fun _ => Digest32) R n

noncomputable def alarm (table : K → Digest32) {n : Nat} :
    Computation K R n → (K → Option Digest32) → Finset Digest32 → Bool
  | .ret _, _, _ => false
  | .draw key next, cache, seen => match cache key with
    | some answer => alarm table (next answer) cache seen
    | none => decide (table key ∈ seen) ||
      alarm table (next (table key)) (put cache key (table key)) (insert (table key) seen)

noncomputable def risk {n : Nat} :
    Computation K R n → (K → Option Digest32) → Finset Digest32 → ℚ
  | .ret _, _, _ => 0
  | .draw key next, cache, seen => match cache key with
    | some answer => risk (next answer) cache seen
    | none => average (fun answer : Digest32 => if answer ∈ seen then 1 else
      risk (next answer) (put cache key answer) (insert answer seen))

private theorem ledger_nonneg (n k : Nat) : 0 ≤ collisionLedger n k := by
  cases n with
  | zero => simp [collisionLedger]
  | succ n =>
    unfold collisionLedger
    simp only [Nat.cast_add,Nat.cast_one,add_sub_cancel_right]
    positivity

private theorem ledger_step (n k : Nat) :
    collisionLedger (n+1) k = (k:ℚ)/2^256 + collisionLedger n (k+1) := by
  unfold collisionLedger
  push_cast
  ring

private theorem ledger_mono_previous (n : Nat) {j k : Nat} (h : j ≤ k) :
    collisionLedger n j ≤ collisionLedger n k := by
  unfold collisionLedger
  apply div_le_div_of_nonneg_right _ (by positivity)
  apply add_le_add_left
  exact mul_le_mul_of_nonneg_left (by exact_mod_cast h) (by positivity)

theorem risk_bound {n : Nat} (p : Computation K R n) (cache : K → Option Digest32)
    (seen : Finset Digest32) : risk p cache seen ≤ collisionLedger n seen.card := by
  classical
  induction p generalizing cache seen with
  | ret r => exact ledger_nonneg _ _
  | @draw n key next ih =>
    have hs := ledger_step n seen.card
    cases hit : cache key with
    | some answer =>
      simp only [risk,hit]
      have ht := le_trans (ih answer cache seen) (ledger_mono_previous n (Nat.le_succ seen.card))
      rw [hs]
      have hn : (0:ℚ) ≤ (seen.card:ℚ)/2^256 := by positivity
      linarith
    | none =>
      simp only [risk,hit]
      calc
        _ ≤ average (fun answer : Digest32 =>
          (if answer ∈ seen then (1:ℚ) else 0) + collisionLedger n (seen.card+1)) := by
          apply average_mono
          intro answer
          have ht := le_trans (ih answer (put cache key answer) (insert answer seen))
            (ledger_mono_previous n (Finset.card_insert_le _ _))
          have hn := ledger_nonneg n (seen.card+1)
          by_cases bad : answer ∈ seen
          · simp only [bad,↓reduceIte]; linarith
          · simpa only [bad,↓reduceIte,zero_add] using ht
        _ = (seen.card:ℚ)/2^256 + collisionLedger n (seen.card+1) := by
          rw [average_add,PublicMerkleProbability.uniform_target_probability,average_const]
        _ = _ := hs.symm

variable [Fintype K]

theorem table_alarm_eq_risk {n : Nat} (p : Computation K R n)
    (cache : K → Option Digest32) (seen : Finset Digest32) :
    average (fun table : K → Digest32 =>
      if alarm (overlay cache table) p cache seen then (1:ℚ) else 0) = risk p cache seen := by
  classical
  induction p generalizing cache seen with
  | ret r => simp [alarm,risk,average_const]
  | draw key next ih =>
    cases hit : cache key with
    | some answer => simp only [alarm,risk,hit]; exact ih answer cache seen
    | none =>
      rw [overlay_average cache key hit
        (fun table => if alarm table (.draw key next) cache seen then (1:ℚ) else 0)]
      simp only [risk,hit]
      apply congrArg average
      funext answer
      by_cases bad : answer ∈ seen
      · simp [alarm,hit,overlay,bad,average_const]
      · rw [← ih answer (put cache key answer) (insert answer seen)]
        simp only [bad,↓reduceIte]
        apply congrArg average
        funext table
        simp [alarm,hit,overlay,bad]

set_option backward.isDefEq.respectTransparency false in
 theorem actual_mixed_birthday_bound {n : Nat} (p : Computation K R n) :
    average (fun table : K → Digest32 =>
      if alarm table p (fun _ => none) ∅ then (1:ℚ) else 0) ≤
      min 1 ((n.choose 2:ℚ)/2^256) := by
  apply le_min
  · calc
      _ ≤ average (fun _ : K → Digest32 => (1:ℚ)) := by
        apply average_mono
        intro table
        split <;> norm_num
      _ = 1 := average_const _
  · have h := risk_bound p (fun _ => none) ∅
    rw [← table_alarm_eq_risk] at h
    simpa only [overlay_empty,Finset.card_empty,PublicCompressionCoupling.collisionLedger_zero] using h

#print axioms actual_mixed_birthday_bound
end Whir.PublicCompressionCouplingBirthday
