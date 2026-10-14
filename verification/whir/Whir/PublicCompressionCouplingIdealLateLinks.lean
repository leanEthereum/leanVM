import Whir.PublicCompressionCouplingHidden

/-! Late links in actual uniform mixed seed/RO tables. Targets are exactly
chaining values of earlier inl compression inputs. Cached draws still publish
their input CV; inr RO draws publish no compression CV. A fresh output is
checked before publishing its own input, giving the actual birthday ledger. -/
namespace Whir.PublicCompressionCouplingIdealLateLinks
open FiatShamirGame DuplexRefinement DuplexFraming DuplexModeGame TypedOracleCompiler
open TypedFiatShamirGame RawOracleCoupling
open PublicCompressionCoupling (collisionLedger)

variable {K R : Type} [DecidableEq K]
abbrev Computation (K R : Type) (n : Nat) := Sampling K (fun _ => Digest32) R n

def advance (inputCV : K → Option Digest32) (key : K) (history : List Digest32) :
    List Digest32 := match inputCV key with
  | none => history
  | some cv => cv :: history

omit [DecidableEq K] in
 theorem advance_length (inputCV : K → Option Digest32) (key : K) (history : List Digest32) :
    (advance inputCV key history).length ≤ history.length+1 := by
  cases hit : inputCV key <;> simp [advance,hit]

noncomputable def alarm (inputCV : K → Option Digest32) (table : K → Digest32) {n : Nat} :
    Computation K R n → (K → Option Digest32) → List Digest32 → Bool
  | .ret _, _, _ => false
  | .draw key next, cache, history => match cache key with
    | some answer => alarm inputCV table (next answer) cache (advance inputCV key history)
    | none => decide (table key ∈ history.toFinset) ||
      alarm inputCV table (next (table key)) (put cache key (table key))
        (advance inputCV key history)

noncomputable def risk (inputCV : K → Option Digest32) {n : Nat} :
    Computation K R n → (K → Option Digest32) → List Digest32 → ℚ
  | .ret _, _, _ => 0
  | .draw key next, cache, history => match cache key with
    | some answer => risk inputCV (next answer) cache (advance inputCV key history)
    | none => average (fun answer : Digest32 => if answer ∈ history.toFinset then 1 else
      risk inputCV (next answer) (put cache key answer) (advance inputCV key history))

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

 theorem risk_bound (inputCV : K → Option Digest32) {n : Nat}
    (p : Computation K R n) (cache : K → Option Digest32) (history : List Digest32) :
    risk inputCV p cache history ≤ collisionLedger n history.length := by
  classical
  induction p generalizing cache history with
  | ret r => exact ledger_nonneg _ _
  | @draw n key next ih =>
    have hs := ledger_step n history.length
    cases hit : cache key with
    | some answer =>
      simp only [risk,hit]
      have ht := le_trans (ih answer cache (advance inputCV key history))
        (ledger_mono_previous n (advance_length inputCV key history))
      rw [hs]
      have hn : (0:ℚ) ≤ (history.length:ℚ)/2^256 := by positivity
      linarith
    | none =>
      simp only [risk,hit]
      calc
        _ ≤ average (fun answer : Digest32 =>
          (if answer ∈ history.toFinset then (1:ℚ) else 0) +
            collisionLedger n (history.length+1)) := by
          apply average_mono
          intro answer
          have ht := le_trans (ih answer (put cache key answer) (advance inputCV key history))
            (ledger_mono_previous n (advance_length inputCV key history))
          have hn := ledger_nonneg n (history.length+1)
          by_cases bad : answer ∈ history.toFinset
          · simp only [bad,↓reduceIte]; linarith
          · simpa only [bad,↓reduceIte,zero_add] using ht
        _ = (history.toFinset.card:ℚ)/2^256 + collisionLedger n (history.length+1) := by
          rw [average_add,PublicMerkleProbability.uniform_target_probability,average_const]
        _ ≤ (history.length:ℚ)/2^256 + collisionLedger n (history.length+1) := by
          apply add_le_add_left
          apply div_le_div_of_nonneg_right _ (by positivity)
          exact_mod_cast List.toFinset_card_le history
        _ = _ := hs.symm

variable [Fintype K]

/-- Exact disintegration of the actual table; adaptive keys and cached requests
are processed by the existing memo semantics, not a supplied alarm bound. -/
theorem table_alarm_eq_risk (inputCV : K → Option Digest32) {n : Nat}
    (p : Computation K R n) (cache : K → Option Digest32) (history : List Digest32) :
    average (fun table : K → Digest32 =>
      if alarm inputCV (overlay cache table) p cache history then (1:ℚ) else 0) =
      risk inputCV p cache history := by
  classical
  induction p generalizing cache history with
  | ret r => simp [alarm,risk,average_const]
  | draw key next ih =>
    cases hit : cache key with
    | some answer =>
      simp only [alarm,risk,hit]
      exact ih answer cache (advance inputCV key history)
    | none =>
      rw [overlay_average cache key hit
        (fun table => if alarm inputCV table (.draw key next) cache history then (1:ℚ) else 0)]
      simp only [risk,hit]
      apply congrArg average
      funext answer
      by_cases bad : answer ∈ history.toFinset
      · simp [alarm,hit,overlay,bad,average_const]
      · rw [← ih answer (put cache key answer) (advance inputCV key history)]
        simp only [bad,↓reduceIte]
        apply congrArg average
        funext table
        simp [alarm,hit,overlay,bad]

set_option backward.isDefEq.respectTransparency false in
 theorem actual_table_bound (inputCV : K → Option Digest32) {n : Nat}
    (p : Computation K R n) :
    average (fun table : K → Digest32 =>
      if alarm inputCV table p (fun _ => none) [] then (1:ℚ) else 0) ≤ compressionBirthdayLoss n := by
  unfold compressionBirthdayLoss
  apply le_min
  · calc
      _ ≤ average (fun _ : K → Digest32 => (1:ℚ)) := by
        apply average_mono
        intro table
        split <;> norm_num
      _ = 1 := average_const _
  · have h := risk_bound inputCV p (fun _ => none) []
    rw [← table_alarm_eq_risk] at h
    simpa only [overlay_empty,List.length_nil,PublicCompressionCoupling.collisionLedger_zero] using h

def mixedCV {Q : Nat} : PublicCompressionCouplingMixed.Key Q → Option Digest32
  | .inl input => some input.cv
  | .inr _ => none

open Classical in
/-- The literal mixed-table public phase uses the PINNED simulator's lookup,
recognition and fallback, retaining all chosen public CVs and the full View. -/
theorem actual_pinned_mixed_probability {R : Type} (Q : Nat) (iv : Digest32)
    (p : Program R) (counted : Counts Q p) :
    letI := PublicCompressionCouplingMixed.mixedKeyFintype Q
    average (fun table : PublicCompressionCouplingMixed.Key Q → Digest32 =>
      if alarm mixedCV table (PublicCompressionCouplingMixed.compile Q iv [] p Q (by rfl) counted)
        (fun _ => none) [] then (1:ℚ) else 0) ≤ compressionBirthdayLoss Q := by
  let _ := PublicCompressionCouplingMixed.mixedKeyFintype Q
  exact actual_table_bound mixedCV _

open Classical in
/-- Exact uniform finite-product marginal, in the real ideal experiment's
RO-first coin order. The tables are not replaced by a stand-in simulator. -/
theorem table_average_eq_ideal {Q : Nat}
    [Fintype (PublicCompressionCouplingMixed.Key Q)] [Fintype DuplexPublicSimulator.Seed]
    [Fintype (RawKey Q → Digest32)]
    (payoff : (PublicCompressionCouplingMixed.Key Q → Digest32) → ℚ) :
    average payoff = average (fun coins : (RawKey Q → Digest32) × DuplexPublicSimulator.Seed =>
      payoff (PublicCompressionCouplingMixed.oracle coins.2 coins.1)) := by
  let e := (PublicCompressionCouplingMixed.tableEquiv Q).trans
    (Equiv.prodComm DuplexPublicSimulator.Seed (RawKey Q → Digest32))
  have h := average_equiv e (fun coins => payoff (e.symm coins))
  have inverse (coins : (RawKey Q → Digest32) × DuplexPublicSimulator.Seed) :
      e.symm coins = PublicCompressionCouplingMixed.oracle coins.2 coins.1 := rfl
  simp only [Equiv.symm_apply_apply] at h
  simpa only [inverse] using h

open Classical in
/-- Actual uniformly sampled RO and pinned fallback seed, with no assumed bad
probability premise. Every counted adaptive Program continuation is covered. -/
theorem actual_ideal_lateLink_probability {R : Type} (Q : Nat) (iv : Digest32)
    (p : Program R) (counted : Counts Q p) :
    letI := DuplexPublicSimulator.seedFintype
    letI := rawOracleFintype Q
    average (fun coins : (RawKey Q → Digest32) × DuplexPublicSimulator.Seed =>
      if alarm mixedCV (PublicCompressionCouplingMixed.oracle coins.2 coins.1)
        (PublicCompressionCouplingMixed.compile Q iv [] p Q (by rfl) counted)
        (fun _ => none) [] then (1:ℚ) else 0) ≤ compressionBirthdayLoss Q := by
  let _ := DuplexPublicSimulator.seedFintype
  let _ := rawOracleFintype Q
  let _ := PublicCompressionCouplingMixed.mixedKeyFintype Q
  have h := actual_pinned_mixed_probability Q iv p counted
  rw [table_average_eq_ideal] at h
  exact h

#print axioms table_alarm_eq_risk
#print axioms actual_table_bound
#print axioms table_average_eq_ideal
#print axioms actual_ideal_lateLink_probability
end Whir.PublicCompressionCouplingIdealLateLinks
