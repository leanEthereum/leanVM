import Whir.PublicCompressionCouplingCausal
import Whir.PublicCompressionCouplingBirthday
import Whir.PublicCompressionCouplingHidden
import Whir.PublicCompressionCouplingIdealLateLinks

/-! The exact Q-dependent causal event ledger used by cache alignment. The
event-to-full-View implication is proved in `PublicCompressionCouplingSourceStream`
and its distinguishing consequence in `PublicCompressionCouplingActualCausalBound`. -/
namespace Whir.PublicCompressionCouplingMixed
open FiatShamirGame DuplexRefinement DuplexFraming DuplexModeGame TypedOracleCompiler

open Classical in
noncomputable def causalBad {R : Type} (Q : Nat) (iv : Digest32) (p : Program R)
    (counted : Counts Q p) (table : Key Q → Digest32) : Bool :=
  PublicCompressionCouplingBirthday.alarm table (causalCompile Q iv [] p Q (by rfl) counted)
    (fun _ => none) ∅ ||
  PublicCompressionCouplingIdealLateLinks.alarm PublicCompressionCouplingIdealLateLinks.mixedCV
    table (compile Q iv [] p Q (by rfl) counted) (fun _ => none) [] ||
  hiddenGuess Q iv p counted table

open Classical in
 theorem actual_causalBad_probability {R : Type} (Q : Nat) (iv : Digest32)
    (p : Program R) (counted : Counts Q p) :
    letI := mixedKeyFintype Q
    average (fun table : Key Q → Digest32 =>
      if causalBad Q iv p counted table then (1:ℚ) else 0) ≤ duplexModeLoss Q := by
  let := mixedKeyFintype Q
  unfold duplexModeLoss
  apply le_min
  · calc
      _ ≤ average (fun _ : Key Q → Digest32 => (1:ℚ)) := by
        apply average_mono
        intro table
        split <;> norm_num
      _ = 1 := average_const _
  · have birthday := PublicCompressionCouplingBirthday.actual_mixed_birthday_bound
      (causalCompile Q iv [] p Q (by rfl) counted)
    have late := PublicCompressionCouplingIdealLateLinks.actual_pinned_mixed_probability Q iv p counted
    have hidden := actual_hiddenGuess_probability Q iv p counted
    have birthday' := birthday.trans (min_le_right _ _)
    have late' := late.trans (min_le_right _ _)
    have hidden' := hidden.trans (min_le_right _ _)
    have union : average (fun table : Key Q → Digest32 =>
        if causalBad Q iv p counted table then (1:ℚ) else 0) ≤
      average (fun table =>
        (if PublicCompressionCouplingBirthday.alarm table
          (causalCompile Q iv [] p Q (by rfl) counted) (fun _ => none) ∅ then (1:ℚ) else 0) +
        (if PublicCompressionCouplingIdealLateLinks.alarm PublicCompressionCouplingIdealLateLinks.mixedCV
          table (compile Q iv [] p Q (by rfl) counted) (fun _ => none) [] then (1:ℚ) else 0) +
        (if hiddenGuess Q iv p counted table then (1:ℚ) else 0)) := by
      apply average_mono
      intro table
      unfold causalBad
      cases PublicCompressionCouplingBirthday.alarm table
        (causalCompile Q iv [] p Q (by rfl) counted) (fun _ => none) ∅ <;>
        cases PublicCompressionCouplingIdealLateLinks.alarm PublicCompressionCouplingIdealLateLinks.mixedCV
          table (compile Q iv [] p Q (by rfl) counted) (fun _ => none) [] <;>
        cases hiddenGuess Q iv p counted table <;> norm_num
    rw [average_add,average_add] at union
    linarith

open Classical in
 theorem actual_ideal_causalBad_probability {R : Type} (Q : Nat) (iv : Digest32)
    (p : Program R) (counted : Counts Q p) :
    letI := DuplexPublicSimulator.seedFintype
    letI := rawOracleFintype Q
    average (fun coins : (RawKey Q → Digest32) × DuplexPublicSimulator.Seed =>
      if causalBad Q iv p counted (oracle coins.2 coins.1) then (1:ℚ) else 0) ≤ duplexModeLoss Q := by
  let := DuplexPublicSimulator.seedFintype
  let := rawOracleFintype Q
  let := mixedKeyFintype Q
  have bound := actual_causalBad_probability Q iv p counted
  rw [PublicCompressionCouplingIdealLateLinks.table_average_eq_ideal] at bound
  exact bound

#print axioms actual_causalBad_probability
#print axioms actual_ideal_causalBad_probability
end Whir.PublicCompressionCouplingMixed
