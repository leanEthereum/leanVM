import Whir.PCSRewindKnowledgeProbability

/-! Averaging is applied to actual accepted AND analysis-safe full trials.
The executable collector still retains every accepted trial. Averaging the safe
event directly avoids an unnecessary conditional-bad-event Markov loss. -/
namespace Whir.PCSRewindExtractor
open Concrete Protocol CausalGame KnowledgeExtraction
open SamplingProbability AuthenticatedResetProbability ResetAcceptanceAmplification

variable {Prefix Suffix Trial : Type*} [Fintype Prefix] [Nonempty Prefix]
  [Fintype Suffix] [Nonempty Suffix] [Fintype Trial] [Nonempty Trial]

/-- Accepted safe mass loses only the actual bad event, with arbitrary overlap. -/
theorem safe_acceptance_mass (accept bad : Trial → Prop) :
    probability accept - probability bad ≤ probability (fun t => accept t ∧ ¬ bad t) := by
  let events : Bool → Trial → Prop
    | false => fun t => accept t ∧ ¬ bad t
    | true => bad
  have cover : ∀ t, accept t → ∃ b, events b t := by
    intro t accepted
    by_cases badHere : bad t
    · exact ⟨true, badHere⟩
    · exact ⟨false, accepted, badHere⟩
  have bound := (mono _ _ cover).trans (union_le events)
  simp only [Fintype.sum_bool, events] at bound
  linarith

/-- Safe-prefix mass derives from acceptance; no availability is supplied. -/
theorem safe_good_prefix_mass (accept bad : Prefix × Suffix → Prop) :
    (probability accept - probability bad) / 2 ≤
      probability (GoodPrefix (fun t => accept t ∧ ¬ bad t)) := by
  exact (by linarith [safe_acceptance_mass accept bad] :
    (probability accept - probability bad) / 2 ≤
      probability (fun t => accept t ∧ ¬ bad t) / 2).trans
        (good_prefix_mass (fun t => accept t ∧ ¬ bad t))

/-- Whole safe acceptance yields a verified-output chance. The per-prefix
recovery premise is discharged by the actual heavy-coordinate certificate. -/
theorem safe_prefix_attempt_chance (accept bad : Prefix × Suffix → Prop)
    (success : Prefix × Trial → Prop) (δ : ℝ) (δnonneg : 0 ≤ δ) (δle : δ ≤ 1)
    (recover : ∀ p, GoodPrefix (fun t => accept t ∧ ¬ bad t) p →
      1 - δ ≤ probability (fun seed => success (p, seed))) :
    (probability accept - probability bad) / 2 * (1 - δ) ≤ probability success := by
  exact (mul_le_mul_of_nonneg_right
    (by linarith [safe_acceptance_mass accept bad] :
      (probability accept - probability bad) / 2 ≤
        probability (fun t => accept t ∧ ¬ bad t) / 2)
    (sub_nonneg.mpr δle)).trans
      (prefix_attempt_chance (fun t => accept t ∧ ¬ bad t) success δ δnonneg δle recover)

#print axioms safe_good_prefix_mass
#print axioms safe_prefix_attempt_chance
end Whir.PCSRewindExtractor
