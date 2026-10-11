import Whir.CausalPositions

/-! Cumulative causal state on completed verifier messages. The step theorem
uses pointwise incoming-history fibers, not a marginal probability of an entire
tape. The concrete source ledger instantiates both hypotheses. -/
namespace Whir.PCSRoundByRoundKnowledge
open Concrete Protocol CausalGame CausalProbability
open Classical

noncomputable def state {c : Config} (bad : Coordinate c → Tape c → Prop)
    (completed : Finset (Coordinate c)) (t : Tape c) : Bool :=
  if ∃ q ∈ completed, bad q t then true else false

@[simp] theorem state_initial {c : Config} (bad : Coordinate c → Tape c → Prop)
    (t : Tape c) : state bad ∅ t = false := by
  classical
  simp [state]

theorem state_final {c : Config} (bad : Coordinate c → Tape c → Prop)
    (t : Tape c) : state bad Finset.univ t = true ↔ ∃ q, bad q t := by
  classical
  simp [state]

theorem state_next {c : Config} (bad : Coordinate c → Tape c → Prop)
    (completed : Finset (Coordinate c)) (q : Coordinate c) (t : Tape c) :
    state bad (insert q completed) t = true ↔ state bad completed t = true ∨ bad q t := by
  classical
  simp [state, or_comm]

open Classical in
/-- After any fixed undoomed public history, an arbitrary continuation can only
make this update doomed through the current message's actual event. Future
coins and extraction failure are allowed in `failure`; they are not conditioned
on or substituted for the local fiber. -/
theorem conditional_state_transition {c : Config}
    (bad : Coordinate c → Tape c → Prop) (completed : Finset (Coordinate c))
    (q : Coordinate c) (t : Tape c) (failure : Sample q → Prop) (epsilon : ℚ)
    (before : state bad completed t = false)
    (fixed : ∀ r ∈ completed, ∀ x : Sample q, bad r (set q t x) ↔ bad r t)
    (fiber : Soundness.uniformProb (Finset.univ.filter fun x : Sample q =>
      bad q (set q t x)) ≤ epsilon) :
    Soundness.uniformProb (Finset.univ.filter fun x : Sample q =>
      failure x ∧ state bad (insert q completed) (set q t x) = true) ≤ epsilon := by
  have included : (Finset.univ.filter fun x : Sample q =>
      failure x ∧ state bad (insert q completed) (set q t x) = true) ⊆
      Finset.univ.filter fun x : Sample q => bad q (set q t x) := by
    intro x member
    have doomed := (state_next bad completed q (set q t x)).mp (Finset.mem_filter.mp member).2.2
    rcases doomed with past | now
    · have pastEvent : ∃ r ∈ completed, bad r (set q t x) := by
        simpa only [state, ite_eq_left_iff, Bool.false_eq_true, imp_false, not_not] using past
      obtain ⟨r, member, event⟩ := pastEvent
      have old : state bad completed t = true := by
        simp only [state, ite_eq_left_iff, Bool.false_eq_true, imp_false, not_not]
        exact ⟨r, member, (fixed r member x).mp event⟩
      rw [before] at old
      contradiction
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, now⟩
  apply le_trans ?_ fiber
  unfold Soundness.uniformProb
  exact div_le_div_of_nonneg_right (Nat.cast_le.mpr (Finset.card_le_card included)) (by positivity)

#print axioms state_initial
#print axioms conditional_state_transition

end Whir.PCSRoundByRoundKnowledge
