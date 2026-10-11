import Whir.PublicCompressionCouplingActualMismatch
import Whir.PublicCompressionCouplingSourceStream

/-! Actual duplex whole-view distinguishing bound from the causal event ledger.
The sharp birthday bounds control individual subevents, while `duplexModeLoss`
covers unrestricted adaptive whole Views under one aggregate Counts Q cap. -/
namespace Whir.PublicCompressionCouplingActualJoint
open FiatShamirGame DuplexRefinement DuplexFraming DuplexModeGame
open TypedOracleCompiler (Sampling)
set_option maxRecDepth 4096
open PublicCompressionCouplingMixed

private theorem average_fintype {T : Type} (old new : Fintype T) (f : T → ℚ) :
    @average T old f = @average T new f := by
  cases Subsingleton.elim old new
  rfl

open Classical in
theorem actual_joint_mismatch_le_causalBad {R : Type}
    (Q : Nat) (iv : Digest32) (p : Program R) (counted : Counts Q p) :
    letI := mixedKeyFintype Q
    Sampling.expectation viewMismatch (actualJoint Q iv p counted) ≤
    average (fun table : Key Q → Digest32 =>
      if causalBad Q iv p counted table then (1:ℚ) else 0) := by
  let := mixedKeyFintype Q
  apply actual_joint_mismatch_le_causalBad_of_alignment Q iv p counted
  intro trace pair execution table quiet
  exact PublicCompressionCouplingSourceStream.actual_joint_good_view Q iv p counted
    execution table quiet

open Classical in
/-- Every existing adversary and whole-View observer is covered, including an
empty adversary-coin type. No operational correspondence hypothesis remains. -/
theorem actual_modeAdv_le_duplexModeLoss {AdvCoins R : Type} [Fintype AdvCoins]
    (Q : Nat) (iv : Digest32) (adversary : AdvCoins → Program R)
    (counted : ∀ a, Counts Q (adversary a)) (D : View R → Bool) :
    letI := DuplexPublicSimulator.seedFintype
    ModeAdv (DuplexPublicSimulator.simulator Q) iv adversary counted D ≤ duplexModeLoss Q := by
  let := DuplexPublicSimulator.seedFintype
  let := mixedKeyFintype Q
  by_cases populated : Nonempty AdvCoins
  swap
  · let : IsEmpty AdvCoins := not_nonempty_iff.mp populated
    have bound := actual_joint_observer_bound Q iv adversary counted D
    simp [average] at bound
    exact bound.trans (by unfold duplexModeLoss; apply le_min <;> positivity)
  let := populated
  calc
    _ ≤ average (fun a => Sampling.expectation viewMismatch
        (actualJoint Q iv (adversary a) (counted a))) :=
      actual_joint_observer_bound Q iv adversary counted D
    _ ≤ average (fun _ : AdvCoins => duplexModeLoss Q) := by
      apply average_mono
      intro a
      have mismatch := actual_joint_mismatch_le_causalBad Q iv (adversary a) (counted a)
      have risk := actual_causalBad_probability (R := R) Q iv (adversary a) (counted a)
      let canonical : Fintype (Key Q → Digest32) := inferInstance
      conv at mismatch => rhs; rw [average_fintype _ canonical]
      conv at risk => lhs; rw [average_fintype _ canonical]
      exact le_trans mismatch risk
    _ = duplexModeLoss Q := average_const _

#print axioms actual_joint_mismatch_le_causalBad
#print axioms actual_modeAdv_le_duplexModeLoss
end Whir.PublicCompressionCouplingActualJoint
