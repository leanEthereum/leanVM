import Whir.PublicCompressionCouplingActualJointBound
import Whir.PublicCompressionCouplingJointResidual

/-! Residual-cache accounting for the actual joint full-View mismatch. The
operational good-event implication is separated from the exact finite marginal
identity; the final distinguishing endpoint instantiates that implication. -/
namespace Whir.PublicCompressionCouplingActualJoint
open FiatShamirGame DuplexRefinement DuplexFraming DuplexModeGame
open TypedOracleCompiler (Sampling)
open RawOracleCoupling PublicCompressionCouplingJoint PublicCompressionCouplingMixed

open Classical in
theorem actual_joint_residual_causalBad {R : Type} (Q : Nat) (iv : Digest32)
    (p : Program R) (counted : Counts Q p) :
    letI := mixedKeyFintype Q
    Sampling.expectation (fun pair => average (fun table : Key Q → Digest32 =>
      if causalBad Q iv p counted (overlay pair.2.2 table) then (1:ℚ) else 0))
      (actualJoint Q iv p counted) =
    average (fun table : Key Q → Digest32 =>
      if causalBad Q iv p counted table then (1:ℚ) else 0) := by
  let := mixedKeyFintype Q
  rw [actualJoint, joint_second_residual
    (PublicCompressionProgram.compile iv p Q counted) (fun _ => none)
    (causalCompile Q iv [] p Q (by rfl) counted) (fun _ => none)
    (fun _ table => if causalBad Q iv p counted table then (1:ℚ) else 0)]
  rfl

open Classical in
/-- The operational premise is discharged by actual source alignment in the
closed endpoint, not supplied by an adversary or observer. -/
theorem actual_joint_mismatch_le_causalBad_of_alignment {R : Type}
    (Q : Nat) (iv : Digest32) (p : Program R) (counted : Counts Q p)
    (alignment : ∀ trace pair, Sampling.Runs (actualJoint Q iv p counted) trace pair →
      ∀ table : Key Q → Digest32,
      causalBad Q iv p counted (overlay pair.2.2 table) = false →
      pair.1.1.view = pair.2.1.1) :
    letI := mixedKeyFintype Q
    Sampling.expectation viewMismatch (actualJoint Q iv p counted) ≤
    average (fun table : Key Q → Digest32 =>
      if causalBad Q iv p counted table then (1:ℚ) else 0) := by
  let := mixedKeyFintype Q
  rw [← actual_joint_residual_causalBad Q iv p counted]
  apply expectation_mono_runs
  intro trace pair execution
  calc
    viewMismatch pair = average (fun _ : Key Q → Digest32 => viewMismatch pair) :=
      (average_const _).symm
    _ ≤ average (fun table : Key Q → Digest32 =>
        if causalBad Q iv p counted (overlay pair.2.2 table) then (1:ℚ) else 0) := by
      apply average_mono
      intro table
      cases bad : causalBad Q iv p counted (overlay pair.2.2 table) with
      | false => simp [viewMismatch, alignment trace pair execution table bad]
      | true => simp only [↓reduceIte, viewMismatch]; split <;> norm_num

#print axioms actual_joint_residual_causalBad
#print axioms actual_joint_mismatch_le_causalBad_of_alignment
end Whir.PublicCompressionCouplingActualJoint
