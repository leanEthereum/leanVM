import Whir.PublicCompressionCouplingActualJoint

/-! The whole-public-View fundamental inequality for the literal shared-answer
coupling. Its right side is the actual coupling's View mismatch, not a supplied
certificate or a primitive soundness assumption. -/
namespace Whir.PublicCompressionCouplingActualJoint
open FiatShamirGame DuplexRefinement DuplexFraming DuplexModeGame
open TypedOracleCompiler (Sampling)

private theorem expectation_mono {K R : Type} {n : Nat}
    (p : Sampling K (fun _ => Digest32) R n) {f g : R → ℚ} (h : ∀ r, f r ≤ g r) :
    Sampling.expectation f p ≤ Sampling.expectation g p := by
  induction p with
  | ret result => exact h result
  | draw key next ih => exact average_mono (fun answer => ih answer)

private theorem expectation_add {K R : Type} {n : Nat}
    (p : Sampling K (fun _ => Digest32) R n) (f g : R → ℚ) :
    Sampling.expectation (fun r => f r+g r) p =
      Sampling.expectation f p+Sampling.expectation g p := by
  induction p with
  | ret result => rfl
  | draw key next ih =>
    simp only [Sampling.expectation,ih,average_add]

abbrev JointResult (Q : Nat) (R : Type) :=
  (Execution R × PublicCompressionCouplingJoint.Cache Node) ×
    ((View R × List PublicCompressionCouplingMixed.InspectedConstruction) ×
      PublicCompressionCouplingJoint.Cache (PublicCompressionCouplingMixed.Key Q))

open Classical in
noncomputable def viewMismatch {Q : Nat} {R : Type} (result : JointResult Q R) : ℚ :=
  if result.1.1.view = result.2.1.1 then 0 else 1

open Classical in
 theorem actual_joint_observer_bound {AdvCoins R : Type} [Fintype AdvCoins]
    (Q : Nat) (iv : Digest32) (adversary : AdvCoins → Program R)
    (counted : ∀ a, Counts Q (adversary a)) (D : View R → Bool) :
    letI := DuplexPublicSimulator.seedFintype
    ModeAdv (DuplexPublicSimulator.simulator Q) iv adversary counted D ≤
      average (fun a => Sampling.expectation viewMismatch
        (actualJoint Q iv (adversary a) (counted a))) := by
  let := DuplexPublicSimulator.seedFintype
  unfold ModeAdv
  rw [← actual_joint_real Q iv adversary counted D,← actual_joint_ideal Q iv adversary counted D]
  by_cases populated : Nonempty AdvCoins
  swap
  · let : IsEmpty AdvCoins := not_nonempty_iff.mp populated
    simp [average]
  let := populated
  apply abs_le.mpr
  constructor
  · have bound : average (fun a => Sampling.expectation
        (fun pair => if D pair.2.1.1 then (1:ℚ) else 0)
        (actualJoint Q iv (adversary a) (counted a))) ≤
      average (fun a => Sampling.expectation
        (fun pair => if D pair.1.1.view then (1:ℚ) else 0)
        (actualJoint Q iv (adversary a) (counted a))) +
      average (fun a => Sampling.expectation viewMismatch
        (actualJoint Q iv (adversary a) (counted a))) := by
      rw [← average_add]
      apply average_mono
      intro a
      rw [← expectation_add]
      apply expectation_mono
      intro pair
      by_cases equal : pair.1.1.view = pair.2.1.1
      · simp only [viewMismatch,equal,↓reduceIte,add_zero,le_refl]
      · simp only [viewMismatch,equal,↓reduceIte]
        cases D pair.1.1.view <;> cases D pair.2.1.1 <;> norm_num
    linarith
  · have bound : average (fun a => Sampling.expectation
        (fun pair => if D pair.1.1.view then (1:ℚ) else 0)
        (actualJoint Q iv (adversary a) (counted a))) ≤
      average (fun a => Sampling.expectation
        (fun pair => if D pair.2.1.1 then (1:ℚ) else 0)
        (actualJoint Q iv (adversary a) (counted a))) +
      average (fun a => Sampling.expectation viewMismatch
        (actualJoint Q iv (adversary a) (counted a))) := by
      rw [← average_add]
      apply average_mono
      intro a
      rw [← expectation_add]
      apply expectation_mono
      intro pair
      by_cases equal : pair.1.1.view = pair.2.1.1
      · simp only [viewMismatch,equal,↓reduceIte,add_zero,le_refl]
      · simp only [viewMismatch,equal,↓reduceIte]
        cases D pair.1.1.view <;> cases D pair.2.1.1 <;> norm_num
    linarith

#print axioms actual_joint_observer_bound
end Whir.PublicCompressionCouplingActualJoint
