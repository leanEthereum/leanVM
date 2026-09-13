import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Fts.TargetShapeEnvelope
namespace SphincsSecurity.Concrete

open ENNReal

theorem targetShapeQuery_iterate_mono (arrival : ENNReal) (queries : Nat) {f g : TargetShapeVector} (h : TargetShapeLE f g) :
    TargetShapeLE ((targetShapeQuery arrival)^[queries] f) ((targetShapeQuery arrival)^[queries] g) := by
  induction queries with
  | zero => exact h
  | succ queries ih =>
      simp only [Function.iterate_succ_apply']
      exact targetShapeQuery_mono arrival ih

theorem targetShapeEnvelope_mono (uniform reuse arrival : ENNReal) (queries signings : Nat)
    {f g : TargetShapeVector} (h : TargetShapeLE f g) :
    TargetShapeLE (targetShapeEnvelope uniform reuse arrival queries signings f) (targetShapeEnvelope uniform reuse arrival queries signings g) :=
  targetShapeSigning_iterate_mono uniform reuse signings (targetShapeQuery_iterate_mono arrival queries h)

theorem targetShapeEnvelope_queries_mono (uniform reuse arrival : ENNReal) (signings : Nat) (f : TargetShapeVector)
    {small large : Nat} (h : small ≤ large) :
    TargetShapeLE (targetShapeEnvelope uniform reuse arrival small signings f) (targetShapeEnvelope uniform reuse arrival large signings f) := by
  apply targetShapeSigning_iterate_mono
  intro G R _
  exact Function.monotone_iterate_of_id_le (show ∀ f : TargetShapeVector, f ≤ targetShapeQuery arrival f from fun _ _ _ => le_self_add) h f G R

theorem le_targetShapeEnvelope (uniform reuse arrival : ENNReal) (queries signings : Nat) (f : TargetShapeVector) :
    f ≤ targetShapeEnvelope uniform reuse arrival queries signings f :=
  (Function.id_le_iterate_of_id_le (show ∀ f : TargetShapeVector, f ≤ targetShapeQuery arrival f from fun _ _ _ => le_self_add) queries f).trans
    (Function.id_le_iterate_of_id_le (show ∀ f : TargetShapeVector, f ≤ targetShapeSigning uniform reuse f from
      fun _ _ _ => le_self_add.trans le_self_add) signings _)

theorem targetShapeEnvelope_query (uniform reuse arrival : ENNReal) (queries signings : Nat) (f : TargetShapeVector) :
    targetShapeEnvelope uniform reuse arrival queries signings (targetShapeQuery arrival f) =
      targetShapeEnvelope uniform reuse arrival (queries + 1) signings f := by
  simp only [targetShapeEnvelope, Function.iterate_succ_apply]

theorem targetShapeQuery_iterate_signing_le (uniform reuse arrival : ENNReal) (queries : Nat) (f : TargetShapeVector) :
    TargetShapeLE ((targetShapeQuery arrival)^[queries] (targetShapeSigning uniform reuse f))
      (targetShapeSigning uniform reuse ((targetShapeQuery arrival)^[queries] f)) := by
  induction queries with
  | zero => exact TargetShapeLE.refl _
  | succ queries ih =>
      simp only [Function.iterate_succ_apply']
      exact (targetShapeQuery_mono arrival ih).trans (targetShapeQuery_signing_le uniform reuse arrival _)

theorem targetShapeEnvelope_signing_le (uniform reuse arrival : ENNReal) (queries signings : Nat) (f : TargetShapeVector) :
    TargetShapeLE (targetShapeEnvelope uniform reuse arrival queries signings (targetShapeSigning uniform reuse f))
      (targetShapeEnvelope uniform reuse arrival queries (signings + 1) f) := by
  unfold targetShapeEnvelope
  rw [Function.iterate_succ_apply]
  exact targetShapeSigning_iterate_mono uniform reuse signings (targetShapeQuery_iterate_signing_le uniform reuse arrival queries f)

end SphincsSecurity.Concrete
