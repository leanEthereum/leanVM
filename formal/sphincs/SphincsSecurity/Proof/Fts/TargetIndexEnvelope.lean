import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Fts.TargetShapeCardinality
import SphincsSecurity.Proof.Fts.TargetShapeContinuation
namespace SphincsSecurity.Concrete

open ENNReal

noncomputable def targetIndexQuery (arrival : ENNReal) (moments : TargetIndexVector) (power degree : Nat) : ENNReal :=
  moments power degree + arrival * targetIndexCacheLower moments power degree

noncomputable def targetIndexSigning (uniform reuse : ENNReal) (moments : TargetIndexVector) (power degree : Nat) : ENNReal :=
  moments power degree + uniform *
    (targetIndexCacheLower moments power degree + targetIndexTreeLower moments power degree + targetIndexCacheLower (targetIndexTreeLower moments) power degree) +
      reuse * targetIndexReuseStep moments power degree

noncomputable def targetIndexEnvelope (uniform reuse arrival : ENNReal) (queries signings : Nat) (moments : TargetIndexVector) : TargetIndexVector :=
  (targetIndexSigning uniform reuse)^[signings] ((targetIndexQuery arrival)^[queries] moments)

theorem targetShapeQuery_lift (arrival : ENNReal) (moments : TargetIndexVector) :
    targetShapeQuery arrival (liftTargetIndexVector moments) = liftTargetIndexVector (targetIndexQuery arrival moments) := by
  funext groups remaining
  simp only [targetShapeQuery, targetCacheLower_lift, liftTargetIndexVector, targetIndexQuery]

theorem targetShapeSigning_lift (uniform reuse : ENNReal) (moments : TargetIndexVector)
    (groups : Finset (Finset FtsTree)) (remaining : Finset FtsTree) (hvalid : TargetShapeValid groups remaining) :
    targetShapeSigning uniform reuse (liftTargetIndexVector moments) groups remaining =
      liftTargetIndexVector (targetIndexSigning uniform reuse moments) groups remaining := by
  simp only [targetShapeSigning, targetTreeLower_lift, targetCacheLower_lift, targetReuseStep_lift moments groups remaining hvalid,
    liftTargetIndexVector, targetIndexSigning]

theorem targetShapeSigning_congr (uniform reuse : ENNReal) {f g : TargetShapeVector}
    (heq : ∀ G R, TargetShapeValid G R → f G R = g G R)
    (groups : Finset (Finset FtsTree)) (remaining : Finset FtsTree) (hvalid : TargetShapeValid groups remaining) :
    targetShapeSigning uniform reuse f groups remaining = targetShapeSigning uniform reuse g groups remaining :=
  le_antisymm (targetShapeSigning_mono uniform reuse (fun G R hv => (heq G R hv).le) groups remaining hvalid)
    (targetShapeSigning_mono uniform reuse (fun G R hv => (heq G R hv).ge) groups remaining hvalid)

theorem targetShapeEnvelope_congr (uniform reuse arrival : ENNReal) (queries signings : Nat) {f g : TargetShapeVector}
    (heq : ∀ G R, TargetShapeValid G R → f G R = g G R)
    (groups : Finset (Finset FtsTree)) (remaining : Finset FtsTree) (hvalid : TargetShapeValid groups remaining) :
    targetShapeEnvelope uniform reuse arrival queries signings f groups remaining =
      targetShapeEnvelope uniform reuse arrival queries signings g groups remaining :=
  le_antisymm (targetShapeEnvelope_mono uniform reuse arrival queries signings (fun G R hv => (heq G R hv).le) groups remaining hvalid)
    (targetShapeEnvelope_mono uniform reuse arrival queries signings (fun G R hv => (heq G R hv).ge) groups remaining hvalid)

theorem targetShapeQuery_iterate_lift (arrival : ENNReal) (queries : Nat) (moments : TargetIndexVector) :
    (targetShapeQuery arrival)^[queries] (liftTargetIndexVector moments) = liftTargetIndexVector ((targetIndexQuery arrival)^[queries] moments) := by
  induction queries with
  | zero => rfl
  | succ queries ih => simp only [Function.iterate_succ_apply', ih, targetShapeQuery_lift]

theorem targetShapeSigning_iterate_lift (uniform reuse : ENNReal) (signings : Nat) (moments : TargetIndexVector)
    (groups : Finset (Finset FtsTree)) (remaining : Finset FtsTree) (hvalid : TargetShapeValid groups remaining) :
    (targetShapeSigning uniform reuse)^[signings] (liftTargetIndexVector moments) groups remaining =
      liftTargetIndexVector ((targetIndexSigning uniform reuse)^[signings] moments) groups remaining := by
  induction signings generalizing groups remaining with
  | zero => rfl
  | succ signings ih =>
      simp only [Function.iterate_succ_apply']
      rw [targetShapeSigning_congr uniform reuse ih groups remaining hvalid]
      exact targetShapeSigning_lift uniform reuse _ groups remaining hvalid

theorem targetShapeEnvelope_lift (uniform reuse arrival : ENNReal) (queries signings : Nat) (moments : TargetIndexVector)
    (groups : Finset (Finset FtsTree)) (remaining : Finset FtsTree) (hvalid : TargetShapeValid groups remaining) :
    targetShapeEnvelope uniform reuse arrival queries signings (liftTargetIndexVector moments) groups remaining =
      targetIndexEnvelope uniform reuse arrival queries signings moments groups.card remaining.card := by
  unfold targetShapeEnvelope targetIndexEnvelope
  rw [targetShapeQuery_iterate_lift]
  exact targetShapeSigning_iterate_lift uniform reuse signings _ groups remaining hvalid

end SphincsSecurity.Concrete
