import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Fts.TargetShapeEnvelope
namespace SphincsSecurity.Concrete

open ENNReal

theorem targetCacheLower_tsum {α : Type} (moments : α → TargetShapeVector) (groups : Finset (Finset FtsTree)) (remaining : Finset FtsTree) :
    targetCacheLower (fun G R => ∑' result, moments result G R) groups remaining =
      ∑' result, targetCacheLower (moments result) groups remaining := by
  unfold targetCacheLower
  exact (Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)).symm

theorem targetTreeLower_tsum {α : Type} (moments : α → TargetShapeVector) (groups : Finset (Finset FtsTree)) (remaining : Finset FtsTree) :
    targetTreeLower (fun G R => ∑' result, moments result G R) groups remaining =
      ∑' result, targetTreeLower (moments result) groups remaining := by
  unfold targetTreeLower
  exact (Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)).symm

theorem targetReuseStep_tsum {α : Type} (moments : α → TargetShapeVector) (groups : Finset (Finset FtsTree)) (remaining : Finset FtsTree) :
    targetReuseStep (fun G R => ∑' result, moments result G R) groups remaining =
      ∑' result, targetReuseStep (moments result) groups remaining := by
  unfold targetReuseStep
  exact (Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)).symm

theorem targetShapeQuery_tsum {α : Type} (arrival : ENNReal) (moments : α → TargetShapeVector) (groups : Finset (Finset FtsTree)) (remaining : Finset FtsTree) :
    targetShapeQuery arrival (fun G R => ∑' result, moments result G R) groups remaining =
      ∑' result, targetShapeQuery arrival (moments result) groups remaining := by
  simp only [targetShapeQuery, targetCacheLower_tsum, ENNReal.tsum_mul_left, ENNReal.tsum_add]

theorem targetShapeSigning_tsum {α : Type} (uniform reuse : ENNReal) (moments : α → TargetShapeVector) (groups : Finset (Finset FtsTree)) (remaining : Finset FtsTree) :
    targetShapeSigning uniform reuse (fun G R => ∑' result, moments result G R) groups remaining =
      ∑' result, targetShapeSigning uniform reuse (moments result) groups remaining := by
  have htree : targetTreeLower (fun G R => ∑' result, moments result G R) =
      fun G R => ∑' result, targetTreeLower (moments result) G R := by
    funext G R
    exact targetTreeLower_tsum moments G R
  simp only [targetShapeSigning, htree, targetCacheLower_tsum, targetReuseStep_tsum, ENNReal.tsum_mul_left, ENNReal.tsum_add]

theorem targetShapeQuery_mul (arrival scalar : ENNReal) (moments : TargetShapeVector) (groups : Finset (Finset FtsTree)) (remaining : Finset FtsTree) :
    targetShapeQuery arrival (fun G R => scalar * moments G R) groups remaining =
      scalar * targetShapeQuery arrival moments groups remaining := by
  simp only [targetShapeQuery, targetCacheLower_mul]
  ring

theorem targetShapeSigning_mul (uniform reuse scalar : ENNReal) (moments : TargetShapeVector) (groups : Finset (Finset FtsTree)) (remaining : Finset FtsTree) :
    targetShapeSigning uniform reuse (fun G R => scalar * moments G R) groups remaining =
      scalar * targetShapeSigning uniform reuse moments groups remaining := by
  have htree : targetTreeLower (fun G R => scalar * moments G R) = fun G R => scalar * targetTreeLower moments G R := by
    funext G R
    exact targetTreeLower_mul scalar moments G R
  simp only [targetShapeSigning, htree, targetCacheLower_mul, targetReuseStep_mul]
  ring

theorem targetShapeEnvelope_tsum {α : Type} (uniform reuse arrival : ENNReal) (queries signatures : Nat)
    (moments : α → TargetShapeVector) (groups : Finset (Finset FtsTree)) (remaining : Finset FtsTree) :
    targetShapeEnvelope uniform reuse arrival queries signatures (fun G R => ∑' result, moments result G R) groups remaining =
      ∑' result, targetShapeEnvelope uniform reuse arrival queries signatures (moments result) groups remaining := by
  have hquery (count : Nat) : (targetShapeQuery arrival)^[count] (fun G R => ∑' result, moments result G R) =
      fun G R => ∑' result, (targetShapeQuery arrival)^[count] (moments result) G R := by
    induction count with
    | zero => rfl
    | succ count ih =>
        simp only [Function.iterate_succ_apply', ih]
        funext G R
        exact targetShapeQuery_tsum arrival _ G R
  unfold targetShapeEnvelope
  rw [hquery]
  induction signatures generalizing groups remaining with
  | zero => rfl
  | succ signatures ih =>
      simp only [Function.iterate_succ_apply']
      have hsign : (targetShapeSigning uniform reuse)^[signatures]
          (fun G R => ∑' result, (targetShapeQuery arrival)^[queries] (moments result) G R) =
          fun G R => ∑' result, (targetShapeSigning uniform reuse)^[signatures] ((targetShapeQuery arrival)^[queries] (moments result)) G R := by
        funext G R
        exact ih G R
      rw [hsign]
      exact targetShapeSigning_tsum uniform reuse _ groups remaining

theorem targetShapeEnvelope_mul (uniform reuse arrival scalar : ENNReal) (queries signatures : Nat)
    (moments : TargetShapeVector) (groups : Finset (Finset FtsTree)) (remaining : Finset FtsTree) :
    targetShapeEnvelope uniform reuse arrival queries signatures (fun G R => scalar * moments G R) groups remaining =
      scalar * targetShapeEnvelope uniform reuse arrival queries signatures moments groups remaining := by
  have hquery (count : Nat) : (targetShapeQuery arrival)^[count] (fun G R => scalar * moments G R) =
      fun G R => scalar * (targetShapeQuery arrival)^[count] moments G R := by
    induction count with
    | zero => rfl
    | succ count ih =>
        simp only [Function.iterate_succ_apply', ih]
        funext G R
        exact targetShapeQuery_mul arrival scalar _ G R
  unfold targetShapeEnvelope
  rw [hquery]
  induction signatures generalizing groups remaining with
  | zero => rfl
  | succ signatures ih =>
      simp only [Function.iterate_succ_apply']
      have hsign : (targetShapeSigning uniform reuse)^[signatures]
          (fun G R => scalar * (targetShapeQuery arrival)^[queries] moments G R) =
          fun G R => scalar * (targetShapeSigning uniform reuse)^[signatures] ((targetShapeQuery arrival)^[queries] moments) G R := by
        funext G R
        exact ih G R
      rw [hsign]
      exact targetShapeSigning_mul uniform reuse scalar _ groups remaining

theorem targetShapeEnvelope_expected {α : Type} (uniform reuse arrival : ENNReal) (queries signatures : Nat)
    (weight : α → ENNReal) (moments : α → TargetShapeVector) (groups : Finset (Finset FtsTree)) (remaining : Finset FtsTree) :
    (∑' result, weight result * targetShapeEnvelope uniform reuse arrival queries signatures (moments result) groups remaining) =
      targetShapeEnvelope uniform reuse arrival queries signatures (fun G R => ∑' result, weight result * moments result G R) groups remaining := by
  rw [targetShapeEnvelope_tsum]
  apply tsum_congr
  intro result
  exact (targetShapeEnvelope_mul uniform reuse arrival (weight result) queries signatures (moments result) groups remaining).symm

end SphincsSecurity.Concrete
