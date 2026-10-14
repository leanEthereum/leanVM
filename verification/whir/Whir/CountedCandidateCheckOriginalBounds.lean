import Whir.CountedCandidateCheckOriginalCost
import Whir.CountedCandidateCheckOriginalCorrectness

/-! Complete source-derived bounds for immutable original preparation, one cached public transformation and one actual final checker. The physical cube length is explicit, and malformed preparation never runs its allocating/field-arithmetic branch. -/
namespace Whir.OriginalClaimsChecker
open Concrete Protocol CausalGame RingPCSGame CountedCandidateCheck
open scoped BigOperators

set_option maxHeartbeats 4000000

private theorem eqCharge_source (point : Array E) (v : Nat) :
    eqCharge point v = (countedOriginalEqWeight point v).2 :=
  (countedOriginalEqWeight_charge point v).symm

private theorem eqCharge_bound (point : Array E) (v : Nat) : eqCharge point v ≤ 2 * point.size := by
  rw [eqCharge_source]
  exact countedOriginalEqWeight_field _ _

private theorem regionCharge_bound (offset : Nat) (point : Array E) (v : Nat) :
    regionCharge offset point v ≤ 2 * point.size := by
  unfold regionCharge
  split
  · exact eqCharge_bound _ _
  · simp

private theorem pointCharge_bound (claim : PointClaim) (v : Nat) :
    pointCharge claim v ≤ 2 * originalPointDimension claim := by
  cases claim with
  | point offset point value => exact regionCharge_bound _ _ _
  | strided offset slot stride point value =>
    simp only [pointCharge, originalPointDimension]
    split
    · exact eqCharge_bound _ _
    · simp

theorem sum_map_bound {X : Type*} (xs : List X) (f : X → Nat) (bound : Nat)
    (each : ∀ x ∈ xs, f x ≤ bound) : (xs.map f).sum ≤ xs.length * bound := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have current := each x (by simp)
    have rest := ih (fun y member => each y (by simp [member]))
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    nlinarith

theorem point_dimension (dimension occupied : Nat) (claim : PointClaim)
    (guarded : pointGuard dimension occupied claim) : originalPointDimension claim ≤ dimension := by
  cases claim <;> simp only [pointGuard, originalPointDimension] at * <;> omega

def preparationFieldPolynomial (size families points : Nat) : Nat :=
  128 * size * (families + points) + 3 * size + 64

def checkFieldPolynomial (size families points : Nat) : Nat :=
  64 * families * size + 2 * (points + 1) * size

theorem preparationField_bound (c : Config) (lanes : Nat) {m : Nat} (family : Fin m → FamilyClaim)
    (points : Array PointClaim) (anchorPoint : Array E)
    (guards : Guards c lanes family points anchorPoint) :
    preparationField c family points anchorPoint ≤ preparationFieldPolynomial (2 ^ c.logN) m points.size := by
  have familyDimension := guards.2.2.2.2.2.1
  have pointDimension := guards.2.2.2.2.2.2
  have familyCost := sum_map_bound (List.finRange m)
    (fun j => ((List.range (2 ^ c.logN)).map (regionCharge (family j).offset (family j).point)).sum)
    (2 ^ c.logN * (2 * c.logN)) (by
      intro j _
      have bound := sum_map_bound (List.range (2 ^ c.logN))
        (regionCharge (family j).offset (family j).point) (2 * c.logN) (by
          intro v _
          exact (regionCharge_bound _ _ _).trans (Nat.mul_le_mul_left 2 (familyDimension j).1))
      simpa using bound)
  have pointCost := sum_map_bound (List.finRange points.size)
    (fun i => ((List.range (2 ^ c.logN)).map (pointCharge points[i])).sum)
    (2 ^ c.logN * (2 * c.logN)) (by
      intro i _
      have bound := sum_map_bound (List.range (2 ^ c.logN)) (pointCharge points[i])
        (2 * c.logN) (by
          intro v _
          exact (pointCharge_bound _ _).trans
            (Nat.mul_le_mul_left 2 (point_dimension _ _ _ (pointDimension i))))
      simpa using bound)
  simp only [List.length_finRange] at familyCost pointCost
  have dimension := guards.2.1
  have pointSize := guards.2.2.2.2.1
  have dense : 2 ^ anchorPoint.size - 1 ≤ 2 ^ c.logN := by rw [pointSize]; exact Nat.sub_le _ _
  have perDimension : 2 ^ c.logN * (2 * c.logN) ≤ 2 ^ c.logN * 128 :=
    Nat.mul_le_mul_left _ (by omega)
  have familyBudget := familyCost.trans (Nat.mul_le_mul_left m perDimension)
  have pointBudget := pointCost.trans (Nat.mul_le_mul_left points.size perDimension)
  unfold preparationField preparationFieldPolynomial Whir.ExtractorArithmeticCost.tableCharge
  nlinarith

theorem countedPrepare_field (c : Config) (lanes : Nat) {m : Nat} (family : Fin m → FamilyClaim)
    (points : Array PointClaim) (anchorPoint : Array E) (anchorValue : E) :
    (countedPrepare c lanes family points anchorPoint anchorValue).2.fieldArithmetic ≤
      preparationFieldPolynomial (2 ^ c.logN) m points.size := by
  unfold countedPrepare
  dsimp only
  split
  · rename_i valid
    have guarded : Guards c lanes family points anchorPoint :=
      (prepare_some_iff c lanes family points anchorPoint anchorValue).mp valid
    exact preparationField_bound c lanes family points anchorPoint guarded
  · simp [preparationFieldPolynomial]

theorem countedCheck_value {c : Config} {lanes m : Nat} {family : Fin m → FamilyClaim}
    {points : Array PointClaim} {anchorPoint : Array E} {anchorValue : E}
    (prepared : Prepared c lanes m family points anchorPoint anchorValue) (w : Witness c lanes) :
    (countedCheck prepared w).1 = check prepared w := by
  simp only [countedCheck, arithmeticAll_value, countedSlice_value, countedDot_value,
    Array.all_toList, check]
  split <;> rfl

theorem countedCheck_field {c : Config} {lanes m : Nat} {family : Fin m → FamilyClaim}
    {points : Array PointClaim} {anchorPoint : Array E} {anchorValue : E}
    (prepared : Prepared c lanes m family points anchorPoint anchorValue) (w : Witness c lanes) :
    (countedCheck prepared w).2.fieldArithmetic ≤ checkFieldPolynomial (2 ^ c.logN) m points.size := by
  have familySize : ∀ j : Fin m, prepared.familyWeights[j.val]!.size = 2 ^ c.logN := by
    intro j
    rw [prepared.familyWeights_eq]
    simp [getElem!_pos, j.isLt]
  have familyCost := arithmeticAll_field
    (fun j : Fin m => arithmeticAll (fun bit : Fin 64 =>
      let value := countedSlice (Array.ofFn w) prepared.familyWeights[j.val]! bit
      (value.1 == (prepared.familyTargets[j.val]!)[bit.val]!, value.2)) (List.finRange 64))
    (List.finRange m) (64 * 2 ^ c.logN) (by
      intro j _
      have inner := arithmeticAll_field
        (fun bit : Fin 64 =>
          let value := countedSlice (Array.ofFn w) prepared.familyWeights[j.val]! bit
          (value.1 == (prepared.familyTargets[j.val]!)[bit.val]!, value.2))
        (List.finRange 64) (2 ^ c.logN) (by
          intro bit _
          simpa only [familySize j] using countedSlice_field (Array.ofFn w) prepared.familyWeights[j.val]! bit)
      simpa using inner)
  have pointsCost := arithmeticAll_field
    (fun claim : Claim =>
      let value := countedDot (tab (2 ^ c.logN) fun i => E.ofK ((Array.ofFn w)[i]?.getD 0)) claim.weight
      (value.1 == claim.value, value.2)) prepared.pointClaims.toList (2 * 2 ^ c.logN) (by
        intro claim _
        exact Nat.mul_le_mul_left 2 (by
          simp))
  have pointCount : prepared.pointClaims.toList.length = points.size := by
    rw [prepared.pointClaims_eq]
    simp
  have anchorCost :
      (countedDot (tab (2 ^ c.logN) fun i => E.ofK ((Array.ofFn w)[i]?.getD 0)) prepared.anchorTable).2 ≤
        2 * 2 ^ c.logN :=
    Nat.mul_le_mul_left 2 (by
      simp)
  simp only [List.length_finRange, pointCount] at familyCost pointsCost
  unfold countedCheck
  dsimp only
  split <;> dsimp only [checkWork] <;> unfold checkFieldPolynomial <;> nlinarith

theorem countedInput_field {c : Config} {lanes m : Nat} {family : Fin m → FamilyClaim}
    {points : Array PointClaim} {anchorPoint : Array E} {anchorValue : E}
    (prepared : Prepared c lanes m family points anchorPoint anchorValue) (root : BaseOracle)
    (publicPrefix : Prefix) : (countedInput prepared root publicPrefix).2.fieldArithmetic =
      m + 77 * m * 2 ^ c.logN + 64 * (2 * m + 77) := by
  simp [countedInput, transformationWork, transformationField, mapField_eq]
  ring

#print axioms countedPrepare_field
#print axioms countedCheck_value
#print axioms countedCheck_field
#print axioms countedInput_field

end Whir.OriginalClaimsChecker
