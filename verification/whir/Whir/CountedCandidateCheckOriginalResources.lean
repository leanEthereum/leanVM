import Whir.CountedCandidateCheckOriginalBounds

/-! Source field operations, bit tests, lookups, comparisons, loop visits and finite storage slots are separate logical units. These polynomials bound every such charged unit for guarded immutable original statements, without deriving dimensional restrictions from acceptance. They do not assert a wall-clock bound for an external prover. -/
namespace Whir.OriginalClaimsChecker
open Concrete Protocol CausalGame RingPCSGame CountedCandidateCheck

set_option maxHeartbeats 4000000

def preparationPolynomial (size families points : Nat) : Nat :=
  (532 * families + 536 * points + 151) * size + 661 * families + 286 * points + 570

def checkPolynomial (size families points : Nat) : Nat :=
  (384 * families + 9 * points + 12) * size + 256 * families + 5 * points + 5

def transformationPolynomial (size families points : Nat) : Nat :=
  (156 * families + 1) * size + 387 * families + 3 * points + 9930

theorem guarded_occupied_le (c : Config) (lanes : Nat) {m : Nat}
    (family : Fin m → FamilyClaim) (points : Array PointClaim) (anchorPoint : Array E)
    (guards : Guards c lanes family points anchorPoint) :
    lanes * 2 ^ (c.logN - c.folds[0]!) ≤ 2 ^ c.logN := by
  have scaled := Nat.mul_le_mul_right (2 ^ (c.logN - c.folds[0]!)) guards.2.2.2.1
  have foldBound := guards.1
  have exponent : c.folds[0]! + (c.logN - c.folds[0]!) = c.logN := by omega
  simpa only [← Nat.pow_add, exponent] using scaled

theorem preparationWork_total (c : Config) (lanes : Nat) {m : Nat}
    (family : Fin m → FamilyClaim) (points : Array PointClaim) (anchorPoint : Array E)
    (guards : Guards c lanes family points anchorPoint) :
    (preparationWork c family points anchorPoint).total ≤
      preparationPolynomial (2 ^ c.logN) m points.size := by
  have field := preparationField_bound c lanes family points anchorPoint guards
  have dimension := guards.2.1
  have anchorDimension := guards.2.2.2.2.1
  have families := sum_map_bound (List.finRange m)
    (fun j => (family j).point.size + 64 + 4) 132 (by
      intro j _
      have hd := (guards.2.2.2.2.2.1 j).1
      omega)
  have pointsBound := sum_map_bound (List.finRange points.size)
    (fun i => originalPointDimension points[i] + 6) 70 (by
      intro i _
      have hd := point_dimension _ _ _ (guards.2.2.2.2.2.2 i)
      omega)
  simp only [List.length_finRange] at families pointsBound
  have bits := Nat.mul_le_mul_left (2 * (m + points.size) * 2 ^ c.logN) dimension
  have lookups := Nat.mul_le_mul_left (2 * (m + points.size + 1) * 2 ^ c.logN)
    (show c.logN + 4 ≤ 68 by omega)
  have familyInner := Nat.mul_le_mul_left (2 ^ c.logN)
    (show 2 * c.logN + 4 ≤ 132 by omega)
  have familyLoops := Nat.mul_le_mul_left m (Nat.add_le_add_left familyInner 66)
  have pointInner := Nat.mul_le_mul_left (2 ^ c.logN)
    (show 2 * c.logN + 6 ≤ 134 by omega)
  have pointLoops := Nat.mul_le_mul_left points.size (Nat.add_le_add_left pointInner 2)
  unfold preparationWork Work.total preparationPolynomial preparationFieldPolynomial at *
  dsimp only at *
  nlinarith

theorem countedPrepare_total (c : Config) (lanes : Nat) {m : Nat}
    (family : Fin m → FamilyClaim) (points : Array PointClaim) (anchorPoint : Array E)
    (anchorValue : E) :
    (countedPrepare c lanes family points anchorPoint anchorValue).2.total ≤
      preparationPolynomial (2 ^ c.logN) m points.size := by
  unfold countedPrepare
  dsimp only
  split
  · rename_i valid
    exact preparationWork_total c lanes family points anchorPoint
      ((prepare_some_iff c lanes family points anchorPoint anchorValue).mp valid)
  · simp only [Work.total]
    unfold preparationPolynomial
    omega

theorem checkWork_total (c : Config) (lanes families points charge : Nat)
    (occupied : lanes * 2 ^ (c.logN - c.folds[0]!) ≤ 2 ^ c.logN)
    (field : charge ≤ checkFieldPolynomial (2 ^ c.logN) families points) :
    (checkWork c lanes families points charge).total ≤
      checkPolynomial (2 ^ c.logN) families points := by
  unfold checkWork Work.total checkPolynomial checkFieldPolynomial at *
  dsimp only at *
  nlinarith

theorem countedCheck_total {c : Config} {lanes m : Nat} {family : Fin m → FamilyClaim}
    {points : Array PointClaim} {anchorPoint : Array E} {anchorValue : E}
    (prepared : Prepared c lanes m family points anchorPoint anchorValue) (w : Witness c lanes) :
    (countedCheck prepared w).2.total ≤ checkPolynomial (2 ^ c.logN) m points.size := by
  have occupied := guarded_occupied_le c lanes family points anchorPoint prepared.guards
  have field := countedCheck_field prepared w
  unfold countedCheck at field ⊢
  dsimp only at field ⊢
  split <;> rename_i branch <;> simp only [branch, ite_true] at field <;>
    exact checkWork_total c lanes m points.size _ occupied field

theorem countedInput_total {c : Config} {lanes m : Nat} {family : Fin m → FamilyClaim}
    {points : Array PointClaim} {anchorPoint : Array E} {anchorValue : E}
    (prepared : Prepared c lanes m family points anchorPoint anchorValue) (root : BaseOracle)
    (publicPrefix : Prefix) :
    (countedInput prepared root publicPrefix).2.total = transformationPolynomial (2 ^ c.logN) m points.size := by
  simp only [countedInput, transformationWork, transformationField, Work.total, mapField_eq]
  unfold transformationPolynomial
  ring

#print axioms countedPrepare_total
#print axioms countedCheck_total
#print axioms countedInput_total

end Whir.OriginalClaimsChecker
