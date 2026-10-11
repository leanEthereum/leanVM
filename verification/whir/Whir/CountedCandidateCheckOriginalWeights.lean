import Whir.CountedCandidateCheckArithmetic
import Whir.RingPCSGame

/-! Executable original-claim weight counters. Each actual equality-factor iteration reads one coordinate bit and one point entry, multiplies once, and adds only for a zero bit. Region and strided selectors retain the literal source predicates; their bounded-word metadata operations are separate from field arithmetic. -/
namespace Whir.CountedCandidateCheck
open Concrete Protocol CausalGame RingPCSGame
open scoped BigOperators

private def originalEqStep (point : Array E) (u : Nat) (value : E) (i : Fin point.size) : E × Nat :=
  if u.testBit i.val then (value * point[i], 1) else (value * (1 + point[i]), 2)

private theorem originalEqStep_value (point : Array E) (u : Nat) (value : E) (i : Fin point.size) :
    (originalEqStep point u value i).1 = value * (if u.testBit i.val then point[i] else 1 + point[i]) := by
  unfold originalEqStep
  split <;> rfl

def countedOriginalEqWeight (point : Array E) (u : Nat) : E × Nat :=
  loop (originalEqStep point u) (List.finRange point.size) (1, 0)

theorem countedOriginalEqWeight_value (point : Array E) (u : Nat) :
    (countedOriginalEqWeight point u).1 = RingPCSGame.eqWeight point u := by
  simp only [countedOriginalEqWeight, loop_value, originalEqStep_value, RingPCSGame.eqWeight,
    Fin.prod_univ_def, List.prod_eq_foldl, List.foldl_map]

theorem countedOriginalEqWeight_field (point : Array E) (u : Nat) :
    (countedOriginalEqWeight point u).2 ≤ 2 * point.size := by
  have bound := loop_bound (originalEqStep point u) (fun _ => True) 2
    (fun _ _ _ => trivial) (by intro value i _; unfold originalEqStep; split <;> simp)
    (List.finRange point.size) (1, 0) trivial
  simpa [countedOriginalEqWeight, Nat.mul_comm] using bound

/-- Exact source factor charges: the companion metadata pass need not recompute any field product. -/
theorem countedOriginalEqWeight_charge (point : Array E) (u : Nat) :
    (countedOriginalEqWeight point u).2 =
      ((List.finRange point.size).map fun i => 1 + if u.testBit i.val then 0 else 1).sum := by
  have charged := loop_constant_charge (originalEqStep point u)
    (fun i => 1 + if u.testBit i.val then 0 else 1)
    (by intro value i; unfold originalEqStep; split <;> simp_all)
    (List.finRange point.size) (1, 0)
  simpa [countedOriginalEqWeight] using charged

/-- Exact bit-read, point-lookup and product-loop lengths are identical to the actual source factor list. -/
theorem countedOriginalEqWeight_loops (point : Array E) :
    (List.finRange point.size).length = point.size := by simp

def countedOriginalRegionWeight (offset : Nat) (point : Array E) (v : Nat) : E × Nat :=
  if offset ≤ v ∧ v < offset + 2 ^ point.size then countedOriginalEqWeight point (v - offset) else (0, 0)

theorem countedOriginalRegionWeight_value (offset : Nat) (point : Array E) (v : Nat) :
    (countedOriginalRegionWeight offset point v).1 = regionWeight offset point v := by
  unfold countedOriginalRegionWeight regionWeight
  split <;> simp [countedOriginalEqWeight_value]

theorem countedOriginalRegionWeight_field (offset : Nat) (point : Array E) (v : Nat) :
    (countedOriginalRegionWeight offset point v).2 ≤ 2 * point.size := by
  unfold countedOriginalRegionWeight
  split
  · exact countedOriginalEqWeight_field _ _
  · simp

def originalPointDimension : PointClaim → Nat
  | .point _ point _ => point.size
  | .strided _ _ _ point _ => point.size

def countedOriginalPointWeight : PointClaim → Nat → E × Nat
  | .point offset point _, v => countedOriginalRegionWeight offset point v
  | .strided offset slot stride point _, v =>
    if offset + slot ≤ v ∧ v < offset + 2 ^ (stride + point.size) ∧
        (v - offset) % 2 ^ stride = slot then
      countedOriginalEqWeight point ((v - offset) / 2 ^ stride) else (0, 0)

theorem countedOriginalPointWeight_value (claim : PointClaim) (v : Nat) :
    (countedOriginalPointWeight claim v).1 = pointWeight claim v := by
  cases claim with
  | point offset point value => exact countedOriginalRegionWeight_value _ _ _
  | strided offset slot stride point value =>
    simp only [countedOriginalPointWeight, pointWeight]
    split <;> simp [countedOriginalEqWeight_value]

theorem countedOriginalPointWeight_field (claim : PointClaim) (v : Nat) :
    (countedOriginalPointWeight claim v).2 ≤ 2 * originalPointDimension claim := by
  cases claim with
  | point offset point value => exact countedOriginalRegionWeight_field _ _ _
  | strided offset slot stride point value =>
    simp only [countedOriginalPointWeight, originalPointDimension]
    split
    · exact countedOriginalEqWeight_field _ _
    · simp

#print axioms countedOriginalEqWeight_value
#print axioms countedOriginalPointWeight_value

end Whir.CountedCandidateCheck
