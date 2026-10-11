import Whir.CountedCandidateCheckOriginal
import Whir.CountedCandidateCheckLoops

/-! Concrete original-checker resource counters. Field charges follow the source product, sum, square and power loops. Non-field charges include bit reads, array lookups, comparisons, loop visits and admitted finite input/output slots. Upper charges also cover source short-circuiting; no supplied cost model determines any coefficient. -/
namespace Whir.OriginalClaimsChecker
open Concrete Protocol CausalGame RingPCSGame CountedCandidateCheck
open scoped BigOperators

set_option maxHeartbeats 4000000

structure Work where
  fieldArithmetic : Nat := 0
  bitReads : Nat := 0
  lookups : Nat := 0
  comparisons : Nat := 0
  iterations : Nat := 0
  slots : Nat := 0
  deriving Repr, BEq

def Work.total (work : Work) : Nat := work.fieldArithmetic + work.bitReads + work.lookups +
  work.comparisons + work.iterations + work.slots

/-- This charge uses only metadata and bit tests, not a second execution of the field products. -/
def eqCharge (point : Array E) (v : Nat) : Nat :=
  ((List.finRange point.size).map fun i => 1 + if v.testBit i.val then 0 else 1).sum

def regionCharge (offset : Nat) (point : Array E) (v : Nat) : Nat :=
  if offset ≤ v ∧ v < offset + 2 ^ point.size then eqCharge point (v - offset) else 0

def pointCharge : PointClaim → Nat → Nat
  | .point offset point _, v => regionCharge offset point v
  | .strided offset slot stride point _, v =>
    if offset + slot ≤ v ∧ v < offset + 2 ^ (stride + point.size) ∧
        (v - offset) % 2 ^ stride = slot then eqCharge point ((v - offset) / 2 ^ stride) else 0

def preparationField (c : Config) {m : Nat} (family : Fin m → FamilyClaim)
    (points : Array PointClaim) (anchorPoint : Array E) : Nat :=
  ((List.finRange m).map fun j => ((List.range (2 ^ c.logN)).map
    (regionCharge (family j).offset (family j).point)).sum).sum +
  ((List.finRange points.size).map fun i => ((List.range (2 ^ c.logN)).map (pointCharge points[i])).sum).sum +
  Whir.ExtractorArithmeticCost.tableCharge anchorPoint + 64

/-- Includes the extra metadata-only charge traversal, so instrumentation bookkeeping does not disappear from the non-field resource boundary. -/
def preparationWork (c : Config) {m : Nat} (family : Fin m → FamilyClaim)
    (points : Array PointClaim) (anchorPoint : Array E) : Work :=
  let dimensionWords := ((List.finRange m).map fun j => (family j).point.size + 64 + 4).sum +
    ((List.finRange points.size).map fun i => originalPointDimension points[i] + 6).sum + anchorPoint.size + 12
  { fieldArithmetic := preparationField c family points anchorPoint
    bitReads := 2 * (m + points.size) * 2 ^ c.logN * c.logN
    lookups := 3 * dimensionWords + 2 * (m + points.size + 1) * 2 ^ c.logN * (c.logN + 4)
    comparisons := 5 + 3 * m + 4 * points.size + (4 * m + 6 * points.size) * 2 ^ c.logN
    iterations := 5 + m * (66 + 2 ^ c.logN * (2 * c.logN + 4)) +
      points.size * (2 + 2 ^ c.logN * (2 * c.logN + 6)) + 4 * 2 ^ c.logN + c.logN + 64
    slots := 4 * (m + points.size + 2) * 2 ^ c.logN + 64 * m + 64 + dimensionWords }

def countedPrepare (c : Config) (lanes : Nat) {m : Nat} (family : Fin m → FamilyClaim)
    (points : Array PointClaim) (anchorPoint : Array E) (anchorValue : E) :
    Option (Prepared c lanes m family points anchorPoint anchorValue) × Work :=
  let result := prepare c lanes family points anchorPoint anchorValue
  if result.isSome then (result, preparationWork c family points anchorPoint) else
    (result, { comparisons := 16 * (m + points.size + 1), iterations := 16 * (m + points.size + 1) })

theorem countedPrepare_value (c : Config) (lanes : Nat) {m : Nat} (family : Fin m → FamilyClaim)
    (points : Array PointClaim) (anchorPoint : Array E) (anchorValue : E) :
    (countedPrepare c lanes family points anchorPoint anchorValue).1 =
      prepare c lanes family points anchorPoint anchorValue := by
  unfold countedPrepare
  dsimp only
  split <;> rfl

def countedSliceLoop (words : Array K) (weights : Array E) (bit : Fin 64) :
    Nat → Nat → E × Nat → E × Nat
  | 0, _, state => state
  | fuel + 1, offset, state =>
    let next := if wordBit (words[offset]?.getD 0) bit then
      (state.1 + weights[offset]!, state.2 + 1) else state
    countedSliceLoop words weights bit fuel (offset + 1) next

def countedSlice (words : Array K) (weights : Array E) (bit : Fin 64) : E × Nat :=
  countedSliceLoop words weights bit weights.size 0 (0, 0)

private theorem countedSliceLoop_value (words : Array K) (weights : Array E) (bit : Fin 64)
    (fuel offset : Nat) (state : E × Nat) :
    (countedSliceLoop words weights bit fuel offset state).1 =
      sliceLoop words weights bit fuel offset state.1 := by
  induction fuel generalizing offset state with
  | zero => rfl
  | succ fuel ih =>
    simp only [countedSliceLoop, sliceLoop]
    split <;> simp_all

private theorem countedSliceLoop_field (words : Array K) (weights : Array E) (bit : Fin 64)
    (fuel offset : Nat) (state : E × Nat) :
    (countedSliceLoop words weights bit fuel offset state).2 ≤ state.2 + fuel := by
  induction fuel generalizing offset state with
  | zero => simp [countedSliceLoop]
  | succ fuel ih =>
    simp only [countedSliceLoop]
    split
    · exact (ih (offset + 1) (state.1 + weights[offset]!, state.2 + 1)).trans_eq (by omega)
    · exact (ih (offset + 1) state).trans (by omega)

theorem countedSlice_value (words : Array K) (weights : Array E) (bit : Fin 64) :
    (countedSlice words weights bit).1 = slice words weights bit := countedSliceLoop_value _ _ _ _ _ _

theorem countedSlice_field (words : Array K) (weights : Array E) (bit : Fin 64) :
    (countedSlice words weights bit).2 ≤ weights.size := by
  simpa [countedSlice] using countedSliceLoop_field words weights bit weights.size 0 (0, 0)

/-- The predicate runs only until its first actual false result, retaining all field work already performed. -/
def arithmeticAll {X : Type*} (predicate : X → Bool × Nat) : List X → Bool × Nat
  | [] => (true, 0)
  | x :: xs =>
    let next := predicate x
    if next.1 then
      let rest := arithmeticAll predicate xs
      (rest.1, next.2 + rest.2)
    else (false, next.2)

theorem arithmeticAll_value {X : Type*} (predicate : X → Bool × Nat) (xs : List X) :
    (arithmeticAll predicate xs).1 = xs.all (fun x => (predicate x).1) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [arithmeticAll, List.all_cons, ih]; split <;> simp_all

theorem arithmeticAll_field {X : Type*} (predicate : X → Bool × Nat) (xs : List X)
    (bound : Nat) (each : ∀ x ∈ xs, (predicate x).2 ≤ bound) :
    (arithmeticAll predicate xs).2 ≤ xs.length * bound := by
  induction xs with
  | nil => simp [arithmeticAll]
  | cons x xs ih =>
    have current := each x (by simp)
    have rest := ih (fun y member => each y (by simp [member]))
    simp only [arithmeticAll, List.length_cons]
    split <;> dsimp only <;> nlinarith

def checkWork (c : Config) (lanes m points : Nat) (fieldArithmetic : Nat) : Work :=
  let size := 2 ^ c.logN
  { fieldArithmetic
    bitReads := 64 * m * size
    lookups := 2 * 64 * m * size + 4 * (points + 1) * size + lanes * 2 ^ (c.logN - c.folds[0]!)
    comparisons := 3 * (64 * m + points + 1) + 64 * m * size
    iterations := 64 * m * (size + 1) + 2 * (points + 1) * (size + 1)
    slots := lanes * 2 ^ (c.logN - c.folds[0]!) + size + (points + 1) * size }

def countedCheck {c : Config} {lanes m : Nat} {family : Fin m → FamilyClaim}
    {points : Array PointClaim} {anchorPoint : Array E} {anchorValue : E}
    (prepared : Prepared c lanes m family points anchorPoint anchorValue) (w : Witness c lanes) : Bool × Work :=
  let words := Array.ofFn w
  let familyOk := arithmeticAll (fun j : Fin m => arithmeticAll (fun bit : Fin 64 =>
    let value := countedSlice words prepared.familyWeights[j.val]! bit
    (value.1 == (prepared.familyTargets[j.val]!)[bit.val]!, value.2)) (List.finRange 64)) (List.finRange m)
  if !familyOk.1 then (false, checkWork c lanes m points.size familyOk.2) else
    let packed := tab (2 ^ c.logN) fun i => E.ofK (words[i]?.getD 0)
    let pointOk := arithmeticAll (fun claim : Claim =>
      let value := countedDot packed claim.weight
      (value.1 == claim.value, value.2)) prepared.pointClaims.toList
    let anchor := countedDot packed prepared.anchorTable
    (pointOk.1 && (anchor.1 == anchorValue), checkWork c lanes m points.size (familyOk.2 + pointOk.2 + anchor.2))

/-- Source square-and-multiply depth: six shifts32,16,8,4,2,1, plus one scale and one add in each stage. -/
def mapField : Nat := ((List.finRange 6).map fun j => 2 ^ (5 - j.val) + 2).sum

theorem mapField_eq : mapField = 75 := by decide

def transformationField (c : Config) (m : Nat) : Nat :=
  m + 2 ^ c.logN * m * (mapField + 2) + 64 * (2 * m + mapField + 2)

def transformationWork (c : Config) (m points : Nat) : Work :=
  let size := 2 ^ c.logN
  { fieldArithmetic := transformationField c m
    lookups := 2 * m * size + 2 * m * 64 + points + 6 + 64
    iterations := m + m * size * (mapField + 2) + 64 * (2 * m + mapField + 2) + points + 2
    slots := size + m + points + 2 }

def countedInput {c : Config} {lanes m : Nat} {family : Fin m → FamilyClaim}
    {points : Array PointClaim} {anchorPoint : Array E} {anchorValue : E}
    (prepared : Prepared c lanes m family points anchorPoint anchorValue) (root : BaseOracle)
    (publicPrefix : Prefix) : Public × Work :=
  (input prepared root publicPrefix, transformationWork c m points.size)

theorem countedInput_value {c : Config} {lanes m : Nat} {family : Fin m → FamilyClaim}
    {points : Array PointClaim} {anchorPoint : Array E} {anchorValue : E}
    (prepared : Prepared c lanes m family points anchorPoint anchorValue) (root : BaseOracle)
    (publicPrefix : Prefix) : (countedInput prepared root publicPrefix).1 = input prepared root publicPrefix := rfl

end Whir.OriginalClaimsChecker
