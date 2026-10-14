import Whir.CountedCandidateCheckOriginalAnchor
import Whir.BatchingRefinement

/-! The actual original-claim checker caches immutable input weights once and materializes the witness once per check. Original family bit slices, all ordinary and strided point claims, and the literal saved anchor are checked separately before an output can be returned. Public finite functions are input-table reads, not an allowance for arbitrary external evaluation time. -/
namespace Whir.OriginalClaimsChecker
open Concrete Protocol CausalGame RingPCSGame CountedCandidateCheck
open scoped BigOperators

set_option maxHeartbeats 4000000

def pointGuard (dimension occupied : Nat) : PointClaim → Prop
  | .point offset point _ => point.size ≤ dimension ∧ offset % 2 ^ point.size = 0 ∧
      offset + 2 ^ point.size ≤ occupied
  | .strided offset slot stride point _ => stride + point.size ≤ dimension ∧
      slot < 2 ^ stride ∧ offset % 2 ^ (stride + point.size) = 0 ∧
      offset + 2 ^ (stride + point.size) ≤ occupied

instance (dimension occupied : Nat) (point : PointClaim) : Decidable (pointGuard dimension occupied point) := by
  cases point <;> unfold pointGuard <;> infer_instance

def Guards (c : Config) (lanes : Nat) {m : Nat} (family : Fin m → FamilyClaim)
    (points : Array PointClaim) (anchorPoint : Array E) : Prop :=
  c.folds[0]! ≤ c.logN ∧ c.logN ≤ 64 ∧ 0 < lanes ∧ lanes ≤ 2 ^ c.folds[0]! ∧
    anchorPoint.size = c.logN ∧
    (∀ j, (family j).point.size ≤ c.logN ∧
      (family j).offset % 2 ^ (family j).point.size = 0 ∧
      (family j).offset + 2 ^ (family j).point.size ≤ lanes * 2 ^ (c.logN - c.folds[0]!)) ∧
    ∀ i : Fin points.size, pointGuard c.logN (lanes * 2 ^ (c.logN - c.folds[0]!)) points[i]

instance (c : Config) (lanes : Nat) {m : Nat} (family : Fin m → FamilyClaim)
    (points : Array PointClaim) (anchorPoint : Array E) : Decidable (Guards c lanes family points anchorPoint) := by
  unfold Guards
  infer_instance

structure Prepared (c : Config) (lanes m : Nat) (family : Fin m → FamilyClaim)
    (points : Array PointClaim) (anchorPoint : Array E) (anchorValue : E) where
  guards : Guards c lanes family points anchorPoint
  familyWeights : Array (Array E)
  familyWeights_eq : familyWeights = Array.ofFn (fun j : Fin m =>
    tab (2 ^ c.logN) (regionWeight (family j).offset (family j).point))
  familyTargets : Array (Array E)
  familyTargets_eq : familyTargets = Array.ofFn (fun j : Fin m => Array.ofFn (family j).slices)
  pointClaims : Array Claim
  pointClaims_eq : pointClaims = points.map (publicPoint (2 ^ c.logN))
  anchorTable : Array E
  anchorTable_eq : anchorTable = eqTable anchorPoint
  anchorClaim : Claim
  anchorClaim_eq : anchorClaim = ⟨CommitmentAnchor.weight c lanes anchorPoint, anchorValue⟩
  basisCache : Array E
  basisCache_eq : basisCache = powers (E.ofK 2) 64

def prepare (c : Config) (lanes : Nat) {m : Nat} (family : Fin m → FamilyClaim)
    (points : Array PointClaim) (anchorPoint : Array E) (anchorValue : E) :
    Option (Prepared c lanes m family points anchorPoint anchorValue) :=
  if valid : Guards c lanes family points anchorPoint then
    let anchorTable := eqTable anchorPoint
    let anchorWeight := tab (2 ^ c.logN) fun i =>
      if i < lanes * 2 ^ (c.logN - c.folds[0]!) then anchorTable[i]! else 0
    some {
      guards := valid
      familyWeights := Array.ofFn (fun j : Fin m =>
        let claim := family j
        tab (2 ^ c.logN) (regionWeight claim.offset claim.point))
      familyWeights_eq := rfl
      familyTargets := Array.ofFn (fun j : Fin m => Array.ofFn (family j).slices)
      familyTargets_eq := rfl
      pointClaims := points.map (publicPoint (2 ^ c.logN))
      pointClaims_eq := rfl
      anchorTable := anchorTable
      anchorTable_eq := rfl
      anchorClaim := ⟨anchorWeight, anchorValue⟩
      anchorClaim_eq := rfl
      basisCache := powers (E.ofK 2) 64
      basisCache_eq := rfl }
  else none

/-- Tail recursion uses no per-bit coefficient array or repeated witness materialization. A zero bit skips its field addition. -/
def sliceLoop (words : Array K) (weights : Array E) (bit : Fin 64) : Nat → Nat → E → E
  | 0, _, value => value
  | fuel + 1, offset, value =>
    let next := if wordBit (words[offset]?.getD 0) bit then value + weights[offset]! else value
    sliceLoop words weights bit fuel (offset + 1) next

def slice (words : Array K) (weights : Array E) (bit : Fin 64) : E :=
  sliceLoop words weights bit weights.size 0 0

def check {c : Config} {lanes m : Nat} {family : Fin m → FamilyClaim}
    {points : Array PointClaim} {anchorPoint : Array E} {anchorValue : E}
    (prepared : Prepared c lanes m family points anchorPoint anchorValue) (w : Witness c lanes) : Bool :=
  let words := Array.ofFn w
  let familyOk := (List.finRange m).all fun j =>
    (List.finRange 64).all fun bit =>
      slice words prepared.familyWeights[j.val]! bit == (prepared.familyTargets[j.val]!)[bit.val]!
  if !familyOk then false else
    let packed := tab (2 ^ c.logN) fun i => E.ofK (words[i]?.getD 0)
    prepared.pointClaims.all (fun claim => dot packed claim.weight == claim.value) &&
      (dot packed prepared.anchorTable == anchorValue)

/-- Gamma powers and the six-stage additive map are shared by the family weight and target computations. Every gamma stays inside the additive map. -/
def input {c : Config} {lanes m : Nat} {family : Fin m → FamilyClaim}
    {points : Array PointClaim} {anchorPoint : Array E} {anchorValue : E}
    (prepared : Prepared c lanes m family points anchorPoint anchorValue) (root : BaseOracle)
    (publicPrefix : Prefix) : Public :=
  let scales := powers publicPrefix.1 m
  let phi := executableMap publicPrefix.2
  let members := List.finRange m
  let weight := tab (2 ^ c.logN) fun v =>
    members.foldl (fun value j => value +
      phi (scales[j.val]! * (prepared.familyWeights[j.val]!)[v]!)) 0
  let target := (List.finRange 64).foldl (fun value bit => value + prepared.basisCache[bit.val]! *
    phi (members.foldl (fun value j => value +
      scales[j.val]! * (prepared.familyTargets[j.val]!)[bit.val]!) 0)) 0
  ⟨c, lanes, root, (#[(⟨weight, target⟩ : Claim)] ++ prepared.pointClaims).push prepared.anchorClaim⟩

end Whir.OriginalClaimsChecker
