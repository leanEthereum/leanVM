import Whir.AnchorPrefixRefinement

/-! Field-operation accounting for the very same source recurrence. A fused `mul_add` costs one multiplication and one addition. Constants, register copies, and Boolean branching are not field operations. This is not a machine-time or recursive-row-count model. -/
namespace Whir.AnchorPrefixRefinementCost
open Concrete AnchoredHeaderCodec AnchoredPhysicalAnchor

/-- Exact source branch charge: two additions build the factor; occupied branches build hi and lo; only higher nonzero count bits update full. -/
def stepCharge (shape : Shape) (j : Nat) (started : Bool) : Nat :=
  2 + (if shape.lanes.testBit j || started then
    2 + (if shape.lanes.testBit j then
      (if j = 0 then 0 else 1) + (if started then 2 else 0)
      else 1)
    else 0) +
    (if shape.lanes >>> (j+1) ≠ 0 then if j = 0 then 0 else 1 else 0)

def countedStep (shape : Shape) (r x : Array E) (j : Nat) (s : PrefixState × Nat) : PrefixState × Nat :=
  (prefixStep shape r x j s.1, s.2+stepCharge shape j s.1.started)

lemma stepCharge_bound (shape : Shape) (j : Nat) (started : Bool) : stepCharge shape j started ≤ 8 := by
  unfold stepCharge
  split_ifs <;> omega

lemma counted_fold (shape : Shape) (r x : Array E) (l : List Nat) (s : PrefixState × Nat) :
    (l.foldl (fun s j => countedStep shape r x j s) s).1 =
      l.foldl (fun s j => prefixStep shape r x j s) s.1 ∧
    (l.foldl (fun s j => countedStep shape r x j s) s).2 ≤ s.2+8*l.length := by
  induction l generalizing s with
  | nil => simp
  | cons j l ih =>
    have h := ih (countedStep shape r x j s)
    constructor
    · simpa only [List.foldl_cons, countedStep] using h.1
    · have hc := stepCharge_bound shape j s.1.started
      simp only [List.foldl_cons, List.length_cons]
      apply le_trans h.2
      change s.2+stepCharge shape j s.1.started+8*l.length ≤ s.2+8*(l.length+1)
      omega

/-- Returning the source value and its own arithmetic charge, not a hypothetical dense-table backend charge. -/
def countedAnchorAt (shape : Shape) (r x : Array E) : E × Nat :=
  if shape.lanes = 2^shape.logBatch then (anchorAt shape r x,3*r.size)
  else
    let result := (List.range shape.logBatch).foldl
      (fun s j => countedStep shape r x j s) ({},0)
    (AnchorPrefixRefinementArith.native.mul
      (AnchorPrefixRefinementArith.eqEvalWith AnchorPrefixRefinementArith.native
        (shape.logN-shape.logBatch) (fun i => r[i]!) (fun i => x[i]!)) result.1.partial,
      3*(shape.logN-shape.logBatch)+result.2+1)

lemma countedAnchorAt_value (shape : Shape) (r x : Array E) :
    (countedAnchorAt shape r x).1 = anchorAt shape r x := by
  have hv := (counted_fold shape r x (List.range shape.logBatch) ({},0)).1
  unfold countedAnchorAt anchorAt AnchorPrefixRefinementArith.anchorAtWith
  split_ifs
  · rfl
  · dsimp only
    rw [hv]
    rfl

/-- Linear source arithmetic bound, including the full-cube fast branch and all low coordinates. The high-coordinate DP never allocates or evaluates an intermediate cube. -/
theorem countedAnchorAt_bound (shape : Shape) (r x : Array E) (hr : r.size = shape.logN) :
    (countedAnchorAt shape r x).2 ≤ 3*shape.logN+8*shape.logBatch+1 := by
  have hb := (counted_fold shape r x (List.range shape.logBatch) ({},0)).2
  simp only [List.length_range, Nat.zero_add] at hb
  unfold countedAnchorAt
  split_ifs
  · simp only [hr]; omega
  · simp only
    have hs : shape.logN-shape.logBatch ≤ shape.logN := Nat.sub_le _ _
    omega

#print axioms countedAnchorAt_value
#print axioms countedAnchorAt_bound
end Whir.AnchorPrefixRefinementCost
