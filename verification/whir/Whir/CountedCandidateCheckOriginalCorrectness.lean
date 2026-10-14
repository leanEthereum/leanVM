import Whir.CountedCandidateCheckOriginal

/-! Correctness of the cached original checker and cached public transformation. These results quantify over every prepared immutable original statement and every candidate; no honest-root recomputation or compressed-family equality replaces original honesty. -/
namespace Whir.OriginalClaimsChecker
open Concrete Protocol CausalGame RingPCSGame CountedCandidateCheck
open scoped BigOperators

set_option maxHeartbeats 4000000

private theorem sliceLoop_eq (words : Array K) (weights : Array E) (bit : Fin 64)
    (fuel offset : Nat) (value : E) :
    sliceLoop words weights bit fuel offset value = value +
      ∑ j ∈ Finset.range fuel,
        if wordBit (words[offset + j]?.getD 0) bit then weights[offset + j]! else 0 := by
  induction fuel generalizing offset value with
  | zero => simp [sliceLoop]
  | succ fuel ih =>
    rw [sliceLoop, ih, Finset.sum_range_succ']
    by_cases h : wordBit (words[offset]?.getD 0) bit = true
    · simp [h, add_assoc, add_comm, add_left_comm]
    · simp [h, add_comm, add_left_comm]

theorem slice_eq (words : Array K) (weights : Array E) (bit : Fin 64) :
    slice words weights bit = RingSwitch.slice
      (fun v : Fin weights.size => weights[v.val]!)
      (fun i v => wordBit (words[v.val]?.getD 0) i) bit := by
  unfold slice RingSwitch.slice
  rw [sliceLoop_eq]
  simp only [zero_add]
  rw [Fin.sum_univ_eq_sum_range
    (fun v => RingSwitch.bit (wordBit (words[v]?.getD 0) bit) * weights[v]!) weights.size]
  apply Finset.sum_congr rfl
  intro v within
  cases h : wordBit (words[v]?.getD 0) bit <;> simp [RingSwitch.bit]

private theorem family_weight (c : Config) (lanes m : Nat) (family : Fin m → FamilyClaim)
    (points : Array PointClaim) (anchorPoint : Array E) (anchorValue : E)
    (prepared : Prepared c lanes m family points anchorPoint anchorValue) (j : Fin m) :
    prepared.familyWeights[j.val]! = tab (2 ^ c.logN) (regionWeight (family j).offset (family j).point) := by
  rw [prepared.familyWeights_eq]
  simp [getElem!_pos, j.isLt]

private theorem family_target (c : Config) (lanes m : Nat) (family : Fin m → FamilyClaim)
    (points : Array PointClaim) (anchorPoint : Array E) (anchorValue : E)
    (prepared : Prepared c lanes m family points anchorPoint anchorValue) (j : Fin m) (bit : Fin 64) :
    (prepared.familyTargets[j.val]!)[bit.val]! = (family j).slices bit := by
  rw [prepared.familyTargets_eq]
  simp [getElem!_pos, j.isLt, bit.isLt]

private theorem family_slice (c : Config) (lanes m : Nat) (family : Fin m → FamilyClaim)
    (points : Array PointClaim) (anchorPoint : Array E) (anchorValue : E)
    (prepared : Prepared c lanes m family points anchorPoint anchorValue)
    (w : Witness c lanes) (j : Fin m) (bit : Fin 64) :
    slice (Array.ofFn w) prepared.familyWeights[j.val]! bit = honestSlices c lanes family w j bit := by
  rw [family_weight]
  unfold slice honestSlices RingSwitch.slice paddedWord
  rw [sliceLoop_eq]
  simp only [ArrayLayout.size_tab, zero_add]
  rw [Fin.sum_univ_eq_sum_range (fun v =>
    RingSwitch.bit (wordBit ((Array.ofFn w)[v]?.getD 0) bit) *
      regionWeight (family j).offset (family j).point v) (2 ^ c.logN)]
  apply Finset.sum_congr rfl
  intro v within
  rw [ArrayLayout.getElem!_tab _ _ _ (Finset.mem_range.mp within)]
  cases h : wordBit ((Array.ofFn w)[v]?.getD 0) bit <;> simp [RingSwitch.bit]

/-- Some preparation is possible exactly when the literal source metadata guards hold. -/
theorem prepare_some_iff (c : Config) (lanes : Nat) {m : Nat} (family : Fin m → FamilyClaim)
    (points : Array PointClaim) (anchorPoint : Array E) (anchorValue : E) :
    (prepare c lanes family points anchorPoint anchorValue).isSome = true ↔
      Guards c lanes family points anchorPoint := by
  unfold prepare
  split <;> simp_all

/-- This is original honesty, including every one of the64 bit slices per original family, every point value, and the same saved anchor. -/
theorem check_iff {c : Config} {lanes m : Nat} {family : Fin m → FamilyClaim}
    {points : Array PointClaim} {anchorPoint : Array E} {anchorValue : E}
    (prepared : Prepared c lanes m family points anchorPoint anchorValue) (w : Witness c lanes) :
    check prepared w = true ↔ Honest c lanes family points w ∧
      CommitmentAnchor.value c lanes w anchorPoint = anchorValue := by
  have familyCheck : ((List.finRange m).all fun j => (List.finRange 64).all fun bit =>
      slice (Array.ofFn w) prepared.familyWeights[j.val]! bit ==
        (prepared.familyTargets[j.val]!)[bit.val]!) = true ↔
      (fun j => (family j).slices) = honestSlices c lanes family w := by
    simp only [List.all_eq_true, List.mem_finRange, forall_true_left, beq_iff_eq,
      family_slice, family_target]
    exact ⟨fun h => funext (fun j => funext (fun bit => (h j bit).symm)),
      fun h j bit => (congrFun (congrFun h j) bit).symm⟩
  have pointsCheck : prepared.pointClaims.all
      (fun claim => dot (paddedWitness c lanes w) claim.weight == claim.value) = true ↔
      ∀ point ∈ points.toList,
        dot (paddedWitness c lanes w) (publicPoint (2 ^ c.logN) point).weight = pointValue point := by
    rw [prepared.pointClaims_eq, Array.all_eq_true]
    simp only [Array.size_map, Array.getElem_map, publicPoint, beq_iff_eq]
    constructor
    · intro h point member
      obtain ⟨i, within, rfl⟩ := Array.mem_iff_getElem.mp (Array.mem_toList_iff.mp member)
      exact h i within
    · intro h i within
      exact h _ (Array.getElem_mem_toList within)
  unfold check
  dsimp only
  change (if !((List.finRange m).all fun j => (List.finRange 64).all fun bit =>
    slice (Array.ofFn w) prepared.familyWeights[j.val]! bit ==
      (prepared.familyTargets[j.val]!)[bit.val]!) then false else
    prepared.pointClaims.all (fun claim => dot (paddedWitness c lanes w) claim.weight == claim.value) &&
      (dot (paddedWitness c lanes w) prepared.anchorTable == anchorValue)) = true ↔ _
  rw [prepared.anchorTable_eq]
  change (if !((List.finRange m).all fun j => (List.finRange 64).all fun bit =>
    slice (Array.ofFn w) prepared.familyWeights[j.val]! bit ==
      (prepared.familyTargets[j.val]!)[bit.val]!) then false else
    prepared.pointClaims.all (fun claim => dot (paddedWitness c lanes w) claim.weight == claim.value) &&
      (CommitmentAnchor.value c lanes w anchorPoint == anchorValue)) = true ↔ _
  by_cases f : ((List.finRange m).all fun j => (List.finRange 64).all fun bit =>
    slice (Array.ofFn w) prepared.familyWeights[j.val]! bit ==
      (prepared.familyTargets[j.val]!)[bit.val]!) = true
  · have hf := familyCheck.mp f
    simp [f, hf, Honest, Bool.and_eq_true, beq_iff_eq, pointsCheck]
  · have hf : (fun j => (family j).slices) ≠ honestSlices c lanes family w := by
      intro h
      exact f (familyCheck.mpr h)
    simp [f, hf, Honest]

/-- The cached transformation is exactly the source family-first stack with the original anchor appended at its original final position. -/
theorem input_claims {c : Config} {lanes m : Nat} {family : Fin m → FamilyClaim}
    {points : Array PointClaim} {anchorPoint : Array E} {anchorValue : E}
    (prepared : Prepared c lanes m family points anchorPoint anchorValue)
    (root : BaseOracle) (publicPrefix : Prefix) :
    (input prepared root publicPrefix).claims =
      (transformedClaims (2 ^ c.logN) family points publicPrefix).push
        ⟨CommitmentAnchor.weight c lanes anchorPoint, anchorValue⟩ := by
  have familyWeights : ∀ j : Fin m, prepared.familyWeights[j.val]! =
      tab (2 ^ c.logN) (regionWeight (family j).offset (family j).point) := family_weight _ _ _ _ _ _ _ prepared
  have targets : ∀ j : Fin m, ∀ bit : Fin 64,
      (prepared.familyTargets[j.val]!)[bit.val]! = (family j).slices bit := family_target _ _ _ _ _ _ _ prepared
  have cache : ∀ bit : Fin 64, prepared.basisCache[bit.val]! = basis bit := by
    intro bit
    rw [prepared.basisCache_eq, BatchingRefinement.get_powers _ _ _ bit.isLt]
    rfl
  unfold input transformedClaims familyPublic familyTarget RingSwitch.familyTarget transparentWeight
  dsimp only
  rw [prepared.pointClaims_eq, prepared.anchorClaim_eq]
  congr 3
  apply congrArg (fun claim : Claim => [claim])
  congr 1
  · apply Array.ext
    · simp [ArrayLayout.size_tab]
    · intro v hv _
      have within : v < 2 ^ c.logN := by simpa using hv
      rw [ArrayLayout.getElem_tab _ _ _ within, ArrayLayout.getElem_tab _ _ _ within]
      simp only [Fin.sum_univ_def, List.sum_eq_foldl, List.foldl_map]
      apply congrArg (fun f => (List.finRange m).foldl f (0 : E))
      funext value j
      rw [BatchingRefinement.get_powers _ _ _ j.isLt, familyWeights j,
        ArrayLayout.getElem!_tab _ _ _ within]
  · simp only [Fin.sum_univ_def, List.sum_eq_foldl, List.foldl_map]
    apply congrArg (fun f => (List.finRange 64).foldl f (0 : E))
    funext value bit
    rw [cache bit]
    congr 2
    apply congrArg (executableMap publicPrefix.2)
    apply congrArg (fun f => (List.finRange m).foldl f (0 : E))
    funext value j
    rw [BatchingRefinement.get_powers _ _ _ j.isLt, targets j bit]

#print axioms check_iff
#print axioms input_claims

end Whir.OriginalClaimsChecker
