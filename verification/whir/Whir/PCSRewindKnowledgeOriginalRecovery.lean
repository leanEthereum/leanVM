import Whir.PCSRewindSourceRelation
import Whir.PCSRewindKnowledgeOriginalProbability

/-! Outside the actual fixed-root compression escape, a generic recovered
candidate passes the actual original-family checker, not a compressed proxy. -/
namespace Whir.PCSRewindSource
open Concrete Protocol CausalGame KnowledgeExtraction OriginalClaimsChecker
open PCSRewindExtractor

set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
attribute [local irreducible] ParameterBounds.config

 theorem input_checked_of_explains {c : Config} {lanes m : Nat}
    {family : Fin m → RingPCSGame.FamilyClaim} {points : Array RingPCSGame.PointClaim}
    {anchorPoint : Array E} {anchorValue : E}
    (prepared : Prepared c lanes m family points anchorPoint anchorValue)
    (root : BaseOracle) (r : RingPCSGame.Prefix) (w : Witness c lanes)
    (outside : ¬ RingPCSGame.Escape c lanes root family r)
    (explains : Explains (OriginalClaimsChecker.input prepared root r) w) :
    OriginalClaimsChecker.check prepared w = true := by
  classical
  have allTruth : ∀ claim ∈ ((RingPCSGame.transformedClaims (2 ^ c.logN) family points r).push
      ⟨CommitmentAnchor.weight c lanes anchorPoint, anchorValue⟩).toList,
      dot (paddedWitness c lanes w) claim.weight = claim.value := by
    rw [← input_claims prepared root r]
    exact explains.2
  have oldTruth : ∀ claim ∈ (RingPCSGame.transformedClaims (2 ^ c.logN) family points r).toList,
      dot (paddedWitness c lanes w) claim.weight = claim.value := by
    intro claim member
    apply allTruth claim
    simp only [Array.toList_push, List.mem_append]
    exact Or.inl member
  have compressed := oldTruth (RingPCSGame.familyPublic (2 ^ c.logN) family r)
    (by simp [RingPCSGame.transformedClaims])
  rw [RingPCSGame.dot_family] at compressed
  have slices : (fun j => (family j).slices) = RingPCSGame.honestSlices c lanes family w := by
    by_contra different
    exact outside ⟨w, explains.1, different, compressed.symm⟩
  apply (check_iff prepared w).mpr
  refine ⟨⟨slices, ?_⟩, ?_⟩
  · intro point member
    apply oldTruth (RingPCSGame.publicPoint (2 ^ c.logN) point)
    simp only [RingPCSGame.transformedClaims, Array.toList_append, Array.toList_map,
      List.mem_append, List.mem_map]
    exact Or.inr ⟨point, member, rfl⟩
  · have anchor := allTruth
      (⟨CommitmentAnchor.weight c lanes anchorPoint, anchorValue⟩ : Claim)
      (by simp)
    rw [CommitmentAnchor.weight_value c lanes w anchorPoint prepared.guards.2.2.2.2.1] at anchor
    exact anchor

 theorem runOne_recovers_generic {m : Nat} (profile : ParameterBounds.Profile) (rounds lanes : Nat)
    (family : Fin m → RingPCSGame.FamilyClaim) (points : Array RingPCSGame.PointClaim)
    (anchorPoint : Array E) (anchorValue : E)
    (prepared : Prepared (ParameterBounds.config profile) lanes m family points anchorPoint anchorValue)
    (root : BaseOracle) (strategy : RingPCSGame.Prefix → Strategy) (seed : Seed profile rounds)
    (outside : ¬ RingPCSGame.Escape (ParameterBounds.config profile) lanes root family seed.1)
    (w : Witness (ParameterBounds.config profile) lanes)
    (output : (runRewind (OriginalClaimsChecker.input prepared root seed.1) (strategy seed.1)
      (extractor profile rounds).maxReplay (extractor profile rounds).rewindRounds
      ((extractor profile rounds).program (OriginalClaimsChecker.input prepared root seed.1) seed.2)).output = some w) :
    (runOne profile rounds lanes family points anchorPoint anchorValue prepared root strategy seed).output = some w := by
  let claims := (OriginalClaimsChecker.input prepared root seed.1).claims
  change (runRewind (ExecutionShapes.Input profile lanes root claims) (strategy seed.1)
    (extractor profile rounds).maxReplay (extractor profile rounds).rewindRounds
    ((extractor profile rounds).program (ExecutionShapes.Input profile lanes root claims) seed.2)).output = some w at output
  have explains : Explains (OriginalClaimsChecker.input prepared root seed.1) w := by
    change Explains (ExecutionShapes.Input profile lanes root claims) w
    exact extractor_output_explains profile rounds lanes root claims (strategy seed.1) seed.2
      prepared.guards.2.2.2.1 w output
  have checked := input_checked_of_explains prepared root seed.1 w outside explains
  rw [extractor_run] at output
  rw [runOne_value]
  dsimp only at output ⊢
  apply decodedWithFinal_recover (OriginalClaimsChecker.input prepared root seed.1) _ _ _ w
  · exact output
  · exact checked

#print axioms input_checked_of_explains
#print axioms runOne_recovers_generic
#check runOne_recovers_generic
end Whir.PCSRewindSource
