import Whir.PCSRewindKnowledgeBound
import Whir.AnchorPrefixRefinementCaller

/-! Compressed-family dense-claims endpoint only. The actual transformed family
and ordinary point claims include the retained commitment anchor at its final
powers-batch position. A single public seed does not certify every original
FamilyClaim; that requires the separate joint-prefix original-source theorem. -/
namespace Whir.PCSRewindExtractor
open Concrete Protocol CausalGame KnowledgeExtraction SupportedCandidateExtraction
open SamplingProbability AuthenticatedResetProbability

private theorem anchored_claim_shapes {m : Nat} (c : Config) (record : AnchoredHeaderCodec.Record)
    (family : Fin m → RingPCSGame.FamilyClaim) (points : Array RingPCSGame.PointClaim)
    (seed : RingPCSGame.Prefix)
    (j : Fin (AnchorPrefixRefinement.anchoredClaims c record family points seed).size) :
    (AnchorPrefixRefinement.anchoredClaims c record family points seed)[j].weight.size = 2 ^ c.logN := by
  have all : ∀ claim ∈ (AnchorPrefixRefinement.anchoredClaims c record family points seed).toList,
      claim.weight.size = 2 ^ c.logN := by
    intro claim member
    simp only [AnchorPrefixRefinement.anchoredClaims, Array.toList_push, List.mem_append, List.mem_singleton] at member
    rcases member with old | rfl
    · obtain ⟨i, within, equal⟩ := Array.mem_iff_getElem.mp (Array.mem_toList_iff.mp old)
      rw [← equal]
      exact RingPCSGame.transformedClaims_shapes _ _ _ _ ⟨i, within⟩
    · simp [CommitmentAnchor.weight, ArrayLayout.size_tab]
  exact all _ (Array.mem_toList_iff.mpr (Array.getElem_mem j.isLt))

/-- Literal record validity and profile metadata derive the supported lane and
retained point dimensions; dense transformed weights have the actual dimension
and their exact size is ordinaryPoints.size+2. -/
theorem anchored_metadata_shapes {m : Nat} (profile : ParameterBounds.Profile)
    (record : AnchoredHeaderCodec.Record) (family : Fin m → RingPCSGame.FamilyClaim)
    (ordinaryPoints : Array RingPCSGame.PointClaim) (publicSeed : RingPCSGame.Prefix)
    (valid : record.Valid)
    (batchShape : record.shape.logBatch = (ParameterBounds.config profile).folds[0]!)
    (dimensionShape : record.shape.logN = (ParameterBounds.config profile).logN) :
    record.shape.lanes ≤ laneCount (ParameterBounds.config profile) ∧
    record.point.length = (ParameterBounds.config profile).logN ∧
    (AnchorPrefixRefinement.anchoredClaims (ParameterBounds.config profile)
      record family ordinaryPoints publicSeed).size = ordinaryPoints.size + 2 ∧
    ∀ j : Fin (AnchorPrefixRefinement.anchoredClaims (ParameterBounds.config profile)
      record family ordinaryPoints publicSeed).size,
      (AnchorPrefixRefinement.anchoredClaims (ParameterBounds.config profile)
        record family ordinaryPoints publicSeed)[j].weight.size = 2 ^ (ParameterBounds.config profile).logN := by
  refine ⟨?_, valid.2.2.trans dimensionShape, ?_, anchored_claim_shapes _ _ _ _ _⟩
  · simpa only [batchShape] using valid.1.2.2.2.2.2
  · simp only [AnchorPrefixRefinement.anchoredClaims, Array.size_push, RingPCSGame.transformedClaims_size]
    omega

/-- Compressed-family dense claims only: the actual source caller's appended
anchor is included, but one seed does not uncompress every FamilyClaim. -/
theorem anchored_production_knowledge_bound {m : Nat} (profile : ParameterBounds.Profile)
    (record : AnchoredHeaderCodec.Record) (root : BaseOracle)
    (family : Fin m → RingPCSGame.FamilyClaim) (points : Array RingPCSGame.PointClaim)
    (seed : RingPCSGame.Prefix) (strategy : Strategy)
    (valid : record.Valid)
    (batchShape : record.shape.logBatch = (ParameterBounds.config profile).folds[0]!)
    (dimensionShape : record.shape.logN = (ParameterBounds.config profile).logN)
    (pointCap : points.size + 2 ≤ 2 ^ 64)
    (security : Nat) :
    let claims := AnchorPrefixRefinement.anchoredClaims (ParameterBounds.config profile) record family points seed
    let κ := probability (fun tape => experiment
      (ExecutionShapes.Input profile record.shape.lanes root claims) strategy tape = true)
    let gap := κ - (extractionCutoff : ℝ)
    KnowledgeBound profile (knowledgeAttempts gap security) (knowledgeRounds profile gap)
      record.shape.lanes root claims strategy (extractionCutoff + (1 / 2 : ℚ) ^ security) := by
  obtain ⟨laneBound, _pointShape, claimCount, claimShape⟩ :=
    anchored_metadata_shapes profile record family points seed valid batchShape dimensionShape
  have claimCap : (AnchorPrefixRefinement.anchoredClaims
      (ParameterBounds.config profile) record family points seed).size ≤ 2 ^ 64 := by
    rw [claimCount]
    exact pointCap
  exact production_universal_knowledge_bound profile record.shape.lanes root
    (AnchorPrefixRefinement.anchoredClaims (ParameterBounds.config profile) record family points seed)
    strategy laneBound claimShape claimCap security

/-- Any verified output explains the compressed-family dense claims and the
same retained anchor point/value. No conclusion about every original family
functional follows from this fixed-seed endpoint. -/
theorem anchored_extracted_output {m : Nat} (profile : ParameterBounds.Profile)
    (attempts rounds : Nat) (record : AnchoredHeaderCodec.Record) (root : BaseOracle)
    (family : Fin m → RingPCSGame.FamilyClaim) (points : Array RingPCSGame.PointClaim)
    (publicSeed : RingPCSGame.Prefix) (strategy : Strategy)
    (seed : RepeatedSeed profile attempts rounds)
    (valid : record.Valid)
    (batchShape : record.shape.logBatch = (ParameterBounds.config profile).folds[0]!)
    (dimensionShape : record.shape.logN = (ParameterBounds.config profile).logN)
    (w : Witness (ParameterBounds.config profile) record.shape.lanes)
    (output :
      let claims := AnchorPrefixRefinement.anchoredClaims (ParameterBounds.config profile) record family points publicSeed
      let input := ExecutionShapes.Input profile record.shape.lanes root claims
      (runRewind input strategy (repeatedExtractor profile attempts rounds).maxReplay
        (repeatedExtractor profile attempts rounds).rewindRounds
        ((repeatedExtractor profile attempts rounds).program input seed)).output = some w) :
    Explains (ExecutionShapes.Input profile record.shape.lanes root
      (AnchorPrefixRefinement.anchoredClaims (ParameterBounds.config profile) record family points publicSeed)) w ∧
    CommitmentAnchor.value (ParameterBounds.config profile) record.shape.lanes w record.point.toArray = record.value := by
  have laneBound : record.shape.lanes ≤ laneCount (ParameterBounds.config profile) := by
    simpa only [batchShape] using valid.1.2.2.2.2.2
  have pointShape : record.point.length = (ParameterBounds.config profile).logN :=
    valid.2.2.trans dimensionShape
  let claims := AnchorPrefixRefinement.anchoredClaims (ParameterBounds.config profile) record family points publicSeed
  have explains := repeatedExtractor_output_explains profile attempts rounds record.shape.lanes root claims
    strategy seed laneBound w output
  refine ⟨explains, ?_⟩
  have original : (⟨CommitmentAnchor.weight (ParameterBounds.config profile) record.shape.lanes record.point.toArray,
      record.value⟩ : Claim) ∈ claims.toList := by
    simp [claims, AnchorPrefixRefinement.anchoredClaims]
  have same := explains.2 _ original
  rw [CommitmentAnchor.weight_value _ _ _ _ (by simpa using pointShape)] at same
  exact same

/-- The actual retained anchor occupies the unchanged final batching power,
lambda^(ordinaryPoints.size+1), in both the weight and claimed value. -/
theorem anchored_retained_batch {m : Nat} (c : Config) (record : AnchoredHeaderCodec.Record)
    (family : Fin m → RingPCSGame.FamilyClaim) (ordinaryPoints : Array RingPCSGame.PointClaim)
    (publicSeed : RingPCSGame.Prefix) (lambda : E) :
    batchClaims (2 ^ c.logN)
        (AnchorPrefixRefinement.anchoredClaims c record family ordinaryPoints publicSeed) lambda =
      ⟨weightGlue
        (batchClaims (2 ^ c.logN)
          (RingPCSGame.transformedClaims (2 ^ c.logN) family ordinaryPoints publicSeed) lambda).weight
        (CommitmentAnchor.weight c record.shape.lanes record.point.toArray)
        (lambda ^ (ordinaryPoints.size + 1)),
      WHIRNativeArithmetic.initialClaim family ordinaryPoints publicSeed lambda +
        lambda ^ (ordinaryPoints.size + 1) * record.value⟩ := by
  rw [AnchorPrefixRefinement.anchoredClaims, AnchorPrefixRefinement.batchClaims_push]
  simp only [RingPCSGame.transformedClaims_size]
  rw [← WHIRNativeArithmetic.initialClaim_eq_batch_value]
  simp only [Nat.add_comm 1 ordinaryPoints.size]

#print axioms anchored_production_knowledge_bound
#print axioms anchored_extracted_output
#print axioms anchored_retained_batch
#print axioms anchored_metadata_shapes
#check anchored_production_knowledge_bound
#check anchored_extracted_output
#check anchored_retained_batch
#check anchored_metadata_shapes
end Whir.PCSRewindExtractor
