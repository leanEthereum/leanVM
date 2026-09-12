import SphincsSecurity.Proof.Ots.OtsTwoEdgeSource
namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] canonicalGraphLabels canonicalEncodingInputs canonicalGraphInputs instFintypePosition Finset.univ

theorem referenceContactGame_twoEdge_law (inputs : Finset HashInput)
    (hencoding : ∀ parameter, canonicalEncodingInputs parameter ⊆ inputs) (hgraph : ∀ parameter, canonicalGraphInputs parameter ⊆ inputs)
    (address : OtsPrefix.ChainAddress) (dummy : OtsReferenceWords) (adversary : Adversary) :
    (fun result => decide (result.2.2.TwoEdgeAt result.1 (referenceFamilyWords result.2.1 dummy) address)) <$>
      referenceContactGame inputs hencoding dummy adversary = prefixTwoEdgeGame inputs hencoding hgraph address dummy adversary := by
  rw [← prefixContactObservedGame_original inputs hencoding hgraph address dummy adversary]
  unfold prefixContactObservedGame prefixInstrumentedObservedGame prefixTwoEdgeGame
  simp only [map_bind, map_pure]
  apply congrArg (𝒟[sampleParameter] >>= ·)
  funext parameter
  apply congrArg (𝒟[sampleFtsSecrets] >>= ·)
  funext ftsSecret
  apply congrArg (𝒟[FirstSuccessFamily.selected decodeEncodingOutput encodingAttemptLimit] >>= ·)
  funext selections
  let words := referenceFamilyWords selections dummy
  let segment := OtsPrefix.atAddress parameter words address
  apply congrArg (𝒟[PMF.uniformOfFintype segment.ErasedSecrets] >>= ·)
  funext other
  apply congrArg (𝒟[segment.referenceAuxSeedLaw inputs (hencoding parameter) (hgraph parameter) selections] >>= ·)
  funext auxiliary
  have h := congrArg (fun law : PMF Bool => 𝒟[law])
    (contactSeed_twoEdge_eq parameter words address inputs (hencoding parameter) (hgraph parameter) auxiliary other.val ftsSecret adversary)
  simpa only [← PMF.monad_map_eq_map, evalDist_map, bind_map_left, bind_pure_comp, Functor.map_map, Function.comp_def] using h

theorem referenceContactGame_twoEdge_eq (inputs : Finset HashInput)
    (hencoding : ∀ parameter, canonicalEncodingInputs parameter ⊆ inputs) (hgraph : ∀ parameter, canonicalGraphInputs parameter ⊆ inputs)
    (address : OtsPrefix.ChainAddress) (dummy : OtsReferenceWords) (adversary : Adversary) :
    Pr[fun result => result.2.2.TwoEdgeAt result.1 (referenceFamilyWords result.2.1 dummy) address |
      referenceContactGame inputs hencoding dummy adversary] =
    Pr[= true | prefixTwoEdgeGame inputs hencoding hgraph address dummy adversary] := by
  rw [← referenceContactGame_twoEdge_law inputs hencoding hgraph address dummy adversary, ← probEvent_eq_eq_probOutput, probEvent_map]
  simp only [Function.comp_def, decide_eq_true_eq]

def ContactResult.TwoEdge (parameter : PublicParameter) (words : OtsReferenceWords) (result : ContactResult) : Prop :=
  ∃ address, result.TwoEdgeAt parameter words address

theorem referenceContactGame_twoEdge_le_sum (inputs : Finset HashInput)
    (hencoding : ∀ parameter, canonicalEncodingInputs parameter ⊆ inputs) (dummy : OtsReferenceWords) (adversary : Adversary) :
    Pr[fun result => result.2.2.TwoEdge result.1 (referenceFamilyWords result.2.1 dummy) |
      referenceContactGame inputs hencoding dummy adversary] ≤
      ∑ address : OtsPrefix.ChainAddress, Pr[fun result => result.2.2.TwoEdgeAt result.1 (referenceFamilyWords result.2.1 dummy) address |
        referenceContactGame inputs hencoding dummy adversary] := by
  let law := referenceContactGame inputs hencoding dummy adversary
  let event := fun address : OtsPrefix.ChainAddress => fun result : InstrumentedResult ContactResult =>
    result.2.2.TwoEdgeAt result.1 (referenceFamilyWords result.2.1 dummy) address
  refine (_root_.probEvent_mono (mx := law) (q := fun result => ∃ address ∈ (Finset.univ : Finset OtsPrefix.ChainAddress), event address result) ?_).trans
    (probEvent_exists_finset_le_sum Finset.univ law event)
  rintro result _ ⟨address, ha⟩
  exact ⟨address, Finset.mem_univ address, ha⟩

theorem referenceContactGame_twoEdge_sum_cost_le (dummy : OtsReferenceWords) (adversary : Adversary) (q : Nat)
    (hbound : HasHashQueryBound scheme adversary q) (hsmall : q < Fintype.card Digest) :
    (1 - (q : ENNReal) / Fintype.card Digest) *
      (∑ address : OtsPrefix.ChainAddress, Pr[fun result => result.2.2.TwoEdgeAt result.1 (referenceFamilyWords result.2.1 dummy) address |
        referenceContactGame (canonicalGraphGameInputs adversary) (canonicalEncodingInputs_subset_gameInputs adversary) dummy adversary]) ≤
      prefixTwoEdgeRate q * (∑' result : ReferenceRecordedResult, Pr[= result | referenceRecordedGame (canonicalGraphGameInputs adversary)
        (canonicalEncodingInputs_subset_gameInputs adversary) dummy adversary] * (result.prefixCalls dummy : ENNReal)) := by
  simp only [referenceContactGame_twoEdge_eq _ _ (canonicalGraphInputs_subset_gameInputs adversary)]
  have hsum := Finset.sum_le_sum (s := (Finset.univ : Finset OtsPrefix.ChainAddress))
    fun address _ => prefixTwoEdgeGame_le address dummy adversary q hbound hsmall
  rw [← Finset.mul_sum] at hsum
  have hlower := Finset.sum_le_sum (s := (Finset.univ : Finset OtsPrefix.ChainAddress))
    fun address _ => prefixIdealCostGame_lower address dummy adversary q hbound
  rw [← Finset.mul_sum] at hlower
  simp only [prefixCountedObservedGame_original, tsum_probOutput_map_mul, ReferenceRecordedResult.prefixCounted] at hlower
  conv at hlower =>
    rhs
    rw [← tsum_fintype (L := SummationFilter.unconditional OtsPrefix.ChainAddress), ENNReal.tsum_comm]
    simp only [tsum_fintype, ← Finset.mul_sum, ← Nat.cast_sum]
  have hscaled := mul_le_mul' (le_refl (1 - (q : ENNReal) / Fintype.card Digest)) hsum
  rw [mul_left_comm] at hscaled
  exact hscaled.trans (mul_le_mul' le_rfl hlower)

theorem referenceContactGame_twoEdge_cost_le (dummy : OtsReferenceWords) (adversary : Adversary) (q : Nat)
    (hbound : HasHashQueryBound scheme adversary q) (hsmall : q < Fintype.card Digest) :
    (1 - (q : ENNReal) / Fintype.card Digest) *
      Pr[fun result => result.2.2.TwoEdge result.1 (referenceFamilyWords result.2.1 dummy) |
        referenceContactGame (canonicalGraphGameInputs adversary) (canonicalEncodingInputs_subset_gameInputs adversary) dummy adversary] ≤
      prefixTwoEdgeRate q * (∑' result : ReferenceRecordedResult, Pr[= result | referenceRecordedGame (canonicalGraphGameInputs adversary)
        (canonicalEncodingInputs_subset_gameInputs adversary) dummy adversary] * (result.prefixCalls dummy : ENNReal)) :=
  (mul_le_mul' le_rfl (referenceContactGame_twoEdge_le_sum _ _ dummy adversary)).trans
    (referenceContactGame_twoEdge_sum_cost_le dummy adversary q hbound hsmall)

theorem referenceContactGame_twoEdge_le (dummy : OtsReferenceWords) (adversary : Adversary) (q : Nat)
    (hbound : HasHashQueryBound scheme adversary q) (hsmall : q < Fintype.card Digest) :
    Pr[fun result => result.2.2.TwoEdge result.1 (referenceFamilyWords result.2.1 dummy) |
      referenceContactGame (canonicalGraphGameInputs adversary) (canonicalEncodingInputs_subset_gameInputs adversary) dummy adversary] ≤
      (prefixTwoEdgeRate q * (∑' result : ReferenceRecordedResult, Pr[= result | referenceRecordedGame (canonicalGraphGameInputs adversary)
        (canonicalEncodingInputs_subset_gameInputs adversary) dummy adversary] * (result.prefixCalls dummy : ENNReal))) /
        (1 - (q : ENNReal) / Fintype.card Digest) := by
  have hcard : (Fintype.card Digest : ENNReal) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hpositive : 0 < 1 - (q : ENNReal) / Fintype.card Digest := by
    apply tsub_pos_iff_lt.mpr
    rw [ENNReal.div_lt_iff (Or.inl hcard) (Or.inl (by finiteness)), one_mul]
    exact_mod_cast hsmall
  apply (ENNReal.le_div_iff_mul_le (Or.inl (ne_of_gt hpositive)) (Or.inl (by finiteness))).mpr
  simpa only [mul_comm] using referenceContactGame_twoEdge_cost_le dummy adversary q hbound hsmall

end SphincsSecurity.Concrete
