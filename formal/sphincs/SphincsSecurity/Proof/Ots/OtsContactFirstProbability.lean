import SphincsSecurity.Proof.Ots.OtsContactFirstLaw
namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] canonicalGraphLabels canonicalEncodingInputs canonicalGraphInputs instFintypePosition OtsContactTrace.contacts Finset.univ

theorem referenceContactGame_contacted_law (inputs : Finset HashInput)
    (hencoding : ∀ parameter, canonicalEncodingInputs parameter ⊆ inputs) (hgraph : ∀ parameter, canonicalGraphInputs parameter ⊆ inputs)
    (address : OtsPrefix.ChainAddress) (dummy : OtsReferenceWords) (adversary : Adversary) :
    (fun result => decide (result.2.2.Contacted result.1 (referenceFamilyWords result.2.1 dummy) address)) <$>
      referenceContactGame inputs hencoding dummy adversary = prefixContactGame inputs hencoding hgraph address dummy adversary := by
  rw [← prefixContactObservedGame_original inputs hencoding hgraph address dummy adversary]
  unfold prefixContactObservedGame prefixInstrumentedObservedGame prefixContactGame
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
    (contactSeed_contacted_eq parameter words address inputs (hencoding parameter) (hgraph parameter) auxiliary other.val ftsSecret adversary)
  simpa only [← PMF.monad_map_eq_map, evalDist_map, bind_map_left, bind_pure_comp, Functor.map_map, Function.comp_def] using h

theorem referenceContactGame_contacted_eq (inputs : Finset HashInput)
    (hencoding : ∀ parameter, canonicalEncodingInputs parameter ⊆ inputs) (hgraph : ∀ parameter, canonicalGraphInputs parameter ⊆ inputs)
    (address : OtsPrefix.ChainAddress) (dummy : OtsReferenceWords) (adversary : Adversary) :
    Pr[fun result => result.2.2.Contacted result.1 (referenceFamilyWords result.2.1 dummy) address |
      referenceContactGame inputs hencoding dummy adversary] =
    Pr[= true | prefixContactGame inputs hencoding hgraph address dummy adversary] := by
  rw [← referenceContactGame_contacted_law inputs hencoding hgraph address dummy adversary, ← probEvent_eq_eq_probOutput, probEvent_map]
  simp only [Function.comp_def, decide_eq_true_eq]

theorem referenceContactGame_marked_le_sum (inputs : Finset HashInput)
    (hencoding : ∀ parameter, canonicalEncodingInputs parameter ⊆ inputs) (hgraph : ∀ parameter, canonicalGraphInputs parameter ⊆ inputs)
    (dummy : OtsReferenceWords) (adversary : Adversary) :
    Pr[fun result => result.2.2.Marked result.1 (referenceFamilyWords result.2.1 dummy) |
      referenceContactGame inputs hencoding dummy adversary] ≤
    ∑ address : OtsPrefix.ChainAddress, Pr[= true | prefixContactGame inputs hencoding hgraph address dummy adversary] := by
  simp only [← referenceContactGame_contacted_eq inputs hencoding hgraph]
  let law := referenceContactGame inputs hencoding dummy adversary
  let event := fun address : OtsPrefix.ChainAddress => fun result : InstrumentedResult ContactResult =>
    result.2.2.Contacted result.1 (referenceFamilyWords result.2.1 dummy) address
  refine (_root_.probEvent_mono (mx := law) (q := fun result => ∃ address ∈ (Finset.univ : Finset OtsPrefix.ChainAddress), event address result) ?_).trans
    (probEvent_exists_finset_le_sum Finset.univ law event)
  intro result _ hm
  obtain ⟨address, ha⟩ := hm
  refine ⟨address, Finset.mem_univ address, ?_⟩
  change address ∈ OtsContactTrace.contacts result.1 (referenceFamilyWords result.2.1 dummy) result.2.2.frontier (result.2.2.before * result.2.2.after)
  rw [OtsContactTrace.contacts_mul]
  exact Finset.mem_union_left _ ha

theorem referenceContactGame_sum_contact_probability (inputs : Finset HashInput)
    (hencoding : ∀ parameter, canonicalEncodingInputs parameter ⊆ inputs) (hgraph : ∀ parameter, canonicalGraphInputs parameter ⊆ inputs)
    (dummy : OtsReferenceWords) (adversary : Adversary) :
    (∑ address : OtsPrefix.ChainAddress, Pr[= true | prefixContactGame inputs hencoding hgraph address dummy adversary]) =
      ∑' result, Pr[= result | referenceContactGame inputs hencoding dummy adversary] *
        ((OtsContactTrace.contacts result.1 (referenceFamilyWords result.2.1 dummy) result.2.2.frontier
          (result.2.2.before * result.2.2.after)).card : ENNReal) := by
  simp only [← referenceContactGame_contacted_eq inputs hencoding hgraph, ContactResult.Contacted]
  rw [← tsum_fintype (L := SummationFilter.unconditional OtsPrefix.ChainAddress)]
  simp only [probEvent_eq_tsum_ite]
  rw [ENNReal.tsum_comm]
  apply tsum_congr
  intro result
  rw [tsum_fintype, Fintype.sum_ite_mem, Finset.sum_const, nsmul_eq_mul, mul_comm]

theorem referenceContactGame_contacts_cost_le (dummy : OtsReferenceWords) (adversary : Adversary) (q : Nat)
    (hbound : HasHashQueryBound scheme adversary q) (hsmall : q < Fintype.card Digest) :
    (1 - (q : ENNReal) / Fintype.card Digest) *
      (∑' result, Pr[= result | referenceContactGame (canonicalGraphGameInputs adversary)
        (canonicalEncodingInputs_subset_gameInputs adversary) dummy adversary] *
          ((OtsContactTrace.contacts result.1 (referenceFamilyWords result.2.1 dummy) result.2.2.frontier
            (result.2.2.before * result.2.2.after)).card : ENNReal)) ≤
      (2 / Fintype.card Digest) *
        (∑' result : ReferenceRecordedResult, Pr[= result | referenceRecordedGame (canonicalGraphGameInputs adversary)
          (canonicalEncodingInputs_subset_gameInputs adversary) dummy adversary] * (result.prefixCalls dummy : ENNReal)) := by
  rw [← referenceContactGame_sum_contact_probability _ _ (canonicalGraphInputs_subset_gameInputs adversary)]
  have hsum := Finset.sum_le_sum (s := (Finset.univ : Finset OtsPrefix.ChainAddress))
    fun address _ => prefixContactGame_le address dummy adversary q hbound hsmall
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

theorem referenceContactGame_marked_cost_le (dummy : OtsReferenceWords) (adversary : Adversary) (q : Nat)
    (hbound : HasHashQueryBound scheme adversary q) (hsmall : q < Fintype.card Digest) :
    (1 - (q : ENNReal) / Fintype.card Digest) *
      Pr[fun result => result.2.2.Marked result.1 (referenceFamilyWords result.2.1 dummy) |
        referenceContactGame (canonicalGraphGameInputs adversary) (canonicalEncodingInputs_subset_gameInputs adversary) dummy adversary] ≤
      (2 / Fintype.card Digest) *
        (∑' result : ReferenceRecordedResult, Pr[= result | referenceRecordedGame (canonicalGraphGameInputs adversary)
          (canonicalEncodingInputs_subset_gameInputs adversary) dummy adversary] * (result.prefixCalls dummy : ENNReal)) := by
  have h := mul_le_mul' (le_refl (1 - (q : ENNReal) / Fintype.card Digest))
    (referenceContactGame_marked_le_sum _ (canonicalEncodingInputs_subset_gameInputs adversary)
      (canonicalGraphInputs_subset_gameInputs adversary) dummy adversary)
  rw [referenceContactGame_sum_contact_probability] at h
  exact h.trans (referenceContactGame_contacts_cost_le dummy adversary q hbound hsmall)

end SphincsSecurity.Concrete
