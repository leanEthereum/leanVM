import SphincsSecurity.Proof.Ots.OtsMarkerContactPartition
import SphincsSecurity.Proof.Ots.OtsMarkerContactBound
import SphincsSecurity.Proof.Ots.OtsContactMarkerBound
namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] canonicalGraphInputs canonicalEncodingInputs canonicalGraphGameInputs Finset.univ OtsContactTrace.contacts

theorem referenceContactGame_marker_residual_le_checkpoint (inputs : Finset HashInput)
    (hencoding : ∀ parameter, canonicalEncodingInputs parameter ⊆ inputs) (address : OtsPrefix.ChainAddress)
    (dummy : OtsReferenceWords) (adversary : Adversary) :
    Pr[fun result => (OtsEncodingMarker.Seen result.1 (referenceFamilyWords result.2.1 dummy) address (result.2.2.before * result.2.2.after) ∧
      address ∈ OtsContactTrace.contacts result.1 (referenceFamilyWords result.2.1 dummy) result.2.2.frontier (result.2.2.before * result.2.2.after)) ∧
        ¬OtsEncodingMarker.ContactBeforeMarker result.1 (referenceFamilyWords result.2.1 dummy) result.2.2.frontier
          (result.2.2.before * result.2.2.after) | referenceContactGame inputs hencoding dummy adversary] ≤
      Pr[fun result => result.2.2.ContactAfterStop (OtsEncodingMarker.stopAt address) result.1 (referenceFamilyWords result.2.1 dummy) address |
        markerCheckpointGame address inputs hencoding dummy adversary] := by
  have h := congrArg (fun law : SPMF (PublicParameter × ReferenceFamily × OtsFrontierValues × (Bool × SigningBoundaryTrace) × OtsContactTrace.Trace) =>
    Pr[fun result => (OtsEncodingMarker.Seen result.1 (referenceFamilyWords result.2.1 dummy) address result.2.2.2.2 ∧
      address ∈ OtsContactTrace.contacts result.1 (referenceFamilyWords result.2.1 dummy) result.2.2.1 result.2.2.2.2) ∧
        ¬OtsEncodingMarker.ContactBeforeMarker result.1 (referenceFamilyWords result.2.1 dummy) result.2.2.1 result.2.2.2.2 | law])
    (referenceCheckpointGame_frontier_trace (OtsEncodingMarker.stopAt address) inputs hencoding dummy adversary)
  simp only [probEvent_map, Function.comp_def] at h
  rw [← h]
  exact _root_.probEvent_mono fun result hr he =>
    markerCheckpointGame_partition inputs hencoding address dummy adversary result hr he.1.1 he.1.2 he.2

theorem referenceContactGame_markerContact_partition (inputs : Finset HashInput)
    (hencoding : ∀ parameter, canonicalEncodingInputs parameter ⊆ inputs) (dummy : OtsReferenceWords) (adversary : Adversary) :
    Pr[fun result => result.2.2.MarkerContact result.1 (referenceFamilyWords result.2.1 dummy) |
      referenceContactGame inputs hencoding dummy adversary] ≤
      Pr[fun result => OtsEncodingMarker.ContactBeforeMarker result.1 (referenceFamilyWords result.2.1 dummy) result.2.2.frontier
        (result.2.2.before * result.2.2.after) | referenceContactGame inputs hencoding dummy adversary] +
      ∑ address : OtsPrefix.ChainAddress,
        Pr[fun result => result.2.2.ContactAfterStop (OtsEncodingMarker.stopAt address) result.1 (referenceFamilyWords result.2.1 dummy) address |
          markerCheckpointGame address inputs hencoding dummy adversary] := by
  let law := referenceContactGame inputs hencoding dummy adversary
  let bad := fun result : InstrumentedResult ContactResult =>
    OtsEncodingMarker.ContactBeforeMarker result.1 (referenceFamilyWords result.2.1 dummy) result.2.2.frontier (result.2.2.before * result.2.2.after)
  let residual := fun address : OtsPrefix.ChainAddress => fun result : InstrumentedResult ContactResult =>
    (OtsEncodingMarker.Seen result.1 (referenceFamilyWords result.2.1 dummy) address (result.2.2.before * result.2.2.after) ∧
      address ∈ OtsContactTrace.contacts result.1 (referenceFamilyWords result.2.1 dummy) result.2.2.frontier (result.2.2.before * result.2.2.after)) ∧
        ¬bad result
  have hsplit : Pr[fun result => result.2.2.MarkerContact result.1 (referenceFamilyWords result.2.1 dummy) | law] ≤
      Pr[bad | law] + Pr[fun result => ∃ address ∈ (Finset.univ : Finset OtsPrefix.ChainAddress), residual address result | law] := by
    refine (_root_.probEvent_mono (q := fun result => bad result ∨
      ∃ address ∈ (Finset.univ : Finset OtsPrefix.ChainAddress), residual address result) ?_).trans (probEvent_or_le _ _ _)
    intro result _ hm
    by_cases hb : bad result
    · exact Or.inl hb
    · obtain ⟨address, hm, hc⟩ := hm
      exact Or.inr ⟨address, Finset.mem_univ address, ⟨hm, hc⟩, hb⟩
  refine hsplit.trans (add_le_add le_rfl ?_)
  refine (probEvent_exists_finset_le_sum Finset.univ law residual).trans (Finset.sum_le_sum ?_)
  intro address _
  exact referenceContactGame_marker_residual_le_checkpoint inputs hencoding address dummy adversary

theorem referenceContactGame_markerContact_shared_bound (dummy : OtsReferenceWords) (adversary : Adversary) (budget : Nat)
    (hbound : HasHashQueryBound scheme adversary budget) (hsmall : budget < Fintype.card Digest) :
    ((1 - (budget : ENNReal) / Fintype.card Digest) * (Fintype.card Digest : ENNReal)) *
      Pr[fun result => result.2.2.MarkerContact result.1 (referenceFamilyWords result.2.1 dummy) |
        referenceContactGame (canonicalGraphGameInputs adversary) (canonicalEncodingInputs_subset_gameInputs adversary) dummy adversary] ≤
      (82 * ((budget : ENNReal) / Fintype.card Digest)) * (∑' result,
        Pr[= result | referenceRecordedGame (canonicalGraphGameInputs adversary) (canonicalEncodingInputs_subset_gameInputs adversary) dummy adversary] *
          (result.prefixCalls dummy : ENNReal)) +
      (3444 * ((budget : ENNReal) / Fintype.card Digest)) * (∑' result,
        Pr[= result | referenceRecordedGame (canonicalGraphGameInputs adversary) (canonicalEncodingInputs_subset_gameInputs adversary) dummy adversary] *
          (result.encodingCalls : ENNReal)) := by
  have h := mul_le_mul' (le_refl ((1 - (budget : ENNReal) / Fintype.card Digest) * (Fintype.card Digest : ENNReal)))
    (referenceContactGame_markerContact_partition (canonicalGraphGameInputs adversary)
      (canonicalEncodingInputs_subset_gameInputs adversary) dummy adversary)
  rw [mul_add] at h
  exact h.trans (add_le_add (referenceContactGame_contactMarker_shared_bound dummy adversary budget hbound hsmall)
    (markerCheckpointGame_contact_shared_bound dummy adversary budget hbound hsmall))

theorem referenceContactGame_markerContact_le (dummy : OtsReferenceWords) (adversary : Adversary) (budget : Nat)
    (hbound : HasHashQueryBound scheme adversary budget) (hsmall : budget < Fintype.card Digest) :
    Pr[fun result => result.2.2.MarkerContact result.1 (referenceFamilyWords result.2.1 dummy) |
      referenceContactGame (canonicalGraphGameInputs adversary) (canonicalEncodingInputs_subset_gameInputs adversary) dummy adversary] ≤
      ((82 * ((budget : ENNReal) / Fintype.card Digest)) * (∑' result,
        Pr[= result | referenceRecordedGame (canonicalGraphGameInputs adversary) (canonicalEncodingInputs_subset_gameInputs adversary) dummy adversary] *
          (result.prefixCalls dummy : ENNReal)) +
       (3444 * ((budget : ENNReal) / Fintype.card Digest)) * (∑' result,
        Pr[= result | referenceRecordedGame (canonicalGraphGameInputs adversary) (canonicalEncodingInputs_subset_gameInputs adversary) dummy adversary] *
          (result.encodingCalls : ENNReal))) /
        ((1 - (budget : ENNReal) / Fintype.card Digest) * (Fintype.card Digest : ENNReal)) := by
  have hcard : (Fintype.card Digest : ENNReal) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hpositive : 0 < 1 - (budget : ENNReal) / Fintype.card Digest := by
    apply tsub_pos_iff_lt.mpr
    rw [ENNReal.div_lt_iff (Or.inl hcard) (Or.inl (by finiteness)), one_mul]
    exact_mod_cast hsmall
  apply (ENNReal.le_div_iff_mul_le (Or.inl (mul_ne_zero (ne_of_gt hpositive) hcard)) (Or.inl (by finiteness))).mpr
  simpa only [mul_comm] using referenceContactGame_markerContact_shared_bound dummy adversary budget hbound hsmall

end SphincsSecurity.Concrete
