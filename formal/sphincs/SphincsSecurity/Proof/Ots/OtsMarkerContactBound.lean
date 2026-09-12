import SphincsSecurity.Proof.Ots.OtsMarkerContactSource
namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] canonicalGraphInputs canonicalEncodingInputs canonicalGraphGameInputs Finset.univ

private theorem sum_membership_probability {Address Result : Type} [Fintype Address] [DecidableEq Address]
    (law : SPMF Result) (marked : Result → Finset Address) :
    (∑ address : Address, Pr[fun result => address ∈ marked result | law]) =
      ∑' result, Pr[= result | law] * ((marked result).card : ENNReal) := by
  rw [← tsum_fintype (L := SummationFilter.unconditional Address)]
  simp only [probEvent_eq_tsum_ite]
  rw [ENNReal.tsum_comm]
  apply tsum_congr
  intro result
  rw [tsum_fintype, Fintype.sum_ite_mem, Finset.sum_const, nsmul_eq_mul, mul_comm]

theorem referenceContactGame_sum_marker_probability (inputs : Finset HashInput)
    (hencoding : ∀ parameter, canonicalEncodingInputs parameter ⊆ inputs) (dummy : OtsReferenceWords) (adversary : Adversary) :
    (∑ address : OtsPrefix.ChainAddress, Pr[fun result => OtsEncodingMarker.Seen result.1 (referenceFamilyWords result.2.1 dummy) address
      (result.2.2.before * result.2.2.after) | referenceContactGame inputs hencoding dummy adversary]) =
      ∑' result, Pr[= result | referenceContactGame inputs hencoding dummy adversary] *
        ((OtsEncodingMarker.markers result.1 (referenceFamilyWords result.2.1 dummy) (result.2.2.before * result.2.2.after)).card : ENNReal) := by
  simpa only [OtsEncodingMarker.mem_markers] using sum_membership_probability
    (referenceContactGame inputs hencoding dummy adversary)
    (fun result => OtsEncodingMarker.markers result.1 (referenceFamilyWords result.2.1 dummy) (result.2.2.before * result.2.2.after))

theorem markerCheckpointGame_contact_shared_bound (dummy : OtsReferenceWords) (adversary : Adversary) (budget : Nat)
    (hbound : HasHashQueryBound scheme adversary budget) (hsmall : budget < Fintype.card Digest) :
    ((1 - (budget : ENNReal) / Fintype.card Digest) * (Fintype.card Digest : ENNReal)) *
      (∑ address : OtsPrefix.ChainAddress,
        Pr[fun result => result.2.2.ContactAfterStop (OtsEncodingMarker.stopAt address) result.1 (referenceFamilyWords result.2.1 dummy) address |
          markerCheckpointGame address (canonicalGraphGameInputs adversary) (canonicalEncodingInputs_subset_gameInputs adversary) dummy adversary]) ≤
      (3444 * ((budget : ENNReal) / Fintype.card Digest)) * ∑' result,
        Pr[= result | referenceRecordedGame (canonicalGraphGameInputs adversary) (canonicalEncodingInputs_subset_gameInputs adversary) dummy adversary] *
          (result.encodingCalls : ENNReal) := by
  have hsum := Finset.sum_le_sum (s := (Finset.univ : Finset OtsPrefix.ChainAddress))
    (fun address _ => markerCheckpointGame_contact_le_marker address dummy adversary budget hbound hsmall)
  rw [← Finset.mul_sum, ← Finset.mul_sum, referenceContactGame_sum_marker_probability] at hsum
  refine hsum.trans ((mul_le_mul' le_rfl (referenceContactGame_markers_le_encodingCost dummy adversary)).trans_eq ?_)
  simp only [Nat.cast_mul, Nat.cast_ofNat, div_eq_mul_inv]
  ring

end SphincsSecurity.Concrete
