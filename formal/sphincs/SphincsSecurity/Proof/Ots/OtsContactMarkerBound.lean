import SphincsSecurity.Proof.Ots.EncodingContactMarkerSource
import SphincsSecurity.Proof.Ots.OtsContactFirstProbability
namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec OtsEncodingMarker
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] canonicalGraphInputs canonicalEncodingInputs canonicalGraphGameInputs Finset.univ OtsContactTrace.contacts

theorem referenceContactGame_contactMarker_le_cost (inputs : Finset HashInput)
    (hencoding : ∀ parameter, canonicalEncodingInputs parameter ⊆ inputs)
    (hgraph : ∀ parameter, canonicalGraphInputs parameter ⊆ inputs)
    (dummy : OtsReferenceWords) (adversary : Adversary) :
    Pr[fun result => ContactBeforeMarker result.1 (referenceFamilyWords result.2.1 dummy) result.2.2.frontier
      (result.2.2.before * result.2.2.after) | referenceContactGame inputs hencoding dummy adversary] ≤
      (41 / (Fintype.card Digest : ENNReal)) * ∑' result,
        Pr[= result | referenceContactGame inputs hencoding dummy adversary] *
          (contactMarkerCost result.1 (referenceFamilyWords result.2.1 dummy) result.2.2.frontier 1 (result.2.2.before * result.2.2.after) : ENNReal) := by
  refine le_trans ?_ (referenceContactGame_contactMarker_count_le inputs hencoding hgraph dummy adversary)
  rw [probEvent_eq_tsum_ite]
  apply ENNReal.tsum_le_tsum
  intro result
  split
  · rename_i he
    have hp := (contactMarkerCount_pos_iff _ _ _ _).mpr he
    exact (mul_one _).symm.trans_le (mul_le_mul' le_rfl (by exact_mod_cast Nat.succ_le_iff.mpr hp))
  · exact bot_le

theorem referenceContactGame_contactMarker_le_contacts (dummy : OtsReferenceWords) (adversary : Adversary) (budget : Nat)
    (hbound : HasHashQueryBound scheme adversary budget) :
    Pr[fun result => ContactBeforeMarker result.1 (referenceFamilyWords result.2.1 dummy) result.2.2.frontier
      (result.2.2.before * result.2.2.after) | referenceContactGame (canonicalGraphGameInputs adversary)
        (canonicalEncodingInputs_subset_gameInputs adversary) dummy adversary] ≤
      (41 * ((budget : ENNReal) / Fintype.card Digest)) * ∑' result,
        Pr[= result | referenceContactGame (canonicalGraphGameInputs adversary) (canonicalEncodingInputs_subset_gameInputs adversary) dummy adversary] *
          ((OtsContactTrace.contacts result.1 (referenceFamilyWords result.2.1 dummy) result.2.2.frontier
            (result.2.2.before * result.2.2.after)).card : ENNReal) := by
  have hcost : (∑' result, Pr[= result | referenceContactGame (canonicalGraphGameInputs adversary)
      (canonicalEncodingInputs_subset_gameInputs adversary) dummy adversary] *
        (contactMarkerCost result.1 (referenceFamilyWords result.2.1 dummy) result.2.2.frontier 1 (result.2.2.before * result.2.2.after) : ENNReal)) ≤
      (budget : ENNReal) * ∑' result, Pr[= result | referenceContactGame (canonicalGraphGameInputs adversary)
        (canonicalEncodingInputs_subset_gameInputs adversary) dummy adversary] *
          ((OtsContactTrace.contacts result.1 (referenceFamilyWords result.2.1 dummy) result.2.2.frontier
            (result.2.2.before * result.2.2.after)).card : ENNReal) := by
    rw [← ENNReal.tsum_mul_left]
    apply ENNReal.tsum_le_tsum
    intro result
    by_cases hr : result ∈ support (referenceContactGame (canonicalGraphGameInputs adversary)
        (canonicalEncodingInputs_subset_gameInputs adversary) dummy adversary)
    · have hl := (referenceContactGame_cost _ _ dummy adversary result hr).trans
        (referenceContactGame_hashCalls_le dummy adversary budget hbound result hr)
      have hc := (contactMarkerCost_le result.1 (referenceFamilyWords result.2.1 dummy) result.2.2.frontier 1
        (result.2.2.before * result.2.2.after)).trans (Nat.mul_le_mul_right _ hl)
      simp only [one_mul] at hc
      rw [mul_left_comm (budget : ENNReal)]
      apply mul_le_mul' le_rfl
      exact_mod_cast hc
    · rw [probOutput_eq_zero_of_not_mem_support hr, zero_mul, zero_mul, mul_zero]
  refine (referenceContactGame_contactMarker_le_cost _ _ (canonicalGraphInputs_subset_gameInputs adversary) dummy adversary).trans
    ((mul_le_mul' le_rfl hcost).trans_eq ?_)
  simp only [div_eq_mul_inv]
  ring

theorem referenceContactGame_contactMarker_shared_bound (dummy : OtsReferenceWords) (adversary : Adversary) (budget : Nat)
    (hbound : HasHashQueryBound scheme adversary budget) (hsmall : budget < Fintype.card Digest) :
    ((1 - (budget : ENNReal) / Fintype.card Digest) * (Fintype.card Digest : ENNReal)) *
      Pr[fun result => ContactBeforeMarker result.1 (referenceFamilyWords result.2.1 dummy) result.2.2.frontier
        (result.2.2.before * result.2.2.after) | referenceContactGame (canonicalGraphGameInputs adversary)
          (canonicalEncodingInputs_subset_gameInputs adversary) dummy adversary] ≤
      (82 * ((budget : ENNReal) / Fintype.card Digest)) * ∑' result,
        Pr[= result | referenceRecordedGame (canonicalGraphGameInputs adversary) (canonicalEncodingInputs_subset_gameInputs adversary) dummy adversary] *
          (result.prefixCalls dummy : ENNReal) := by
  have hraw := mul_le_mul' (le_refl (1 - (budget : ENNReal) / Fintype.card Digest))
    (referenceContactGame_contactMarker_le_contacts dummy adversary budget hbound)
  rw [mul_left_comm] at hraw
  have hc := hraw.trans (mul_le_mul' le_rfl (referenceContactGame_contacts_cost_le dummy adversary budget hbound hsmall))
  have hn : (Fintype.card Digest : ENNReal) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have h := mul_le_mul' (le_refl (Fintype.card Digest : ENNReal)) hc
  have hcancel : (Fintype.card Digest : ENNReal) * (Fintype.card Digest : ENNReal)⁻¹ = 1 := ENNReal.mul_inv_cancel hn (by finiteness)
  rw [mul_left_comm (Fintype.card Digest : ENNReal), ← mul_assoc] at h
  refine h.trans_eq ?_
  simp only [div_eq_mul_inv]
  calc
    _ = 82 * ((budget : ENNReal) * (Fintype.card Digest : ENNReal)⁻¹) *
        (∑' result, Pr[= result | referenceRecordedGame (canonicalGraphGameInputs adversary)
          (canonicalEncodingInputs_subset_gameInputs adversary) dummy adversary] * (result.prefixCalls dummy : ENNReal)) *
        ((Fintype.card Digest : ENNReal) * (Fintype.card Digest : ENNReal)⁻¹) := by ring
    _ = _ := by rw [hcancel, mul_one]

end SphincsSecurity.Concrete
