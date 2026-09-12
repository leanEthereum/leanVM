import SphincsSecurity.Proof.Ots.PublicEncodingMatch
import SphincsSecurity.Proof.Ots.EncodingTablePrior
namespace SphincsSecurity.Concrete.PublicEncodingMatch

open _root_.OracleComp OracleSpec UniformTableCompletion
attribute [local instance] Classical.propDecidable
attribute [local irreducible] Finset.univ canonicalEncodingInputs canonicalGraphInputs
set_option backward.isDefEq.respectTransparency false

theorem reference_cell_not_match (parameter : PublicParameter) (messages : EncodingPosition → Digest)
    (words : OtsReferenceWords) (selections : ReferenceFamily) (row : EncodingRow) (word : Encoding)
    (hselected : selections row.1 = some (row.2, word)) (answer : HashOutput) :
    ¬Match parameter messages words selections (referenceFamilyCell parameter messages row).val answer := by
  rintro ⟨position, hat, hnonreference, _⟩
  have hp : AtEncodingPosition parameter (referenceFamilyCell parameter messages row).val row.1 := ⟨_, rfl⟩
  obtain rfl := atEncodingPosition_unique hat hp
  apply hnonreference
  rw [referenceInput, hselected]
  rfl

theorem match_allowed_cases (parameter : PublicParameter) (messages : EncodingPosition → Digest)
    (words : OtsReferenceWords) (selections : ReferenceFamily) (cell : canonicalEncodingInputs parameter) :
    referenceEncodingAllowed parameter messages selections cell = Finset.univ ∨
      ∀ answer ∈ referenceEncodingAllowed parameter messages selections cell,
        ¬Match parameter messages words selections cell.val answer := by
  by_cases hc : cell ∈ Set.range (referenceFamilyCell parameter messages)
  · obtain ⟨row, rfl⟩ := hc
    rw [referenceEncodingAllowed, UniformTableSplit.join_embed, encodingFamilyAllowed]
    cases hs : selections row.1 with
    | none =>
        right
        intro answer ha hm
        have hi := (FirstSuccessTable.mem_invalid decodeEncodingOutput answer).mp ha
        obtain ⟨_, _, _, hd⟩ := hm
        rw [hi] at hd
        contradiction
    | some selected =>
        obtain ⟨index, word⟩ := selected
        simp only [encodingSelectionAllowed]
        split_ifs with hfiber
        · rw [FirstSuccessTable.allowed]
          split_ifs with hlt heq
          · right
            intro answer ha hm
            have hi := (FirstSuccessTable.mem_invalid decodeEncodingOutput answer).mp ha
            obtain ⟨_, _, _, hd⟩ := hm
            rw [hi] at hd
            contradiction
          · right
            intro answer _
            apply reference_cell_not_match parameter messages words selections row word ?_ answer
            simpa only [heq] using hs
          · exact Or.inl rfl
        · exact Or.inl rfl
  · left
    exact UniformTableSplit.join_outside (referenceFamilyCell parameter messages)
      (referenceFamilyCell_injective parameter messages) (encodingFamilyAllowed selections) (fun _ => Finset.univ)
      (⟨cell, hc⟩ : UniformTableSplit.Outside (referenceFamilyCell parameter messages))

theorem match_allowed_le (parameter : PublicParameter) (messages : EncodingPosition → Digest)
    (words : OtsReferenceWords) (selections : ReferenceFamily) (cell : canonicalEncodingInputs parameter) :
    Pr[Match parameter messages words selections cell.val |
      PMF.uniformOfFinset (referenceEncodingAllowed parameter messages selections cell)
        (referenceEncodingAllowed_nonempty parameter messages selections cell)] ≤ (Fintype.card Digest : ENNReal)⁻¹ := by
  rcases match_allowed_cases parameter messages words selections cell with hfull | hnone
  · simpa only [probEvent_eq_tsum_ite, PMF.probOutput_eq_apply, PMF.uniformOfFinset_apply,
      hfull, Finset.mem_univ, if_true, Finset.card_univ, SPMF.probOutput_liftM, PMF.uniformOfFintype_apply] using
      prob_match_le parameter messages words selections cell.val
  · have hz : Pr[Match parameter messages words selections cell.val |
        PMF.uniformOfFinset (referenceEncodingAllowed parameter messages selections cell)
          (referenceEncodingAllowed_nonempty parameter messages selections cell)] = 0 := by
      simp only [probEvent_eq_tsum_ite, PMF.probOutput_eq_apply]
      apply ENNReal.tsum_eq_zero.mpr
      intro answer
      by_cases ha : answer ∈ referenceEncodingAllowed parameter messages selections cell
      · exact if_neg (hnone answer ha)
      · simp only [PMF.uniformOfFinset_apply, if_neg ha, ite_self]
    rw [hz]
    exact bot_le

end SphincsSecurity.Concrete.PublicEncodingMatch
