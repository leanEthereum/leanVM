import SphincsSecurity.Proof.Ots.EncodingTraceCache
import SphincsSecurity.Proof.Ots.EncodingMarkerKernel
namespace SphincsSecurity.Concrete.OtsEncodingMarker

open _root_.OracleComp OracleSpec UniformTableCompletion EncodingObservation
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] Finset.univ canonicalEncodingInputs markers

def NewMarker (parameter : PublicParameter) (words : OtsReferenceWords) (history : OtsContactTrace.Trace)
    (address : OtsPrefix.ChainAddress) (entry : HashInput × HashOutput) : Prop :=
  EntryMarker parameter words address entry ∧ ¬Seen parameter words address history

theorem NewMarker.not_mem {parameter : PublicParameter} {words : OtsReferenceWords} {history : OtsContactTrace.Trace}
    {address : OtsPrefix.ChainAddress} {entry : HashInput × HashOutput}
    (h : NewMarker parameter words history address entry) : entry ∉ history.toList :=
  fun hin => h.2 ⟨entry, hin, h.1⟩

theorem newMarker_cell_le (parameter : PublicParameter) (messages : EncodingPosition → Digest)
    (selections : ReferenceFamily) (dummy : OtsReferenceWords) (history : OtsContactTrace.Trace)
    (allowed : canonicalEncodingInputs parameter → Finset HashOutput)
    (hc : TraceConsistent parameter (referenceEncodingAllowed parameter messages selections) history allowed)
    (address : OtsPrefix.ChainAddress) (row : canonicalEncodingInputs parameter) :
    Pr[fun output => NewMarker parameter (referenceFamilyWords selections dummy) history address (row.val, output) |
      cell (allowed row)] ≤ 41 / (Fintype.card Digest : ENNReal) := by
  refine (_root_.probEvent_mono (fun _ _ h => ⟨h.1, h.not_mem⟩)).trans
    ((hc.new_reply_probability_le row (fun output => EntryMarker parameter (referenceFamilyWords selections dummy) address
      (row.val, output))).trans ?_)
  simpa only [cell, dif_pos (referenceEncodingAllowed_nonempty parameter messages selections row), SPMF.probEvent_liftM] using
    entryMarker_allowed_le parameter messages selections dummy address row

theorem newMarker_subset_cell_le (parameter : PublicParameter) (messages : EncodingPosition → Digest)
    (selections : ReferenceFamily) (dummy : OtsReferenceWords) (history : OtsContactTrace.Trace)
    (allowed : canonicalEncodingInputs parameter → Finset HashOutput)
    (hc : TraceConsistent parameter (referenceEncodingAllowed parameter messages selections) history allowed)
    (addresses : Finset OtsPrefix.ChainAddress) (row : canonicalEncodingInputs parameter) :
    Pr[fun output => ∃ address ∈ addresses, NewMarker parameter (referenceFamilyWords selections dummy) history address (row.val, output) |
      cell (allowed row)] ≤ (41 * (addresses.card : ENNReal)) / Fintype.card Digest := by
  have h := (probEvent_exists_finset_le_sum addresses (cell (allowed row))
    (fun address output => NewMarker parameter (referenceFamilyWords selections dummy) history address (row.val, output))).trans
    (Finset.sum_le_sum fun address _ => newMarker_cell_le parameter messages selections dummy history allowed hc address row)
  simpa only [Finset.sum_const, nsmul_eq_mul, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using h

theorem newMarker_any_cell_le (parameter : PublicParameter) (messages : EncodingPosition → Digest)
    (selections : ReferenceFamily) (dummy : OtsReferenceWords) (history : OtsContactTrace.Trace)
    (allowed : canonicalEncodingInputs parameter → Finset HashOutput)
    (hc : TraceConsistent parameter (referenceEncodingAllowed parameter messages selections) history allowed)
    (row : canonicalEncodingInputs parameter) :
    Pr[fun output => ∃ address, NewMarker parameter (referenceFamilyWords selections dummy) history address (row.val, output) |
      cell (allowed row)] ≤ 1722 / (Fintype.card Digest : ENNReal) := by
  refine (_root_.probEvent_mono (fun _ _ h => ?_)).trans
    ((hc.new_reply_probability_le row (fun output => ∃ address, EntryMarker parameter (referenceFamilyWords selections dummy) address
      (row.val, output))).trans ?_)
  · obtain ⟨address, hm⟩ := h
    exact ⟨⟨address, hm.1⟩, hm.not_mem⟩
  · simpa only [cell, dif_pos (referenceEncodingAllowed_nonempty parameter messages selections row), SPMF.probEvent_liftM] using
      entryMarker_any_allowed_le parameter messages selections dummy row

section Cardinality

local instance (priority := 11000) : DecidableEq OtsPrefix.ChainAddress := inferInstance
attribute [local instance 10000] Classical.propDecidable

theorem markers_step_card (parameter : PublicParameter) (words : OtsReferenceWords)
    (history : OtsContactTrace.Trace) (entry : HashInput × HashOutput) :
    (markers parameter words (history * FreeMonoid.of entry)).card = (markers parameter words history).card +
      if ∃ address, NewMarker parameter words history address entry then 1 else 0 := by
  rw [markers_mul]
  by_cases hm : ∃ address, NewMarker parameter words history address entry
  · obtain ⟨address, he, hn⟩ := hm
    have hi : address ∈ markers parameter words (FreeMonoid.of entry) := (mem_markers _ _ _ _).mpr ((seen_of _ _ _ _).mpr he)
    have hs : markers parameter words (FreeMonoid.of entry) = {address} :=
      Finset.eq_singleton_iff_unique_mem.mpr ⟨hi, fun other ho =>
        entryMarker_unique parameter words entry other address ((seen_of _ _ _ _).mp ((mem_markers _ _ _ _).mp ho)) he⟩
    have ha : address ∉ markers parameter words history := fun hin => hn ((mem_markers _ _ _ _).mp hin)
    rw [if_pos ⟨address, he, hn⟩, hs, Finset.union_singleton, Finset.card_insert_of_notMem ha]
  · have hs : markers parameter words (FreeMonoid.of entry) ⊆ markers parameter words history := by
      intro address hi
      by_contra hn
      exact hm ⟨address, (seen_of _ _ _ _).mp ((mem_markers _ _ _ _).mp hi),
        fun hs => hn ((mem_markers _ _ _ _).mpr hs)⟩
    rw [if_neg hm, Finset.union_eq_left.mpr hs, Nat.add_zero]

end Cardinality

end SphincsSecurity.Concrete.OtsEncodingMarker
