import SphincsSecurity.Proof.Ots.OtsPrefixRawSampling
namespace SphincsSecurity.Concrete.OtsPrefix

open _root_.OracleComp OracleSpec
attribute [local instance] Classical.propDecidable
attribute [local irreducible] canonicalEncodingInputs canonicalGraphInputs instFintypePosition
set_option backward.isDefEq.respectTransparency false

noncomputable def rawAnswer (segment : OtsPrefix) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs segment.parameter ⊆ inputs)
    (hgraph : canonicalGraphInputs segment.parameter ⊆ inputs)
    (encoding : canonicalEncodingInputs segment.parameter → HashOutput)
    (tables : Fin segment.digit.val → Digest → Digest) (high : segment.Query → High)
    (remaining : segment.RemainingRows inputs hencoding hgraph) : QueryImpl HashSpec Id :=
  finiteHashAnswer ∅ inputs (joinEncodingTable segment.parameter inputs hencoding encoding
    (segment.joinNonencoding inputs hencoding hgraph tables high remaining))

noncomputable def auxiliaryAnswer (segment : OtsPrefix) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs segment.parameter ⊆ inputs)
    (hgraph : canonicalGraphInputs segment.parameter ⊆ inputs)
    (encoding : canonicalEncodingInputs segment.parameter → HashOutput)
    (remaining : segment.RemainingRows inputs hencoding hgraph) : QueryImpl HashSpec Id :=
  segment.rawAnswer inputs hencoding hgraph encoding (fun _ _ => 0) (fun _ => 0) remaining

theorem rawAnswer_prefix (segment : OtsPrefix) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs segment.parameter ⊆ inputs)
    (hgraph : canonicalGraphInputs segment.parameter ⊆ inputs)
    (encoding : canonicalEncodingInputs segment.parameter → HashOutput)
    (tables : Fin segment.digit.val → Digest → Digest) (high : segment.Query → High)
    (remaining : segment.RemainingRows inputs hencoding hgraph) (query : segment.Query) :
    segment.rawAnswer inputs hencoding hgraph encoding tables high remaining (segment.input query) =
      combine (tables query.1 query.2) (high query) := by
  rw [rawAnswer, finiteHashAnswer_none ∅ inputs _ _ (hgraph (segment.input_mem_graph query)) (by simp)]
  exact (UniformTableSplit.join_outside (encodingInputCell segment.parameter inputs hencoding)
    (encodingInputCell_injective segment.parameter inputs hencoding) encoding _
    (segment.nonencodingCell inputs hencoding hgraph query)).trans
    (segment.joinNonencoding_prefix inputs hencoding hgraph tables high remaining query)

theorem rawAnswer_other (segment : OtsPrefix) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs segment.parameter ⊆ inputs)
    (hgraph : canonicalGraphInputs segment.parameter ⊆ inputs)
    (encoding : canonicalEncodingInputs segment.parameter → HashOutput)
    (first second : Fin segment.digit.val → Digest → Digest) (firstHigh secondHigh : segment.Query → High)
    (remaining : segment.RemainingRows inputs hencoding hgraph) (bytes : HashInput) (hparse : segment.parse bytes = none) :
    segment.rawAnswer inputs hencoding hgraph encoding first firstHigh remaining bytes =
      segment.rawAnswer inputs hencoding hgraph encoding second secondHigh remaining bytes := by
  by_cases hin : bytes ∈ inputs
  · rw [rawAnswer, rawAnswer, finiteHashAnswer_none ∅ inputs _ _ hin (by simp),
      finiteHashAnswer_none ∅ inputs _ _ hin (by simp)]
    by_cases henc : bytes ∈ canonicalEncodingInputs segment.parameter
    · exact (UniformTableSplit.join_embed (encodingInputCell segment.parameter inputs hencoding)
        (encodingInputCell_injective segment.parameter inputs hencoding) encoding _ ⟨bytes, henc⟩).trans
        (UniformTableSplit.join_embed (encodingInputCell segment.parameter inputs hencoding)
          (encodingInputCell_injective segment.parameter inputs hencoding) encoding _ ⟨bytes, henc⟩).symm
    · let cell : UniformTableSplit.Outside (encodingInputCell segment.parameter inputs hencoding) :=
        ⟨⟨bytes, hin⟩, UniformTableSplit.inclusion_not_range hencoding _ henc⟩
      have hcell : cell ∉ Set.range (segment.nonencodingCell inputs hencoding hgraph) := by
        rintro ⟨query, heq⟩
        have hbytes : segment.input query = bytes := congrArg (fun value => value.val.val) heq
        have hsome := (segment.parse_some_iff bytes query).mpr hbytes.symm
        rw [hparse] at hsome
        cases hsome
      calc
        _ = segment.joinNonencoding inputs hencoding hgraph first firstHigh remaining cell :=
          UniformTableSplit.join_outside (encodingInputCell segment.parameter inputs hencoding)
            (encodingInputCell_injective segment.parameter inputs hencoding) encoding _ cell
        _ = remaining ⟨cell, hcell⟩ :=
          UniformTableSplit.join_outside (segment.nonencodingCell inputs hencoding hgraph)
            (segment.nonencodingCell_injective inputs hencoding hgraph) _ remaining ⟨cell, hcell⟩
        _ = segment.joinNonencoding inputs hencoding hgraph second secondHigh remaining cell :=
          (UniformTableSplit.join_outside (segment.nonencodingCell inputs hencoding hgraph)
            (segment.nonencodingCell_injective inputs hencoding hgraph) _ remaining ⟨cell, hcell⟩).symm
        _ = _ :=
          (UniformTableSplit.join_outside (encodingInputCell segment.parameter inputs hencoding)
            (encodingInputCell_injective segment.parameter inputs hencoding) encoding _ cell).symm
  · simp only [rawAnswer, finiteHashAnswer, QueryCache.empty_apply, Option.getD_none, dif_neg hin]

theorem rawAnswer_eq (segment : OtsPrefix) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs segment.parameter ⊆ inputs)
    (hgraph : canonicalGraphInputs segment.parameter ⊆ inputs)
    (encoding : canonicalEncodingInputs segment.parameter → HashOutput)
    (tables : Fin segment.digit.val → Digest → Digest) (high : segment.Query → High)
    (remaining : segment.RemainingRows inputs hencoding hgraph) :
    segment.rawAnswer inputs hencoding hgraph encoding tables high remaining =
      segment.answer tables high (segment.auxiliaryAnswer inputs hencoding hgraph encoding remaining) := by
  funext bytes
  cases hparse : segment.parse bytes with
  | none =>
      rw [answer, hparse]
      exact segment.rawAnswer_other inputs hencoding hgraph encoding _ _ _ _ remaining bytes hparse
  | some query =>
      rw [(segment.parse_some_iff bytes query).mp hparse, rawAnswer_prefix, answer_input]

end SphincsSecurity.Concrete.OtsPrefix
