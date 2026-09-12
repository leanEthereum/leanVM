import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Ots.EncodingOracleSplit
namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec
attribute [local instance] Classical.propDecidable
attribute [local irreducible] canonicalEncodingInputs canonicalGraphInputs
set_option backward.isDefEq.respectTransparency false

abbrev ReferenceSelection := Option (Fin encodingAttemptLimit × Encoding)

noncomputable def referenceTableSelection (key : SecretKey) (f : QueryImpl HashSpec Id)
    (position : EncodingPosition) : ReferenceSelection :=
  FirstSuccessTable.select decodeEncodingOutput (fun counter =>
    readCanonicalEncodingRows key.parameter (canonicalGraphLabels key.parameter key.otsSecret key.ftsSecret f)
      f (position, counter))

def referenceSelectionResult (selection : ReferenceSelection) : Option (Counter × Encoding) × Nat :=
  (selection.map (fun result => (BitVec.ofNat counterBits result.1.val, result.2)),
    selection.elim encodingAttemptLimit (fun result => result.1.val + 1))

theorem referenceSelectionResult_eq_search (key : SecretKey) (f : QueryImpl HashSpec Id)
    (position : EncodingPosition) :
    referenceSelectionResult (referenceTableSelection key f position) =
      canonicalEncodingSearch key f position.lay position.tree position.leafIdx := by
  rw [← congrFun (canonicalEncodingResults_eq key f) position]
  simp only [canonicalEncodingResults, referenceSelectionResult, referenceTableSelection, encodingTableResult, Nat.zero_add]

theorem referenceTableSelection_joinEncodingTable (key : SecretKey) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs key.parameter ⊆ inputs) (hgraph : canonicalGraphInputs key.parameter ⊆ inputs)
    (encoding : canonicalEncodingInputs key.parameter → HashOutput) (outside : NonencodingRows key.parameter inputs hencoding)
    (position : EncodingPosition) :
    referenceTableSelection key (finiteHashAnswer ∅ inputs (joinEncodingTable key.parameter inputs hencoding encoding outside))
      position = FirstSuccessTable.select decodeEncodingOutput
        (encoding ∘ referenceCounterCell key.parameter position (outsideGraphMessage key inputs hencoding outside position)) := by
  rw [referenceTableSelection, canonicalGraphLabels_joinEncodingTable _ _ _ _ hencoding hgraph]
  apply congrArg (FirstSuccessTable.select decodeEncodingOutput)
  funext counter
  change finiteHashAnswer ∅ inputs (joinEncodingTable key.parameter inputs hencoding encoding outside)
    (encodingRetryInput key.parameter position (outsideGraphMessage key inputs hencoding outside position) counter.val) = _
  rw [finiteHashAnswer_none ∅ inputs _ _
    (hencoding (encodingRetryInput_mem_canonicalEncodingInputs _ _ _ counter)) (by simp)]
  exact UniformTableSplit.join_embed _ _ encoding outside
    (referenceCounterCell key.parameter position (outsideGraphMessage key inputs hencoding outside position) counter)

noncomputable local instance instSampleableTypeForallSubtypeHashInputMemFinsetHashOutput_3 (inputs : Finset HashInput) : SampleableType (inputs → HashOutput) :=
  SampleableType.ofFintype (inputs → HashOutput)

end SphincsSecurity.Concrete
