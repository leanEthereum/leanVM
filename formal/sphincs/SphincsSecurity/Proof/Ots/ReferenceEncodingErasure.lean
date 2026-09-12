import SphincsSecurity.Proof.Ots.ReferenceEncodingProgram
import SphincsSecurity.Proof.Reference.ReferenceInstrumentedGame
namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] canonicalEncodingInputs canonicalGraphInputs

noncomputable def referenceEncodingRepresentative (key : SecretKey) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs key.parameter ⊆ inputs)
    (outside : NonencodingRows key.parameter inputs hencoding) (selections : ReferenceFamily) :
    canonicalEncodingInputs key.parameter → HashOutput :=
  if h : ∃ encoding, referenceTableSelection key
      (finiteHashAnswer ∅ inputs (joinEncodingTable key.parameter inputs hencoding encoding outside)) = selections
  then Classical.choose h else fun _ => 0

theorem referenceEncodingRepresentative_selected (key : SecretKey) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs key.parameter ⊆ inputs)
    (outside : NonencodingRows key.parameter inputs hencoding) (selections : ReferenceFamily)
    (encoding : canonicalEncodingInputs key.parameter → HashOutput)
    (hselected : referenceTableSelection key
      (finiteHashAnswer ∅ inputs (joinEncodingTable key.parameter inputs hencoding encoding outside)) = selections) :
    referenceTableSelection key (finiteHashAnswer ∅ inputs (joinEncodingTable key.parameter inputs hencoding
      (referenceEncodingRepresentative key inputs hencoding outside selections) outside)) = selections := by
  have hex : ∃ encoding, referenceTableSelection key
      (finiteHashAnswer ∅ inputs (joinEncodingTable key.parameter inputs hencoding encoding outside)) = selections :=
    ⟨encoding, hselected⟩
  rw [referenceEncodingRepresentative, dif_pos hex]
  exact Classical.choose_spec hex

noncomputable def referenceEncodingProgram (key : SecretKey) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs key.parameter ⊆ inputs)
    (outside : NonencodingRows key.parameter inputs hencoding) (selections : ReferenceFamily)
    (dummy : OtsReferenceWords) (adversary : Adversary) : OracleComp OracleWorld (Bool × SigningBoundaryTrace) :=
  let words := referenceFamilyWords selections dummy
  let frontier := canonicalGraphFrontier key.otsSecret (canonicalGraphLabels key.parameter key.otsSecret key.ftsSecret
    (nonencodingAnswer key.parameter inputs hencoding outside)) words
  CausalFrontierProgram.game key.parameter
    (finiteHashAnswer ∅ inputs (joinEncodingTable key.parameter inputs hencoding
      (referenceEncodingRepresentative key inputs hencoding outside selections) outside)) key.ftsSecret words frontier adversary

theorem referenceEncodingProgram_selected (key : SecretKey) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs key.parameter ⊆ inputs) (hgraph : canonicalGraphInputs key.parameter ⊆ inputs)
    (outside : NonencodingRows key.parameter inputs hencoding) (selections : ReferenceFamily)
    (encoding : canonicalEncodingInputs key.parameter → HashOutput)
    (hselected : referenceTableSelection key
      (finiteHashAnswer ∅ inputs (joinEncodingTable key.parameter inputs hencoding encoding outside)) = selections)
    (dummy : OtsReferenceWords) (adversary : Adversary) :
    let words := referenceFamilyWords selections dummy
    let frontier := canonicalGraphFrontier key.otsSecret (canonicalGraphLabels key.parameter key.otsSecret key.ftsSecret
      (nonencodingAnswer key.parameter inputs hencoding outside)) words
    CausalFrontierProgram.game key.parameter
        (finiteHashAnswer ∅ inputs (joinEncodingTable key.parameter inputs hencoding encoding outside))
        key.ftsSecret words frontier adversary =
      referenceEncodingProgram key inputs hencoding outside selections dummy adversary :=
  joinedEncoding_program_eq key inputs hencoding hgraph encoding _ outside selections hselected
    (referenceEncodingRepresentative_selected key inputs hencoding outside selections encoding hselected) dummy adversary

noncomputable def referenceEncodingRest {Result : Type} (observer : FrontierObserver Result)
    (key : SecretKey) (inputs : Finset HashInput) (hencoding : canonicalEncodingInputs key.parameter ⊆ inputs)
    (outside : NonencodingRows key.parameter inputs hencoding) (selections : ReferenceFamily)
    (encoding : canonicalEncodingInputs key.parameter → HashOutput)
    (dummy : OtsReferenceWords) (adversary : Adversary) : ProbComp Result :=
  let words := referenceFamilyWords selections dummy
  let frontier := canonicalGraphFrontier key.otsSecret (canonicalGraphLabels key.parameter key.otsSecret key.ftsSecret
    (nonencodingAnswer key.parameter inputs hencoding outside)) words
  simulateQ (fixedHashWorld (finiteHashAnswer ∅ inputs (joinEncodingTable key.parameter inputs hencoding encoding outside)))
    (observer key.parameter words frontier (referenceEncodingProgram key inputs hencoding outside selections dummy adversary))

theorem referenceEncodingRest_selected {Result : Type} (observer : FrontierObserver Result)
    (key : SecretKey) (inputs : Finset HashInput) (hencoding : canonicalEncodingInputs key.parameter ⊆ inputs)
    (hgraph : canonicalGraphInputs key.parameter ⊆ inputs)
    (outside : NonencodingRows key.parameter inputs hencoding) (selections : ReferenceFamily)
    (encoding : canonicalEncodingInputs key.parameter → HashOutput)
    (hselected : referenceTableSelection key
      (finiteHashAnswer ∅ inputs (joinEncodingTable key.parameter inputs hencoding encoding outside)) = selections)
    (dummy : OtsReferenceWords) (adversary : Adversary) :
    let oracle := finiteHashAnswer ∅ inputs (joinEncodingTable key.parameter inputs hencoding encoding outside)
    referenceInstrumentedRest observer key oracle (canonicalGraphLabels key.parameter key.otsSecret key.ftsSecret oracle)
        selections dummy adversary =
      referenceEncodingRest observer key inputs hencoding outside selections encoding dummy adversary := by
  dsimp only
  rw [referenceInstrumentedRest, canonicalGraphLabels_joinEncodingTable _ _ _ _ hencoding hgraph]
  rw [referenceEncodingProgram_selected key inputs hencoding hgraph outside selections encoding hselected]
  rfl

theorem referenceEncodingRest_table {Result : Type} (observer : FrontierObserver Result)
    (key : SecretKey) (inputs : Finset HashInput) (hencoding : canonicalEncodingInputs key.parameter ⊆ inputs)
    (hgraph : canonicalGraphInputs key.parameter ⊆ inputs) (selections : ReferenceFamily)
    (table : inputs → HashOutput) (hselected : referenceTableSelection key (finiteHashAnswer ∅ inputs table) = selections)
    (dummy : OtsReferenceWords) (adversary : Adversary) :
    referenceInstrumentedRest observer key (finiteHashAnswer ∅ inputs table)
        (canonicalGraphLabels key.parameter key.otsSecret key.ftsSecret (finiteHashAnswer ∅ inputs table)) selections dummy adversary =
      referenceEncodingRest observer key inputs hencoding (fun cell => table cell.val) selections
        (table ∘ encodingInputCell key.parameter inputs hencoding) dummy adversary := by
  have hjoin : joinEncodingTable key.parameter inputs hencoding (table ∘ encodingInputCell key.parameter inputs hencoding)
      (fun cell => table cell.val) = table := UniformTableSplit.join_split _ _ table
  have hs : referenceTableSelection key (finiteHashAnswer ∅ inputs (joinEncodingTable key.parameter inputs hencoding
      (table ∘ encodingInputCell key.parameter inputs hencoding) (fun cell => table cell.val))) = selections := by
    rw [hjoin]
    exact hselected
  have h := referenceEncodingRest_selected observer key inputs hencoding hgraph (fun cell => table cell.val) selections
    (table ∘ encodingInputCell key.parameter inputs hencoding) hs dummy adversary
  simpa only [hjoin] using h

end SphincsSecurity.Concrete
