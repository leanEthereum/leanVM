import SphincsSecurity.Proof.Hypertree.ReferenceGraphProgram
import SphincsSecurity.Proof.Reference.ReferenceAuxiliarySigning
namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec CanonicalProbeRouting
attribute [local instance] Classical.propDecidable
attribute [local irreducible] canonicalEncodingInputs canonicalGraphInputs instFintypePosition Finset.univ
set_option backward.isDefEq.respectTransparency false

noncomputable def structuralInputs (parameter : PublicParameter) (inputs : Finset HashInput) : Finset HashInput :=
  inputs.filter fun input => ∃ position, AtPosition parameter input position

attribute [local irreducible] structuralInputs

theorem mem_structuralInputs (parameter : PublicParameter) (inputs : Finset HashInput) (input : HashInput) :
    input ∈ structuralInputs parameter inputs ↔ input ∈ inputs ∧ ∃ position, AtPosition parameter input position := by
  rw [structuralInputs, Finset.mem_filter]

theorem structuralInputs_subset (parameter : PublicParameter) (inputs : Finset HashInput) : structuralInputs parameter inputs ⊆ inputs :=
  fun input hi => ((mem_structuralInputs parameter inputs input).mp hi).1

noncomputable def structuralInputCell (parameter : PublicParameter) (inputs : Finset HashInput) : structuralInputs parameter inputs → inputs :=
  Set.inclusion (structuralInputs_subset parameter inputs)

theorem structuralInputCell_injective (parameter : PublicParameter) (inputs : Finset HashInput) :
    Function.Injective (structuralInputCell parameter inputs) := Set.inclusion_injective (structuralInputs_subset parameter inputs)

abbrev NonstructuralRows (parameter : PublicParameter) (inputs : Finset HashInput) :=
  UniformTableSplit.Outside (structuralInputCell parameter inputs) → HashOutput

noncomputable def joinStructuralTable (parameter : PublicParameter) (inputs : Finset HashInput)
    (rows : structuralInputs parameter inputs → HashOutput) (outside : NonstructuralRows parameter inputs) : inputs → HashOutput :=
  UniformTableSplit.join (structuralInputCell parameter inputs) (structuralInputCell_injective parameter inputs) rows outside

theorem joinStructuralTable_agrees_outside (parameter : PublicParameter) (inputs : Finset HashInput)
    (left right : structuralInputs parameter inputs → HashOutput) (outside : NonstructuralRows parameter inputs)
    (input : HashInput) (hn : input ∉ structuralInputs parameter inputs) :
    finiteHashAnswer ∅ inputs (joinStructuralTable parameter inputs left outside) input =
      finiteHashAnswer ∅ inputs (joinStructuralTable parameter inputs right outside) input := by
  by_cases hin : input ∈ inputs
  · rw [finiteHashAnswer_none ∅ inputs _ _ hin (by simp), finiteHashAnswer_none ∅ inputs _ _ hin (by simp)]
    let cell : UniformTableSplit.Outside (structuralInputCell parameter inputs) :=
      ⟨⟨input, hin⟩, UniformTableSplit.inclusion_not_range (structuralInputs_subset parameter inputs) ⟨input, hin⟩ hn⟩
    exact (UniformTableSplit.join_outside _ _ left outside cell).trans
      (UniformTableSplit.join_outside _ _ right outside cell).symm
  · simp only [finiteHashAnswer, QueryCache.empty_apply, Option.getD_none, dif_neg hin]

noncomputable def structuralAnswer (key : SecretKey) (inputs : Finset HashInput) (labels : CanonicalGraphLabels)
    (outside : NonstructuralRows key.parameter inputs) (rows : structuralInputs key.parameter inputs → HashOutput) : QueryImpl HashSpec Id :=
  programmedHash key.parameter key.otsSecret key.ftsSecret labels
    (finiteHashAnswer ∅ inputs (joinStructuralTable key.parameter inputs rows outside))

theorem structuralAnswer_graph (key : SecretKey) (inputs : Finset HashInput) (labels : CanonicalGraphLabels)
    (outside : NonstructuralRows key.parameter inputs) (rows : structuralInputs key.parameter inputs → HashOutput) :
    canonicalGraphLabels key.parameter key.otsSecret key.ftsSecret (structuralAnswer key inputs labels outside rows) = labels :=
  canonicalGraphLabels_programmedHash _ _ _ _ _

theorem structuralAnswer_nonstructural (key : SecretKey) (inputs : Finset HashInput) (labels : CanonicalGraphLabels)
    (outside : NonstructuralRows key.parameter inputs) (left right : structuralInputs key.parameter inputs → HashOutput)
    (input : HashInput) (hn : ¬∃ position, AtPosition key.parameter input position) :
    structuralAnswer key inputs labels outside left input = structuralAnswer key inputs labels outside right input := by
  have hnot : input ∉ structuralInputs key.parameter inputs := fun hi => hn ((mem_structuralInputs _ _ _).mp hi).2
  have hcanonical : ∀ position, input ≠ canonicalGraphInput key.parameter key.otsSecret key.ftsSecret position labels :=
    fun position he => hn ⟨position, ⟨_, he⟩⟩
  rw [structuralAnswer, structuralAnswer, programmedHash_other _ _ _ _ _ input hcanonical,
    programmedHash_other _ _ _ _ _ input hcanonical]
  exact joinStructuralTable_agrees_outside key.parameter inputs left right outside input hnot

theorem structuralAnswer_selections (key : SecretKey) (inputs : Finset HashInput) (labels : CanonicalGraphLabels)
    (outside : NonstructuralRows key.parameter inputs) (left right : structuralInputs key.parameter inputs → HashOutput) :
    referenceTableSelection key (structuralAnswer key inputs labels outside left) =
      referenceTableSelection key (structuralAnswer key inputs labels outside right) := by
  funext position
  rw [referenceTableSelection, referenceTableSelection, structuralAnswer_graph, structuralAnswer_graph]
  apply congrArg (FirstSuccessTable.select decodeEncodingOutput)
  funext counter
  apply structuralAnswer_nonstructural
  rintro ⟨other, ho⟩
  exact (show AtEncodingPosition key.parameter (canonicalEncodingRowInput key.parameter labels (position, counter)) position from
    ⟨_, rfl⟩).not_atPosition other ho

theorem structuralAnswer_message (key : SecretKey) (inputs : Finset HashInput) (labels : CanonicalGraphLabels)
    (outside : NonstructuralRows key.parameter inputs) (left right : structuralInputs key.parameter inputs → HashOutput)
    (payload : HashInput) :
    structuralAnswer key inputs labels outside left (tweakableHashInput key.parameter .message payload) =
      structuralAnswer key inputs labels outside right (tweakableHashInput key.parameter .message payload) := by
  apply structuralAnswer_nonstructural
  rintro ⟨position, hp⟩
  have hd := (decodePosition_some_iff key.parameter _ position).mpr hp
  rw [decodePosition_message] at hd
  contradiction

noncomputable def structuralProgram (key : SecretKey) (inputs : Finset HashInput) (labels : CanonicalGraphLabels)
    (outside : NonstructuralRows key.parameter inputs) (words : OtsReferenceWords) (adversary : Adversary) :
    OracleComp OracleWorld (Bool × SigningBoundaryTrace) :=
  CausalFrontierProgram.game key.parameter (structuralAnswer key inputs labels outside (fun _ => 0)) key.ftsSecret words
    (canonicalGraphFrontier key.otsSecret labels words) adversary

theorem structuralProgram_eq (key : SecretKey) (inputs : Finset HashInput) (labels : CanonicalGraphLabels)
    (outside : NonstructuralRows key.parameter inputs) (rows : structuralInputs key.parameter inputs → HashOutput)
    (words : OtsReferenceWords) (adversary : Adversary) :
    CausalFrontierProgram.game key.parameter (structuralAnswer key inputs labels outside rows) key.ftsSecret words
        (canonicalGraphFrontier key.otsSecret labels words) adversary = structuralProgram key inputs labels outside words adversary :=
  CausalFrontierProgram.game_eq_of_graph key _ _ labels words (structuralAnswer_graph _ _ _ _ _) (structuralAnswer_graph _ _ _ _ _)
    (structuralAnswer_selections _ _ _ _ _ _) (fun _ _ _ => structuralAnswer_message _ _ _ _ _ _ _) adversary

end SphincsSecurity.Concrete
