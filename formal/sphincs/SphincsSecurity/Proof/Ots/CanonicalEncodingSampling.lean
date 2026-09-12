import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Hypertree.CanonicalGraphHonest
import SphincsSecurity.Proof.Ots.EncodingInputs
import SphincsSecurity.Proof.Reference.FiniteHashWorld
import SphincsSecurity.Proof.Ots.ReferenceEncodingTable
namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec OracleComp.DeferredSampling
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

noncomputable def canonicalGraphMessage (labels : CanonicalGraphLabels) (position : EncodingPosition) : Digest :=
  truncateHash (labels (layerMessagePosition
    (referenceIndex position.lay position.tree position.leafIdx) position.lay))

theorem layerMessagePosition_treeBound (index : Index) (lay : Layer) :
    (layerMessagePosition index lay).TreeBound := by
  unfold layerMessagePosition
  split_ifs <;> norm_num [Position.TreeBound, layerHeight, middleLayer, bottomLayer, topLayer, numLayers,
    maxLayerHeight]

theorem canonicalGraphMessage_eq (key : SecretKey) (f : QueryImpl HashSpec Id) (position : EncodingPosition) :
    canonicalGraphMessage (canonicalGraphLabels key.parameter key.otsSecret key.ftsSecret f) position =
      evalWithAnswerFn f (layerMessage key (referenceIndex position.lay position.tree position.leafIdx) position.lay) := by
  rw [canonicalGraphMessage, canonicalGraphLabels_eq_honest _ _ _ _ _ (layerMessagePosition_treeBound _ _),
    eval_layerMessage_eq_honestValue]
  rfl

theorem canonicalEncodingSearch_eq_graph_table (key : SecretKey) (f : QueryImpl HashSpec Id)
    (position : EncodingPosition) :
    canonicalEncodingSearch key f position.lay position.tree position.leafIdx =
      encodingTableResult (referenceEncodingTable key.parameter f position
        (canonicalGraphMessage (canonicalGraphLabels key.parameter key.otsSecret key.ftsSecret f) position)
        encodingAttemptLimit 0) 0 := by
  rw [canonicalEncodingSearch, canonicalGraphMessage_eq, referenceEncodingSearch_eq_table]

abbrev EncodingRow := EncodingPosition × Fin encodingAttemptLimit
abbrev CanonicalEncodingRows := EncodingRow → HashOutput

noncomputable def canonicalEncodingRowInput (parameter : PublicParameter) (labels : CanonicalGraphLabels)
    (row : EncodingRow) : HashInput :=
  encodingRetryInput parameter row.1 (canonicalGraphMessage labels row.1) row.2.val

theorem canonicalEncodingRowInput_injective (parameter : PublicParameter) (labels : CanonicalGraphLabels) :
    Function.Injective (canonicalEncodingRowInput parameter labels) := by
  rintro ⟨left, first⟩ ⟨right, second⟩ heq
  have hposition : left = right := atEncodingPosition_unique
    (show AtEncodingPosition parameter (canonicalEncodingRowInput parameter labels (left, first)) left from ⟨_, rfl⟩)
    (show AtEncodingPosition parameter (canonicalEncodingRowInput parameter labels (left, first)) right from
      ⟨_, heq⟩)
  subst right
  have hcounter := encodingRetryInput_injective_of_lt first.isLt second.isLt heq
  exact Prod.ext rfl (Fin.ext hcounter)

attribute [local irreducible] canonicalEncodingInputs

theorem canonicalEncodingRowInput_mem (parameter : PublicParameter) (labels : CanonicalGraphLabels)
    (row : EncodingRow) : canonicalEncodingRowInput parameter labels row ∈ canonicalEncodingInputs parameter := by
  rw [canonicalEncodingInputs, Finset.mem_biUnion]
  simp only [Finset.mem_univ, true_and]
  refine ⟨row.1, ?_⟩
  simp only [Finset.mem_image, Finset.mem_univ, true_and]
  exact ⟨(canonicalGraphMessage labels row.1, row.2), rfl⟩

noncomputable def canonicalEncodingCell (parameter : PublicParameter) (inputs : Finset HashInput)
    (hinputs : canonicalEncodingInputs parameter ⊆ inputs) (labels : CanonicalGraphLabels) (row : EncodingRow) : inputs :=
  ⟨canonicalEncodingRowInput parameter labels row, hinputs (canonicalEncodingRowInput_mem parameter labels row)⟩

theorem canonicalEncodingCell_injective (parameter : PublicParameter) (inputs : Finset HashInput)
    (hinputs : canonicalEncodingInputs parameter ⊆ inputs) (labels : CanonicalGraphLabels) :
    Function.Injective (canonicalEncodingCell parameter inputs hinputs labels) := by
  intro left right heq
  exact canonicalEncodingRowInput_injective parameter labels (congrArg Subtype.val heq)

noncomputable local instance instSampleableTypeForallSubtypeHashInputMemFinsetHashOutput_2 (inputs : Finset HashInput) : SampleableType (inputs → HashOutput) :=
  SampleableType.ofFintype (inputs → HashOutput)

noncomputable local instance instSampleableTypeCanonicalGraphLabels_1 : SampleableType CanonicalGraphLabels := SampleableType.ofFintype CanonicalGraphLabels

noncomputable local instance instSampleableTypeCanonicalEncodingRows : SampleableType CanonicalEncodingRows := SampleableType.ofFintype CanonicalEncodingRows

noncomputable local instance instSampleableTypeForallFinEncodingAttemptLimitHashOutput : SampleableType (Fin encodingAttemptLimit → HashOutput) :=
  SampleableType.ofFintype (Fin encodingAttemptLimit → HashOutput)

noncomputable def readCanonicalEncodingRows (parameter : PublicParameter) (labels : CanonicalGraphLabels)
    (f : QueryImpl HashSpec Id) : CanonicalEncodingRows := fun row => f (canonicalEncodingRowInput parameter labels row)

theorem readCanonicalEncodingRows_finite (parameter : PublicParameter) (inputs : Finset HashInput)
    (hinputs : canonicalEncodingInputs parameter ⊆ inputs) (labels : CanonicalGraphLabels)
    (table : inputs → HashOutput) :
    readCanonicalEncodingRows parameter labels (finiteHashAnswer ∅ inputs table) =
      table ∘ canonicalEncodingCell parameter inputs hinputs labels := by
  funext row
  exact finiteHashAnswer_none ∅ inputs table _ (hinputs (canonicalEncodingRowInput_mem parameter labels row)) (by simp)

def canonicalEncodingResults (rows : CanonicalEncodingRows) : EncodingPosition → Option (Counter × Encoding) × Nat :=
  fun position => encodingTableResult (fun counter => rows (position, counter)) 0

theorem canonicalEncodingResults_eq (key : SecretKey) (f : QueryImpl HashSpec Id) :
    canonicalEncodingResults (readCanonicalEncodingRows key.parameter
      (canonicalGraphLabels key.parameter key.otsSecret key.ftsSecret f) f) =
        fun position => canonicalEncodingSearch key f position.lay position.tree position.leafIdx := by
  funext position
  rw [canonicalEncodingSearch_eq_graph_table]
  apply congrArg (fun table => encodingTableResult table 0)
  funext counter
  simp only [readCanonicalEncodingRows, canonicalEncodingRowInput, referenceEncodingTable]
  rw [Nat.zero_add]

end SphincsSecurity.Concrete
