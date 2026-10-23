import Sphincs.SecurityHiddenGraphRows
import SphincsBase.Proof.Base.UniformTableSplit

/-! Exact independent-coordinate decomposition of the material secret table and the graph's
full-output labels. Every hidden digest is extracted from a distinct actual sampled answer;
the other128bits and all unselected answers remain explicit independent residual data. -/

open OracleComp OracleSpec
namespace Sphincs.Security.HiddenGraph
open Graph SeedModel SphincsBase.Concrete.UniformTableSplit
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option maxHeartbeats 100000
attribute [local instance] Classical.propDecidable

abbrev SampleCell := SecretPosition ⊕ Position
abbrev JoinedOutputs := SampleCell → HashOutput

noncomputable opaque sampleCellFintype : Fintype SampleCell := inferInstance
noncomputable local instance : Fintype SampleCell := sampleCellFintype
noncomputable local instance : DecidableEq SampleCell := Classical.decEq _

/-- The sampled full answer containing each hidden128-bit coordinate. -/
def coordinateCell : Coordinate → SampleCell
  | .chain lay tree leaf chainIdx position =>
      if h : position.val = 0 then .inl (.inl (lay, tree, leaf, chainIdx))
      else .inr (.chain lay tree leaf chainIdx
        ⟨position.val - 1, by have := position.isLt; simp only [chainLength, winternitzBits] at *; omega⟩)
  | .fchain index c s j a i position =>
      if h : position.val = 0 then .inl (.inr (.inl (index, c, s, j, a, i)))
      else .inr (.fchain index c s j a i
        ⟨position.val - 1, by have := position.isLt; simp only [chainTop] at *; omega⟩)

def coordinateAtCell : SampleCell → Option Coordinate
  | .inl (.inl (lay, tree, leaf, chainIdx)) => some (.chain lay tree leaf chainIdx ⟨0, by decide⟩)
  | .inl (.inr (.inl (index, c, s, j, a, i))) => some (.fchain index c s j a i ⟨0, by decide⟩)
  | .inl (.inr (.inr _)) => none
  | .inr (.chain lay tree leaf chainIdx step) =>
      some (.chain lay tree leaf chainIdx ⟨step.val + 1, by have := step.isLt; omega⟩)
  | .inr (.fchain index c s j a i t) =>
      some (.fchain index c s j a i ⟨t.val + 1, by have := t.isLt; simp only [chainTop] at *; omega⟩)
  | .inr _ => none

theorem coordinateAtCell_cell (coordinate : Coordinate) :
    coordinateAtCell (coordinateCell coordinate) = some coordinate := by
  cases coordinate with
  | chain lay tree leaf chainIdx position => fin_cases position <;> rfl
  | fchain index c s j a i position => fin_cases position <;> rfl

theorem coordinateCell_injective : Function.Injective coordinateCell := by
  intro left right heq
  exact Option.some.inj (by simpa only [coordinateAtCell_cell] using congrArg coordinateAtCell heq)

theorem coordinateCell_outgoing (address : Address) :
    coordinateCell address.outputCoordinate = .inr address.position := by
  cases address with
  | chain lay tree leaf chainIdx step => fin_cases step <;> rfl
  | fchain index c s j a i t => fin_cases t <;> rfl

abbrev CoordinateHighs := Coordinate → Prefix.High
abbrev RemainingOutputs := Outside coordinateCell → HashOutput

noncomputable def splitCoordinateRows :
    (Coordinate → HashOutput) ≃ Table × CoordinateHighs where
  toFun outputs := (fun coordinate => truncateHash (outputs coordinate),
    fun coordinate => (splitHashOutput digestBits (outputs coordinate)).2)
  invFun pair coordinate := Prefix.combine (pair.1 coordinate) (pair.2 coordinate)
  left_inv outputs := funext fun coordinate => Prefix.combine_split (outputs coordinate)
  right_inv pair := Prod.ext
    (funext fun coordinate => Prefix.truncate_combine (pair.1 coordinate) (pair.2 coordinate))
    (funext fun coordinate => congrArg Prod.snd (Prefix.split_combine (pair.1 coordinate) (pair.2 coordinate)))

theorem uniform_coordinate_rows :
    PMF.uniformOfFintype (Coordinate → HashOutput) =
      (PMF.uniformOfFintype Table).bind (fun lows =>
        (PMF.uniformOfFintype CoordinateHighs).map
          (fun highs coordinate => Prefix.combine (lows coordinate) (highs coordinate))) := by
  have h := PMF.uniformOfFintype_map_of_bijective splitCoordinateRows.symm splitCoordinateRows.symm.bijective
  rw [uniform_product, PMF.map_bind] at h
  simpa only [PMF.map_comp, Function.comp_def, splitCoordinateRows, Equiv.coe_fn_symm_mk] using h.symm

noncomputable def assemble (lows : Table) (highs : CoordinateHighs)
    (remaining : RemainingOutputs) : JoinedOutputs :=
  join coordinateCell coordinateCell_injective
    (fun coordinate => Prefix.combine (lows coordinate) (highs coordinate)) remaining

theorem assemble_coordinate (lows : Table) (highs : CoordinateHighs) (remaining : RemainingOutputs)
    (coordinate : Coordinate) :
    assemble lows highs remaining (coordinateCell coordinate) =
      Prefix.combine (lows coordinate) (highs coordinate) :=
  join_embed coordinateCell coordinateCell_injective _ remaining coordinate

theorem assemble_remaining (lows : Table) (highs : CoordinateHighs) (remaining : RemainingOutputs)
    (cell : Outside coordinateCell) :
    assemble lows highs remaining cell.val = remaining cell :=
  join_outside coordinateCell coordinateCell_injective _ remaining cell

/-- All low coordinates, high halves, and other sampled answers are independent. -/
theorem uniform_joined_outputs :
    PMF.uniformOfFintype JoinedOutputs =
      (PMF.uniformOfFintype Table).bind (fun lows =>
        (PMF.uniformOfFintype CoordinateHighs).bind (fun highs =>
          (PMF.uniformOfFintype RemainingOutputs).map (assemble lows highs))) := by
  rw [uniform_join coordinateCell coordinateCell_injective, uniform_coordinate_rows]
  simp only [PMF.bind_bind, PMF.bind_map, Function.comp_def]
  rfl

def joinedSecrets (outputs : JoinedOutputs) : SecretOutputs := outputs ∘ Sum.inl
def joinedLabels (outputs : JoinedOutputs) : CanonicalGraphLabels := outputs ∘ Sum.inr
def joinedPair (outputs : JoinedOutputs) : SecretOutputs × CanonicalGraphLabels :=
  (joinedSecrets outputs, joinedLabels outputs)

theorem joinedPair_bijective : Function.Bijective joinedPair :=
  (Equiv.sumArrowEquivProdArrow SecretPosition Position HashOutput).bijective

/-- This is the actual product sampling used by material preparation and graph presampling,
decomposed into the independent coordinate table required by the stopped reveal experiment. -/
theorem uniform_material_graph_outputs :
    (PMF.uniformOfFintype SecretOutputs).bind (fun secrets =>
      (PMF.uniformOfFintype CanonicalGraphLabels).map (fun labels => (secrets, labels))) =
      (PMF.uniformOfFintype Table).bind (fun lows =>
        (PMF.uniformOfFintype CoordinateHighs).bind (fun highs =>
          (PMF.uniformOfFintype RemainingOutputs).map
            (fun remaining => joinedPair (assemble lows highs remaining)))) := by
  rw [← uniform_product]
  rw [← PMF.uniformOfFintype_map_of_bijective joinedPair joinedPair_bijective, uniform_joined_outputs]
  simp only [PMF.map_bind, PMF.map_comp, Function.comp_def]

def otsFromOutputs (outputs : SecretOutputs) (lay : Layer) (tree : TreeIndex)
    (leaf : LeafIndex) (chainIdx : ChainIndex) : Digest :=
  truncateHash (outputs (.inl (lay, tree, leaf, chainIdx)))

def ftsFromOutputs (outputs : SecretOutputs) : ForestSecrets := fun index c s j a i =>
  truncateHash (outputs (.inr (.inl (index, c, s, j, a, i))))

theorem coordinates_joined (outputs : JoinedOutputs) (coordinate : Coordinate) :
    coordinates (otsFromOutputs (joinedSecrets outputs)) (ftsFromOutputs (joinedSecrets outputs))
      (joinedLabels outputs) coordinate = truncateHash (outputs (coordinateCell coordinate)) := by
  cases coordinate with
  | chain lay tree leaf chainIdx position => fin_cases position <;> rfl
  | fchain index c s j a i position => fin_cases position <;> rfl

/-- The extracted coordinate function is literally the independent low-bit table. -/
theorem coordinates_assemble (lows : Table) (highs : CoordinateHighs) (remaining : RemainingOutputs) :
    coordinates (otsFromOutputs (joinedSecrets (assemble lows highs remaining)))
      (ftsFromOutputs (joinedSecrets (assemble lows highs remaining)))
      (joinedLabels (assemble lows highs remaining)) = lows := by
  funext coordinate
  rw [coordinates_joined, assemble_coordinate, Prefix.truncate_combine]

theorem highHalves_assemble (lows : Table) (highs : CoordinateHighs) (remaining : RemainingOutputs)
    (address : Address) :
    highHalves (joinedLabels (assemble lows highs remaining)) address = highs address.outputCoordinate := by
  simp only [highHalves, joinedLabels, Function.comp_def]
  rw [← coordinateCell_outgoing address, assemble_coordinate, Prefix.split_combine]

theorem completed_active_label (active : Position → Prop) (initial answers : CanonicalGraphLabels)
    (position : Position) (hactive : active position) :
    completedLabels (graphOrder active) initial answers position = answers position := by
  simp only [completedLabels, (mem_graphOrder active position).mpr hactive, ↓reduceIte]

theorem completed_row_high (active : Position → Prop) (initial answers : CanonicalGraphLabels)
    (address : Address) (hactive : active address.position) :
    highHalves (completedLabels (graphOrder active) initial answers) address = highHalves answers address := by
  unfold highHalves
  rw [completed_active_label _ _ _ _ hactive]

noncomputable local instance : SampleableType SecretOutputs := secretOutputsSampleableType
noncomputable local instance : SampleableType CanonicalGraphLabels := graphLabelsSampleable
noncomputable local instance : SampleableType Table := SampleableType.ofFintype _
noncomputable local instance : SampleableType CoordinateHighs := SampleableType.ofFintype _
noncomputable local instance : SampleableType RemainingOutputs := SampleableType.ofFintype _

noncomputable def sampleSplitPair : ProbComp (SecretOutputs × CanonicalGraphLabels) := do
  let lows ← $ᵗ Table
  let highs ← $ᵗ CoordinateHighs
  (fun remaining => joinedPair (assemble lows highs remaining)) <$> ($ᵗ RemainingOutputs)

private theorem uniformSample_evalDistEq_pmf (T : Type) [Fintype T] [Nonempty T] [SampleableType T] :
    ($ᵗ T : ProbComp T) =ᵈ PMF.uniformOfFintype T := by
  refine evalDistEq_iff_forall_prEvent_eq_output.mpr fun x => ?_
  rw [SampleableType.prEvent_uniformSample_eq_singleton, PMF.probOutput_eq_apply,
    PMF.uniformOfFintype_apply]

/-- The probability-program version uses the very secret and graph sampling instances of
the seeded-material and graph-preparation modules. -/
theorem evalDist_sampleSplitPair :
    (($ᵗ SecretOutputs) >>= fun secrets =>
      (fun labels => (secrets, labels)) <$> ($ᵗ CanonicalGraphLabels)) =ᵈ sampleSplitPair := by
  have hl : (($ᵗ SecretOutputs) >>= fun secrets =>
      (fun labels => (secrets, labels)) <$> ($ᵗ CanonicalGraphLabels)) =ᵈ
      ((PMF.uniformOfFintype SecretOutputs).bind fun secrets =>
        (PMF.uniformOfFintype CanonicalGraphLabels).map fun labels => (secrets, labels)) :=
    (uniformSample_evalDistEq_pmf _).bind fun _ => (uniformSample_evalDistEq_pmf _).map _
  have hr : sampleSplitPair =ᵈ ((PMF.uniformOfFintype Table).bind fun lows =>
      (PMF.uniformOfFintype CoordinateHighs).bind fun highs =>
        (PMF.uniformOfFintype RemainingOutputs).map
          fun remaining => joinedPair (assemble lows highs remaining)) :=
    (uniformSample_evalDistEq_pmf _).bind fun _ => (uniformSample_evalDistEq_pmf _).bind fun _ =>
      (uniformSample_evalDistEq_pmf _).map _
  rw [uniform_material_graph_outputs] at hl
  exact hl.trans hr.symm

/-- The public-parameter answer remains independently sampled outside the coordinate split.
This is an exact law of the actual prepared material and independently sampled graph labels. -/
theorem evalDist_sampleMaterial_graph :
    (sampleMaterial >>= fun material =>
      (fun labels => (material, labels)) <$> ($ᵗ CanonicalGraphLabels)) =ᵈ (($ᵗ HashOutput) >>= fun parameterOutput =>
        (fun pair => ((parameterOutput, pair.1), pair.2)) <$> sampleSplitPair) := by
  simp only [sampleMaterial, bind_assoc, pure_bind]
  refine EvalDistEq.bind_right _ fun parameterOutput => ?_
  have h := EvalDistEq.map evalDist_sampleSplitPair
    (fun pair : SecretOutputs × CanonicalGraphLabels => ((parameterOutput, pair.1), pair.2))
  simpa only [map_bind, Functor.map_map, Function.comp_def] using h

/-- Arbitrary adaptive continuations, including query logging and original-cost counters,
can follow the exact material/coordinate decomposition. -/
theorem evalDist_material_graph_continuation {α : Type}
    (next : Material → CanonicalGraphLabels → ProbComp α) :
    (sampleMaterial >>= fun material => ($ᵗ CanonicalGraphLabels) >>= next material) =ᵈ (($ᵗ HashOutput) >>= fun parameterOutput => sampleSplitPair >>= fun pair =>
        next (parameterOutput, pair.1) pair.2) := by
  have h := evalDist_sampleMaterial_graph.bind_left (fun pair => next pair.1 pair.2)
  simpa only [bind_assoc, bind_map_left] using h

end Sphincs.Security.HiddenGraph
