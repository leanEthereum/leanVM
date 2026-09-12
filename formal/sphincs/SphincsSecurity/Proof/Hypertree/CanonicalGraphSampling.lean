import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Hypertree.CanonicalGraph
import SphincsSecurity.Proof.Reference.FiniteHashWorld
namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec OracleComp.DeferredSampling
set_option backward.isDefEq.respectTransparency false

noncomputable local instance instSampleableTypeForallSubtypeHashInputMemFinsetHashOutput_1 (inputs : Finset HashInput) : SampleableType (inputs → HashOutput) :=
  SampleableType.ofFintype (inputs → HashOutput)

noncomputable local instance instSampleableTypeCanonicalGraphLabels : SampleableType CanonicalGraphLabels :=
  SampleableType.ofFintype CanonicalGraphLabels

noncomputable def canonicalPayloadInputs : Finset HashInput :=
  (Finset.range (numChains + 1)).biUnion fun length =>
    (Finset.univ : Finset (Fin length → Digest)).image (fun values => (List.ofFn values).flatMap digestBytes)

attribute [local irreducible] canonicalPayloadInputs

theorem flatMap_mem_canonicalPayloadInputs (values : List Digest) (hvalues : values.length ≤ numChains) :
    values.flatMap digestBytes ∈ canonicalPayloadInputs := by
  classical
  rw [canonicalPayloadInputs, Finset.mem_biUnion]
  refine ⟨values.length, Finset.mem_range.mpr (by omega), ?_⟩
  exact Finset.mem_image.mpr ⟨values.get, Finset.mem_univ _, by rw [List.ofFn_get]⟩

noncomputable def canonicalGraphInputs (parameter : PublicParameter) : Finset HashInput :=
  Finset.univ.biUnion fun position : Position =>
    canonicalPayloadInputs.image (tweakableHashInput parameter position.domain)

attribute [local irreducible] canonicalGraphInputs

variable (parameter : PublicParameter)
  (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
  (ftsSecret : Index → FtsTree → FtsLeaf → Digest)

theorem canonicalGraphSlots_length_le (labels : CanonicalGraphLabels) (position : Position) :
    (canonicalGraphSlots otsSecret ftsSecret labels position).length ≤ numChains := by
  have h := Position.children_length_le position
  cases position <;> simp only [canonicalGraphSlots] <;>
    (try split_ifs) <;> simp only [List.length_map, List.length_singleton] <;>
    first | exact h | decide

theorem canonicalGraphInput_mem (position : Position) (labels : CanonicalGraphLabels) :
    canonicalGraphInput parameter otsSecret ftsSecret position labels ∈ canonicalGraphInputs parameter := by
  classical
  rw [canonicalGraphInputs, Finset.mem_biUnion]
  simp only [Finset.mem_univ, true_and]
  refine ⟨position, ?_⟩
  exact Finset.mem_image.mpr ⟨(canonicalGraphSlots otsSecret ftsSecret labels position).flatMap digestBytes,
    flatMap_mem_canonicalPayloadInputs _
    (canonicalGraphSlots_length_le otsSecret ftsSecret labels position), rfl⟩

noncomputable def canonicalGraphCell (inputs : Finset HashInput)
    (hinputs : canonicalGraphInputs parameter ⊆ inputs)
    (position : Position) (labels : CanonicalGraphLabels) : inputs :=
  ⟨canonicalGraphInput parameter otsSecret ftsSecret position labels,
    hinputs (canonicalGraphInput_mem parameter otsSecret ftsSecret position labels)⟩

theorem canonicalGraphCell_separated (inputs : Finset HashInput)
    (hinputs : canonicalGraphInputs parameter ⊆ inputs) :
    FiniteGraphSampling.Separated (canonicalGraphCell parameter otsSecret ftsSecret inputs hinputs) := by
  intro left right hne before after heq
  exact canonicalGraphInput_separated parameter otsSecret ftsSecret left right hne before after
    (congrArg Subtype.val heq)

theorem read_canonicalGraphCell (inputs : Finset HashInput)
    (hinputs : canonicalGraphInputs parameter ⊆ inputs) (table : inputs → HashOutput)
    (positions : List Position) (labels : CanonicalGraphLabels) :
    FiniteGraphSampling.read (canonicalGraphCell parameter otsSecret ftsSecret inputs hinputs)
      (fun position output values => Function.update values position output) table positions labels =
      readCanonicalGraph parameter otsSecret ftsSecret (finiteHashAnswer ∅ inputs table) positions labels := by
  induction positions generalizing labels with
  | nil => rfl
  | cons position positions ih =>
      have hrow := hinputs (canonicalGraphInput_mem parameter otsSecret ftsSecret position labels)
      have hanswer := finiteHashAnswer_none ∅ inputs table
        (canonicalGraphInput parameter otsSecret ftsSecret position labels) hrow (by simp)
      change FiniteGraphSampling.read _ _ table positions (Function.update labels position
        (table (canonicalGraphCell parameter otsSecret ftsSecret inputs hinputs position labels))) =
          readCanonicalGraph parameter otsSecret ftsSecret (finiteHashAnswer ∅ inputs table) positions
            (Function.update labels position
              (finiteHashAnswer ∅ inputs table (canonicalGraphInput parameter otsSecret ftsSecret position labels)))
      rw [ih, hanswer]
      rfl

noncomputable def plantCanonicalGraph (inputs : Finset HashInput)
    (hinputs : canonicalGraphInputs parameter ⊆ inputs) : ProbComp (CanonicalGraphLabels × (inputs → HashOutput)) :=
  FiniteGraphSampling.plant (canonicalGraphCell parameter otsSecret ftsSecret inputs hinputs)
    (fun position output values => Function.update values position output) canonicalGraphOrder (fun _ => 0)

theorem evalDist_canonicalGraph_eq_plant (inputs : Finset HashInput)
    (hinputs : canonicalGraphInputs parameter ⊆ inputs) :
    𝒟[do
      let table ← sampleHashTable inputs
      pure (canonicalGraphLabels parameter otsSecret ftsSecret (finiteHashAnswer ∅ inputs table), table)] =
      𝒟[plantCanonicalGraph parameter otsSecret ftsSecret inputs hinputs] := by
  have h := FiniteGraphSampling.evalDist_read_eq_plant
    (canonicalGraphCell parameter otsSecret ftsSecret inputs hinputs)
    (fun position output values => Function.update values position output)
    (canonicalGraphCell_separated parameter otsSecret ftsSecret inputs hinputs)
    canonicalGraphOrder canonicalGraphOrder_nodup (fun _ => 0)
  simpa only [read_canonicalGraphCell, canonicalGraphLabels, plantCanonicalGraph, sampleHashTable] using h

theorem evalDist_canonicalGraph_bind_eq_plant {Result : Type} (inputs : Finset HashInput)
    (hinputs : canonicalGraphInputs parameter ⊆ inputs)
    (next : CanonicalGraphLabels → (inputs → HashOutput) → ProbComp Result) :
    𝒟[do
      let table ← sampleHashTable inputs
      next (canonicalGraphLabels parameter otsSecret ftsSecret (finiteHashAnswer ∅ inputs table)) table] =
      𝒟[do let result ← plantCanonicalGraph parameter otsSecret ftsSecret inputs hinputs; next result.1 result.2] := by
  have h := congrArg (fun distribution : SPMF (CanonicalGraphLabels × (inputs → HashOutput)) =>
    distribution >>= fun result => 𝒟[next result.1 result.2])
    (evalDist_canonicalGraph_eq_plant parameter otsSecret ftsSecret inputs hinputs)
  simpa only [evalDist_bind, evalDist_pure, bind_assoc, pure_bind] using h

end SphincsSecurity.Concrete
