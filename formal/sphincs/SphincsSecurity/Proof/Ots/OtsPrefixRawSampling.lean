import SphincsSecurity.Proof.Ots.OtsPrefixOracle
import SphincsSecurity.Proof.Ots.ReferenceFamilySeed
namespace SphincsSecurity.Concrete.OtsPrefix

open _root_.OracleComp OracleSpec
attribute [local irreducible] canonicalEncodingInputs canonicalGraphInputs canonicalPayloadInputs instFintypePosition
set_option backward.isDefEq.respectTransparency false

theorem input_mem_graph (segment : OtsPrefix) (query : segment.Query) :
    segment.input query ∈ canonicalGraphInputs segment.parameter := by
  rw [canonicalGraphInputs, Finset.mem_biUnion]
  simp only [Finset.mem_univ, true_and]
  refine ⟨.chain segment.lay segment.tree segment.leaf segment.chainIdx (segment.step query.1), ?_⟩
  apply Finset.mem_image.mpr
  refine ⟨[query.2].flatMap digestBytes, flatMap_mem_canonicalPayloadInputs _ (by change 1 ≤ numChains; decide), ?_⟩
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, input, Position.domain]

theorem input_not_encoding (segment : OtsPrefix) (query : segment.Query) :
    segment.input query ∉ canonicalEncodingInputs segment.parameter := by
  intro h
  rw [canonicalEncodingInputs] at h
  simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_image] at h
  obtain ⟨position, pair, heq⟩ := h
  have hencoding : AtEncodingPosition segment.parameter (segment.input query) position := ⟨_, heq.symm⟩
  exact hencoding.not_atPosition
    (.chain segment.lay segment.tree segment.leaf segment.chainIdx (segment.step query.1)) ⟨digestBytes query.2, rfl⟩

noncomputable def nonencodingCell (segment : OtsPrefix) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs segment.parameter ⊆ inputs)
    (hgraph : canonicalGraphInputs segment.parameter ⊆ inputs) (query : segment.Query) :
    UniformTableSplit.Outside (encodingInputCell segment.parameter inputs hencoding) :=
  ⟨⟨segment.input query, hgraph (segment.input_mem_graph query)⟩,
    UniformTableSplit.inclusion_not_range hencoding _ (segment.input_not_encoding query)⟩

theorem nonencodingCell_injective (segment : OtsPrefix) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs segment.parameter ⊆ inputs)
    (hgraph : canonicalGraphInputs segment.parameter ⊆ inputs) :
    Function.Injective (segment.nonencodingCell inputs hencoding hgraph) := by
  intro left right heq
  exact segment.input_injective (congrArg (fun cell => cell.val.val) heq)

noncomputable def splitRows (segment : OtsPrefix) :
    (segment.Query → HashOutput) ≃ (Fin segment.digit.val → Digest → Digest) × (segment.Query → High) where
  toFun rows := (fun level input => truncateHash (rows (level, input)), fun query => (splitHashOutput digestBits (rows query)).2)
  invFun pair query := combine (pair.1 query.1 query.2) (pair.2 query)
  left_inv rows := funext fun query => combine_split (rows query)
  right_inv pair := Prod.ext
    (funext fun level => funext fun input => truncate_combine (pair.1 level input) (pair.2 (level, input)))
    (funext fun query => congrArg Prod.snd (split_combine (pair.1 query.1 query.2) (pair.2 query)))

theorem uniform_rows (segment : OtsPrefix) :
    PMF.uniformOfFintype (segment.Query → HashOutput) =
      (PMF.uniformOfFintype (Fin segment.digit.val → Digest → Digest)).bind (fun tables =>
        (PMF.uniformOfFintype (segment.Query → High)).map (fun high => fun query => combine (tables query.1 query.2) (high query))) := by
  have h := PMF.uniformOfFintype_map_of_bijective segment.splitRows.symm segment.splitRows.symm.bijective
  rw [UniformTableSplit.uniform_product, PMF.map_bind] at h
  simpa only [PMF.map_comp, Function.comp_def, splitRows, Equiv.coe_fn_symm_mk] using h.symm

abbrev RemainingRows (segment : OtsPrefix) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs segment.parameter ⊆ inputs)
    (hgraph : canonicalGraphInputs segment.parameter ⊆ inputs) :=
  UniformTableSplit.Outside (segment.nonencodingCell inputs hencoding hgraph) → HashOutput

noncomputable def joinNonencoding (segment : OtsPrefix) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs segment.parameter ⊆ inputs)
    (hgraph : canonicalGraphInputs segment.parameter ⊆ inputs)
    (tables : Fin segment.digit.val → Digest → Digest) (high : segment.Query → High)
    (remaining : segment.RemainingRows inputs hencoding hgraph) : NonencodingRows segment.parameter inputs hencoding :=
  UniformTableSplit.join (segment.nonencodingCell inputs hencoding hgraph)
    (segment.nonencodingCell_injective inputs hencoding hgraph)
    (fun query => combine (tables query.1 query.2) (high query)) remaining

theorem joinNonencoding_prefix (segment : OtsPrefix) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs segment.parameter ⊆ inputs)
    (hgraph : canonicalGraphInputs segment.parameter ⊆ inputs)
    (tables : Fin segment.digit.val → Digest → Digest) (high : segment.Query → High)
    (remaining : segment.RemainingRows inputs hencoding hgraph) (query : segment.Query) :
    segment.joinNonencoding inputs hencoding hgraph tables high remaining
        (segment.nonencodingCell inputs hencoding hgraph query) = combine (tables query.1 query.2) (high query) :=
  UniformTableSplit.join_embed _ _ _ _ _

theorem uniform_nonencoding (segment : OtsPrefix) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs segment.parameter ⊆ inputs)
    (hgraph : canonicalGraphInputs segment.parameter ⊆ inputs) :
    PMF.uniformOfFintype (NonencodingRows segment.parameter inputs hencoding) =
      (PMF.uniformOfFintype (Fin segment.digit.val → Digest → Digest)).bind (fun tables =>
        (PMF.uniformOfFintype (segment.Query → High)).bind (fun high =>
          (PMF.uniformOfFintype (segment.RemainingRows inputs hencoding hgraph)).map
            (segment.joinNonencoding inputs hencoding hgraph tables high))) := by
  rw [UniformTableSplit.uniform_join (segment.nonencodingCell inputs hencoding hgraph)
    (segment.nonencodingCell_injective inputs hencoding hgraph), segment.uniform_rows]
  simp only [PMF.bind_bind, PMF.bind_map, Function.comp_def]
  rfl

end SphincsSecurity.Concrete.OtsPrefix
