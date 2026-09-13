import SphincsSecurity.Proof.Ots.OtsChainBackward
import SphincsSecurity.Proof.Ots.OtsEncodingMarker
import SphincsSecurity.Proof.Hypertree.GraphPayloadInputs
namespace SphincsSecurity.Concrete.OtsVerifierWitness

open _root_.OracleComp OracleSpec OtsContactTrace
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] chainWalk canonicalEncodingInputs canonicalPayloadInputs

variable (f : QueryImpl HashSpec Id) (parameter : PublicParameter) (words : OtsReferenceWords)
  (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex) (secret : ChainIndex → Digest)

abbrev segment (index : ChainIndex) : OtsPrefix := OtsPrefix.atAddress parameter words ⟨lay, tree, leaf, index⟩

def frontier (index : ChainIndex) : Digest := honestChain f parameter lay tree leaf index (secret index) (words lay tree leaf index).val

def ChainException (trace : Trace) : Prop :=
  (∃ index, ForwardChainMatch f (segment parameter words lay tree leaf index) (secret index) trace) ∨
  (∃ index, SeenTwoEdge (segment parameter words lay tree leaf index) (frontier f parameter words lay tree leaf secret index) trace) ∨
  (∃ left right, left ≠ right ∧
    Seen (segment parameter words lay tree leaf left) (frontier f parameter words lay tree leaf secret left) trace ∧
    Seen (segment parameter words lay tree leaf right) (frontier f parameter words lay tree leaf secret right) trace) ∨
  (∃ index, OtsEncodingMarker.Seen parameter words ⟨lay, tree, leaf, index⟩ trace ∧
    Seen (segment parameter words lay tree leaf index) (frontier f parameter words lay tree leaf secret index) trace)

theorem otsLeaf_chain_run (message : Digest) (counter : Counter) (values : ChainIndex → Digest) (candidate : Encoding) (trace : Trace)
    (hencode : evalWithAnswerFn f (encode parameter lay tree leaf message counter) = some candidate)
    (hrun : ContainsRun f trace (otsLeaf parameter lay tree leaf message counter values)) (index : ChainIndex) :
    ContainsRun f trace (recoverChain parameter lay tree leaf index (candidate index) (values index)) := by
  have htail := hrun.bind_right
  rw [hencode] at htail
  exact ContainsRun.sequenceFin_component _ htail.bind_left index

theorem otsLeaf_marker (message : Digest) (counter : Counter) (values : ChainIndex → Digest) (candidate : Encoding) (trace : Trace)
    (hencode : evalWithAnswerFn f (encode parameter lay tree leaf message counter) = some candidate)
    (hrun : ContainsRun f trace (otsLeaf parameter lay tree leaf message counter values))
    (index : ChainIndex) (hneighbor : TargetSum.UnitNeighborAt (words lay tree leaf) candidate index) :
    OtsEncodingMarker.Seen parameter words ⟨lay, tree, leaf, index⟩ trace := by
  let input := tweakableHashInput parameter (.encoding lay tree leaf) (digestBytes message ++ counterBytes counter)
  have hi : input ∈ queriedInputs f (encode parameter lay tree leaf message counter) := by
    simp only [encode, queriedInputs_bind, queriedInputs_tweakableHash, queriedInputs_pure,
      List.append_nil, List.mem_singleton, input]
  refine ⟨(input, f input), hrun.bind_left input hi, ?_⟩
  apply (OtsEncodingMarker.entryMarker_encoding_iff parameter words ⟨lay, tree, leaf, index⟩ message counter (f input)).mpr
  refine ⟨candidate, ?_, hneighbor⟩
  simpa only [encode, evalWithAnswerFn_bind, eval_tweakableHash, evalWithAnswerFn_pure, decodeEncodingOutput, input] using hencode

theorem otsLeaf_chain_classification (message : Digest) (counter : Counter) (values : ChainIndex → Digest)
    (candidate : Encoding) (trace : Trace) (hvalid : TargetSum.Valid (words lay tree leaf))
    (hencode : evalWithAnswerFn f (encode parameter lay tree leaf message counter) = some candidate)
    (hrun : ContainsRun f trace (otsLeaf parameter lay tree leaf message counter values))
    (hendpoints : ∀ index, evalWithAnswerFn f (recoverChain parameter lay tree leaf index (candidate index) (values index))
      = honestChain f parameter lay tree leaf index (secret index) (chainLength - 1)) :
    (candidate = words lay tree leaf ∧ ∀ index, values index = frontier f parameter words lay tree leaf secret index) ∨
      ChainException f parameter words lay tree leaf secret trace := by
  by_cases hforward : ∃ index, ForwardChainMatch f (segment parameter words lay tree leaf index) (secret index) trace
  · exact Or.inr (Or.inl hforward)
  have hn (index : ChainIndex) : ¬ForwardChainMatch f (segment parameter words lay tree leaf index) (secret index) trace :=
    fun h => hforward ⟨index, h⟩
  have hc (index : ChainIndex) := otsLeaf_chain_run f parameter lay tree leaf message counter values candidate trace hencode hrun index
  have hf (index : ChainIndex) (hb : (candidate index).val ≤ (words lay tree leaf index).val) :
      walkValue f parameter lay tree leaf index (candidate index).val (values index)
        ((words lay tree leaf index).val - (candidate index).val) = frontier f parameter words lay tree leaf secret index :=
    recover_frontier f (segment parameter words lay tree leaf index) (secret index) (values index) (candidate index) trace hb
      (hendpoints index) (hc index) (hn index)
  have hcontact (index : ChainIndex) (hb : (candidate index).val < (words lay tree leaf index).val) :
      Seen (segment parameter words lay tree leaf index) (frontier f parameter words lay tree leaf secret index) trace :=
    recover_contact f (segment parameter words lay tree leaf index) (values index) (candidate index) trace hb _ (hf index (Nat.le_of_lt hb)) (hc index)
  have hcandidate := valid_of_eval_encode_eq_some f parameter lay tree leaf message counter candidate hencode
  rcases TargetSum.valid_encoding_classification hvalid hcandidate with heq | ⟨index, hneighbor⟩ | ⟨index, hlarge⟩ | ⟨left, right, hne, hl, hr⟩
  · refine Or.inl ⟨heq.symm, ?_⟩
    intro index
    have hd := congrArg (fun word : Encoding => word index) heq
    simpa only [frontier, hd] using recover_value f (segment parameter words lay tree leaf index) (secret index) (values index)
      (candidate index) trace (by change (words lay tree leaf index).val ≤ (candidate index).val; rw [hd]) (hendpoints index) (hc index) (hn index)
  · refine Or.inr (Or.inr (Or.inr (Or.inr ⟨index,
      otsLeaf_marker f parameter words lay tree leaf message counter values candidate trace hencode hrun index hneighbor, ?_⟩)))
    obtain ⟨raised, _, hlower, _⟩ := hneighbor
    exact hcontact index (by omega)
  · exact Or.inr (Or.inr (Or.inl ⟨index,
      recover_twoEdge f (segment parameter words lay tree leaf index) (values index) (candidate index) trace hlarge _
        (hf index (by omega)) (hc index)⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨left, right, hne, hcontact left hl, hcontact right hr⟩)))

def canonicalLeaf : Digest := evalWithAnswerFn f (leafHash parameter lay tree leaf
  (fun index => honestChain f parameter lay tree leaf index (secret index) (chainLength - 1)))

def LeafOutputMatch (trace : Trace) : Prop :=
  ∃ payload, payload ∈ canonicalPayloadInputs ∧ payload ≠ leafPayload (fun index => honestChain f parameter lay tree leaf index (secret index) (chainLength - 1)) ∧
    (tweakableHashInput parameter (.leaf lay tree leaf) payload, f (tweakableHashInput parameter (.leaf lay tree leaf) payload)) ∈ trace.toList ∧
    truncateHash (f (tweakableHashInput parameter (.leaf lay tree leaf) payload)) = canonicalLeaf f parameter lay tree leaf secret

theorem otsLeaf_classification (message : Digest) (counter : Counter) (values : ChainIndex → Digest)
    (candidate : Encoding) (trace : Trace) (hvalid : TargetSum.Valid (words lay tree leaf))
    (hencode : evalWithAnswerFn f (encode parameter lay tree leaf message counter) = some candidate)
    (hrun : ContainsRun f trace (otsLeaf parameter lay tree leaf message counter values))
    (hleaf : evalWithAnswerFn f (otsLeaf parameter lay tree leaf message counter values)
      = some (canonicalLeaf f parameter lay tree leaf secret)) :
    (candidate = words lay tree leaf ∧ ∀ index, values index = frontier f parameter words lay tree leaf secret index) ∨
      LeafOutputMatch f parameter lay tree leaf secret trace ∨ ChainException f parameter words lay tree leaf secret trace := by
  let endpoints := fun index => evalWithAnswerFn f (recoverChain parameter lay tree leaf index (candidate index) (values index))
  have heval : evalWithAnswerFn f (leafHash parameter lay tree leaf endpoints) = canonicalLeaf f parameter lay tree leaf secret := by
    simpa only [otsLeaf, evalWithAnswerFn_bind, hencode, evalWithAnswerFn_sequenceFin, evalWithAnswerFn_pure,
      Option.some.injEq, endpoints] using hleaf
  by_cases hp : leafPayload endpoints = leafPayload (fun index => honestChain f parameter lay tree leaf index (secret index) (chainLength - 1))
  · have hs := otsLeaf_chain_classification f parameter words lay tree leaf secret message counter values candidate trace hvalid hencode hrun
      (fun index => congrFun (TargetSum.leafPayload_injective hp) index)
    exact hs.imp_right Or.inr
  · refine Or.inr (Or.inl ⟨leafPayload endpoints, leafPayload_mem_canonicalPayloadInputs endpoints, hp, ?_, ?_⟩)
    · apply hrun
      exact otsLeaf_leaf_query_mem f parameter lay tree leaf message counter values candidate hencode
    · simpa only [leafHash, eval_tweakableHash] using heval

end SphincsSecurity.Concrete.OtsVerifierWitness
