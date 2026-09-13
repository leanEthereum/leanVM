import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Residual.RetainedResidualContext
namespace SphincsSecurity.Concrete.RetainedResidual

open _root_.OracleComp OracleSpec CanonicalProbeRouting
attribute [local instance] Classical.propDecidable
attribute [local irreducible] hashInputs canonicalEncodingInputs canonicalGraphInputs instFintypePosition
  signDigestLoop signAfterDigest sequenceFin chainWalk
set_option backward.isDefEq.respectTransparency false

theorem Context.graph_eq {inputs : Finset HashInput} (context : Context inputs) :
    canonicalGraphLabels context.key.parameter context.key.otsSecret context.key.ftsSecret context.oracle = context.graph :=
  canonicalGraphLabels_programmedHash _ _ _ _ _

theorem Context.actual_graph {inputs : Finset HashInput} (context : Context inputs) (position : Position)
    (hbound : position.TreeBound) :
    context.actual (.graph position) = honestValue context.oracle context.key.parameter context.key.otsSecret context.key.ftsSecret position := by
  change truncateHash (context.graph position) = _
  rw [← context.graph_eq, canonicalGraphLabels_eq_honest _ _ _ _ position hbound]
  rfl

theorem Context.input_honest {inputs : Finset HashInput} (context : Context inputs) (position : Position)
    (hbound : position.TreeBound) :
    inputOf context.key.parameter context.actual position =
      honestInput context.oracle context.key.parameter context.key.otsSecret context.key.ftsSecret position := by
  rw [Context.actual, inputOf_canonical]
  apply canonicalGraphInput_eq_honest _ _ _ _ position (hbound.valid position)
  intro child hchild
  exact context.actual_graph child (hbound.child hchild)

theorem Compatible.not_payload_collision {inputs : Finset HashInput} {context : Context inputs} {memory : Memory}
    (hcompatible : Compatible context memory) (position : Position) (hbound : position.TreeBound) (payload : HashInput)
    (hne : payload ≠ honestPayload context.oracle context.key.parameter context.key.otsSecret context.key.ftsSecret position)
    (hcached : memory.external.cache (tweakableHashInput context.key.parameter position.domain payload) ≠ none)
    (hvalue : truncateHash (context.oracle (tweakableHashInput context.key.parameter position.domain payload)) =
      honestValue context.oracle context.key.parameter context.key.otsSecret context.key.ftsSecret position) : False := by
  obtain ⟨answer, hanswer⟩ := Option.ne_none_iff_exists'.mp hcached
  apply hcompatible.structural _ answer hanswer
  refine ⟨position, ⟨payload, rfl⟩, Or.inr ⟨?_, ?_⟩⟩
  · rw [context.input_honest position hbound]
    intro heq
    exact hne (tweakableHashInput_injective context.key.parameter position.domain_inRange position.domain_inRange heq).2
  · rw [hcompatible.cached _ _ hanswer, hvalue, context.actual_graph position hbound]

private theorem foldPosition_bound (height level index : Nat) (hlevel : level < height) (hindex : index < 2 ^ height) :
    2 ^ (level + 1) * (index / 2 ^ (level + 1) + 1) ≤ 2 ^ height := by
  have hpow : (2 : Nat) ^ height = 2 ^ (level + 1) * 2 ^ (height - (level + 1)) := by
    rw [← pow_add, Nat.add_sub_of_le (Nat.succ_le_of_lt hlevel)]
  have hdiv : index / 2 ^ (level + 1) < 2 ^ (height - (level + 1)) := by
    apply (Nat.div_lt_iff_lt_mul (by positivity)).mpr
    simpa only [hpow, Nat.mul_comm] using hindex
  calc
    _ ≤ 2 ^ (level + 1) * 2 ^ (height - (level + 1)) := Nat.mul_le_mul_left _ (Nat.succ_le_of_lt hdiv)
    _ = _ := hpow.symm

theorem Compatible.layer_honest {inputs : Finset HashInput} {context : Context inputs} {memory : Memory}
    (hcompatible : Compatible context memory) (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex)
    (hleafIdx : leafIdx.val < 2 ^ layerHeight lay) (message : Digest) (counter : Counter)
    (values : ChainIndex → Digest) (path : Nat → Digest) (leafValue : Digest)
    (hleaf : evalWithAnswerFn context.oracle
      (otsLeaf context.key.parameter lay tree leafIdx message counter values) = some leafValue)
    (hfold : foldValue context.oracle context.key.parameter lay tree leafIdx path leafValue (layerHeight lay) =
      honestNode context.oracle context.key.parameter lay tree (context.key.otsSecret lay tree) (layerHeight lay) 0)
    (hotsRun : CachedRun memory.external.cache context.oracle
      (otsLeaf context.key.parameter lay tree leafIdx message counter values))
    (hfoldRun : CachedRun memory.external.cache context.oracle
      (treeFold context.key.parameter lay tree leafIdx path (layerHeight lay) leafValue)) :
    HonestLayerOpening context.oracle context.key.parameter context.key.otsSecret lay tree leafIdx message counter values path := by
  cases hencode : evalWithAnswerFn context.oracle (encode context.key.parameter lay tree leafIdx message counter) with
  | none =>
      simp only [otsLeaf, evalWithAnswerFn_bind, hencode, evalWithAnswerFn_pure, reduceCtorEq] at hleaf
  | some codeword =>
      rcases treeFold_extract context.oracle context.key.parameter lay tree (context.key.otsSecret lay tree) leafIdx path leafValue
          (layerHeight lay) (by simpa only [Nat.div_eq_of_lt hleafIdx] using hfold) with
        ⟨hleafValue, hpath⟩ | ⟨level, hlevel, hhit⟩
      · have hleafHonest : evalWithAnswerFn context.oracle
            (otsLeaf context.key.parameter lay tree leafIdx message counter values) =
            some (honestNode context.oracle context.key.parameter lay tree (context.key.otsSecret lay tree) 0 leafIdx.val) := by
          rw [hleaf, hleafValue]
        rcases otsLeaf_extract context.oracle context.key.parameter lay tree (context.key.otsSecret lay tree) leafIdx
            message counter values codeword hencode hleafHonest with hvalues | hhit | ⟨chainIdx, offset, hrange, hoffset, hhit⟩
        · exact ⟨codeword, hencode, hvalues, hpath⟩
        · exact (hcompatible.not_payload_collision (.leaf lay tree leafIdx) (by trivial) _ hhit.1
            (hotsRun _ (otsLeaf_leaf_query_mem context.oracle context.key.parameter lay tree leafIdx message counter values codeword hencode))
            (by simpa only [Position.domain, honestValue_leaf] using hhit.2)).elim
        · apply False.elim
          apply hcompatible.not_payload_collision (.chain lay tree leafIdx chainIdx ⟨_, hrange⟩) (by trivial) _
          · simpa only [honestPayload] using fun heq => hhit.1 (digestBytes_injective heq)
          · exact hotsRun _ (otsLeaf_chain_query_mem context.oracle context.key.parameter lay tree leafIdx message counter values
              codeword hencode chainIdx offset hoffset hrange)
          · simpa only [Position.domain, honestValue_chain] using hhit.2
      · have hlevelMax : level < maxLayerHeight := lt_of_lt_of_le hlevel (layerHeight_le lay)
        have hnodeIdx : leafIdx.val / 2 ^ (level + 1) < 2 ^ maxLayerHeight :=
          lt_of_le_of_lt (Nat.div_le_self _ _) leafIdx.isLt
        apply False.elim
        apply hcompatible.not_payload_collision (.node lay tree ⟨level, hlevelMax⟩ ⟨_, hnodeIdx⟩)
          (foldPosition_bound maxLayerHeight level leafIdx.val hlevelMax leafIdx.isLt) _ hhit.1
        · exact hfoldRun _ (treeFold_query_mem context.oracle context.key.parameter lay tree leafIdx path leafValue
            (layerHeight lay) level hlevel)
        · simpa only [Position.domain, honestValue_node] using hhit.2

theorem Compatible.no_hidden_input {inputs : Finset HashInput} {context : Context inputs} {memory : Memory}
    (hcompatible : Compatible context memory) (position : Position)
    (hcached : memory.external.cache (inputOf context.key.parameter context.actual position) ≠ none) :
    ¬HasHiddenChild context.words memory.routing.disclosed position := by
  obtain ⟨answer, hanswer⟩ := Option.ne_none_iff_exists'.mp hcached
  intro hhidden
  exact hcompatible.structural _ _ hanswer ⟨position, ⟨_, rfl⟩, Or.inl ⟨hhidden, rfl⟩⟩

theorem Context.words_valid {inputs : Finset HashInput} (context : Context inputs)
    (hdummy : ∀ lay tree leaf, TargetSum.Valid (context.dummy lay tree leaf)) :
    ∀ lay tree leaf, TargetSum.Valid (context.words lay tree leaf) := by
  rw [Context.words, referencePrefix_words context.key inputs context.encoding context.graph context.auxiliary context.auxiliary_valid]
  exact canonicalReferenceWords_valid context.key context.oracle context.dummy hdummy

theorem Compatible.layer_word {inputs : Finset HashInput} {context : Context inputs} {memory : Memory}
    (hcompatible : Compatible context memory) (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex)
    (message : Digest) (counter : Counter) (values : ChainIndex → Digest) (codeword : Encoding)
    (hword : TargetSum.Valid (context.words lay tree leafIdx))
    (hencode : evalWithAnswerFn context.oracle (encode context.key.parameter lay tree leafIdx message counter) = some codeword)
    (hvalues : ∀ chain, values chain = honestChain context.oracle context.key.parameter lay tree leafIdx chain
      (context.key.otsSecret lay tree leafIdx chain) (codeword chain).val)
    (hrun : CachedRun memory.external.cache context.oracle (otsLeaf context.key.parameter lay tree leafIdx message counter values)) :
    codeword = context.words lay tree leafIdx := by
  apply Eq.symm
  apply TargetSum.eq_of_le_of_valid hword (valid_of_eval_encode_eq_some _ _ _ _ _ _ _ _ hencode)
  intro chain
  by_contra hnot
  have hlt : (codeword chain).val < (context.words lay tree leafIdx chain).val := by omega
  have hrange : (codeword chain).val < chainLength - 1 := by
    have := (context.words lay tree leafIdx chain).isLt
    omega
  let position : Position := .chain lay tree leafIdx chain ⟨(codeword chain).val, hrange⟩
  have hquery := hrun _ (otsLeaf_chain_query_mem context.oracle context.key.parameter lay tree leafIdx message counter values
    codeword hencode chain 0 (by omega) (by omega))
  simp only [Nat.add_zero, walkValue, chainWalk, evalWithAnswerFn_pure] at hquery
  have hinput : inputOf context.key.parameter context.actual position =
      tweakableHashInput context.key.parameter position.domain (digestBytes (values chain)) := by
    rw [context.input_honest position (by trivial)]
    change tweakableHashInput context.key.parameter position.domain
      (digestBytes (honestChain context.oracle context.key.parameter lay tree leafIdx chain
        (context.key.otsSecret lay tree leafIdx chain) (codeword chain).val)) = _
    rw [hvalues chain]
  apply hcompatible.no_hidden_input position (by rw [hinput]; exact hquery)
  refine ⟨CanonicalCoordinate.chainChild lay tree leafIdx chain ⟨_, hrange⟩, ?_, ?_⟩
  · rw [CanonicalCoordinate.slots_chain]
    exact List.mem_singleton_self _
  · exact (CanonicalCoordinate.hidden_chain_child_iff context.words memory.routing.disclosed lay tree leafIdx chain _).mpr hlt

theorem Compatible.layer_reference {inputs : Finset HashInput} {context : Context inputs} {memory : Memory}
    (hcompatible : Compatible context memory) (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex)
    (message : Digest) (counter : Counter) (values : ChainIndex → Digest) (path : Nat → Digest)
    (hword : TargetSum.Valid (context.words lay tree leafIdx))
    (hhonest : HonestLayerOpening context.oracle context.key.parameter context.key.otsSecret lay tree leafIdx message counter values path)
    (hrun : CachedRun memory.external.cache context.oracle (otsLeaf context.key.parameter lay tree leafIdx message counter values)) :
    ∃ selected, context.auxiliary.selections ⟨lay, tree, leafIdx⟩ = some selected ∧
      message = canonicalGraphMessage context.graph ⟨lay, tree, leafIdx⟩ ∧
      counter = BitVec.ofNat counterBits selected.1.val ∧
      (∀ chain, values chain = honestChain context.oracle context.key.parameter lay tree leafIdx chain
        (context.key.otsSecret lay tree leafIdx chain) (context.words lay tree leafIdx chain).val) ∧
      ∀ level, level < layerHeight lay → path level =
        honestNode context.oracle context.key.parameter lay tree (context.key.otsSecret lay tree) level
          (Nat.xor (leafIdx.val / 2 ^ level) 1) := by
  obtain ⟨codeword, hencode, hvalues, hpath⟩ := hhonest
  have hcodeword := hcompatible.layer_word lay tree leafIdx message counter values codeword hword hencode hvalues hrun
  rw [hcodeword] at hencode hvalues
  let position : EncodingPosition := ⟨lay, tree, leafIdx⟩
  let input := tweakableHashInput context.key.parameter position.domain (digestBytes message ++ counterBytes counter)
  have hreference : PublicEncodingMatch.referenceInput context.key.parameter (canonicalGraphMessage context.graph)
      context.auxiliary.selections position = some input := by
    by_contra hnot
    obtain ⟨answer, hanswer⟩ := Option.ne_none_iff_exists'.mp (CachedRun.otsLeaf_encode_cached hrun)
    apply hcompatible.encoding _ _ hanswer
    refine ⟨position, ⟨_, rfl⟩, hnot, ?_⟩
    rw [hcompatible.cached _ _ hanswer]
    exact decode_of_eval_encode_eq_some _ _ _ _ _ _ _ _ hencode
  cases hselected : context.auxiliary.selections position with
  | none => simp only [PublicEncodingMatch.referenceInput, hselected, Option.map_none, reduceCtorEq] at hreference
  | some selected =>
      have hinput : encodingRetryInput context.key.parameter position (canonicalGraphMessage context.graph position) selected.1.val = input := by
        simpa only [PublicEncodingMatch.referenceInput, hselected, Option.map_some, Option.some.injEq] using hreference
      have hpayload := (tweakableHashInput_injective context.key.parameter (by trivial) (by trivial) hinput).2
      obtain ⟨hmessage, hcounter⟩ := List.append_inj hpayload (by simp [digestBytes_length])
      exact ⟨selected, rfl, (digestBytes_injective hmessage).symm, (bytesLE_injective hcounter).symm, hvalues, hpath⟩

theorem Compatible.ftsTree_honest {inputs : Finset HashInput} {context : Context inputs} {memory : Memory}
    (hcompatible : Compatible context memory) (index : Index) (leaves : IndexGroup → FtsLeaf)
    (secrets : FtsTree → Digest) (paths : FtsTree → Fin ftsTreeHeight → Digest) (tree : FtsTree)
    (hfold : ftsFoldValue context.oracle context.key.parameter index tree (leaves (ftsIndexOf tree)) (paths tree)
      (truncateHash (context.oracle (tweakableHashInput context.key.parameter
        (.ftsLeaf index tree (leaves (ftsIndexOf tree))) (digestBytes (secrets tree))))) ftsTreeHeight =
      honestFtsNode context.oracle context.key.parameter index tree (context.key.ftsSecret index tree) ftsTreeHeight 0)
    (hrun : CachedRun memory.external.cache context.oracle (ftsRecover context.key.parameter index leaves secrets paths)) :
    secrets tree = context.key.ftsSecret index tree (leaves (ftsIndexOf tree)) ∧
      ∀ level (hlevel : level < ftsTreeHeight), paths tree ⟨level, hlevel⟩ =
        honestFtsNode context.oracle context.key.parameter index tree (context.key.ftsSecret index tree) level
          (Nat.xor ((leaves (ftsIndexOf tree)).val / 2 ^ level) 1) := by
  let leafIdx := leaves (ftsIndexOf tree)
  let leafValue := truncateHash (context.oracle (tweakableHashInput context.key.parameter
    (.ftsLeaf index tree leafIdx) (digestBytes (secrets tree))))
  have hroot : leafIdx.val / 2 ^ ftsTreeHeight = 0 := Nat.div_eq_of_lt leafIdx.isLt
  rcases ftsFold_extract context.oracle context.key.parameter index tree (context.key.ftsSecret index tree)
      leafIdx (paths tree) leafValue ftsTreeHeight (le_refl _) (by simpa only [leafIdx, leafValue, hroot] using hfold) with
    ⟨hleafValue, hpath⟩ | ⟨level, hlevel, hhit⟩
  · rcases ftsLeaf_extract context.oracle context.key.parameter index tree (context.key.ftsSecret index tree)
      leafIdx (secrets tree) hleafValue with hsecret | hhit
    · refine ⟨hsecret, ?_⟩
      intro level hlevel
      simpa only [ftsSibling, dif_pos hlevel, leafIdx] using hpath level hlevel
    · apply False.elim
      apply hcompatible.not_payload_collision (.ftsLeaf index tree leafIdx) (by trivial) _
      · simpa only [honestPayload] using fun heq => hhit.1 (digestBytes_injective heq)
      · exact hrun _ (ftsRecover_leaf_query_mem context.oracle context.key.parameter index leaves secrets paths tree)
      · simpa only [Position.domain, honestValue_ftsLeaf] using hhit.2
  · have hnodeIdx : leafIdx.val / 2 ^ (level + 1) < 2 ^ ftsTreeHeight :=
      lt_of_le_of_lt (Nat.div_le_self _ _) leafIdx.isLt
    apply False.elim
    apply hcompatible.not_payload_collision (.ftsNode index tree ⟨level, hlevel⟩ ⟨_, hnodeIdx⟩)
      (foldPosition_bound ftsTreeHeight level leafIdx.val hlevel leafIdx.isLt) _ hhit.1
    · exact hrun _ (ftsRecover_fold_query_mem context.oracle context.key.parameter index leaves secrets paths tree level hlevel)
    · simpa only [Position.domain, honestValue_ftsNode] using hhit.2

theorem Compatible.ftsRecover_honest {inputs : Finset HashInput} {context : Context inputs} {memory : Memory}
    (hcompatible : Compatible context memory) (index : Index) (leaves : IndexGroup → FtsLeaf)
    (secrets : FtsTree → Digest) (paths : FtsTree → Fin ftsTreeHeight → Digest)
    (hrecover : evalWithAnswerFn context.oracle (ftsRecover context.key.parameter index leaves secrets paths) =
      honestFtsKey context.oracle context.key.parameter index (context.key.ftsSecret index))
    (hrun : CachedRun memory.external.cache context.oracle (ftsRecover context.key.parameter index leaves secrets paths)) :
    ∀ tree, secrets tree = context.key.ftsSecret index tree (leaves (ftsIndexOf tree)) ∧
      ∀ level (hlevel : level < ftsTreeHeight), paths tree ⟨level, hlevel⟩ =
        honestFtsNode context.oracle context.key.parameter index tree (context.key.ftsSecret index tree) level
          (Nat.xor ((leaves (ftsIndexOf tree)).val / 2 ^ level) 1) := by
  let roots : FtsTree → Digest := fun tree => evalWithAnswerFn context.oracle
    (ftsFold context.key.parameter index tree (leaves (ftsIndexOf tree)) (paths tree) ftsTreeHeight
      (evalWithAnswerFn context.oracle (ftsLeafHash context.key.parameter index tree (leaves (ftsIndexOf tree)) (secrets tree))))
  by_cases hpayload : ftsRootsPayload roots =
      honestPayload context.oracle context.key.parameter context.key.otsSecret context.key.ftsSecret (.ftsRoots index)
  · have hrootValues : roots = fun tree =>
        honestFtsNode context.oracle context.key.parameter index tree (context.key.ftsSecret index tree) ftsTreeHeight 0 := by
      apply TargetSum.ftsRootsPayload_injective
      simpa only [roots, honestPayload] using hpayload
    intro tree
    apply hcompatible.ftsTree_honest index leaves secrets paths tree _ hrun
    have := congrFun hrootValues tree
    simpa only [roots, evalWithAnswerFn_bind, ftsLeafHash, eval_tweakableHash, ftsFoldValue] using this
  · apply False.elim
    apply hcompatible.not_payload_collision (.ftsRoots index) (by trivial) _ hpayload
    · apply hrun
      have hmem := ftsRecover_roots_query_mem context.oracle context.key.parameter index leaves secrets paths
      convert hmem using 1
      all_goals simp [roots, Position.domain]
    · rw [honestValue_ftsRoots]
      simp only [ftsRecover, evalWithAnswerFn_bind, evalWithAnswerFn_sequenceFin, eval_tweakableHash] at hrecover
      change truncateHash (context.oracle (tweakableHashInput context.key.parameter (.ftsRoots index)
        (ftsRootsPayload roots))) = _
      dsimp only [roots]
      simpa only [evalWithAnswerFn_bind] using hrecover

theorem Compatible.ftsRecover_disclosed {inputs : Finset HashInput} {context : Context inputs} {memory : Memory}
    (hcompatible : Compatible context memory) (index : Index) (leaves : IndexGroup → FtsLeaf)
    (secrets : FtsTree → Digest) (paths : FtsTree → Fin ftsTreeHeight → Digest)
    (hrecover : evalWithAnswerFn context.oracle (ftsRecover context.key.parameter index leaves secrets paths) =
      honestFtsKey context.oracle context.key.parameter index (context.key.ftsSecret index))
    (hrun : CachedRun memory.external.cache context.oracle (ftsRecover context.key.parameter index leaves secrets paths)) :
    ∀ tree, memory.routing.disclosed index tree (leaves (ftsIndexOf tree)) := by
  have hhonest := hcompatible.ftsRecover_honest index leaves secrets paths hrecover hrun
  intro tree
  by_contra hhidden
  apply hcompatible.no_hidden_input (.ftsLeaf index tree (leaves (ftsIndexOf tree)))
  · rw [context.input_honest _ (by trivial)]
    change memory.external.cache (tweakableHashInput context.key.parameter (.ftsLeaf index tree (leaves (ftsIndexOf tree)))
      (digestBytes (context.key.ftsSecret index tree (leaves (ftsIndexOf tree))))) ≠ none
    rw [← (hhonest tree).1]
    exact hrun _ (ftsRecover_leaf_query_mem context.oracle context.key.parameter index leaves secrets paths tree)
  · exact ⟨.ftsStart index tree (leaves (ftsIndexOf tree)), List.mem_singleton_self _, hhidden⟩

theorem Context.layer_message {inputs : Finset HashInput} (context : Context inputs) (index : Index) (lay : Layer) :
    canonicalGraphMessage context.graph ⟨lay, treeIndexAt index lay, leafIndexAt index lay⟩ =
      evalWithAnswerFn context.oracle (layerMessage context.key index lay) := by
  rw [← context.graph_eq, canonicalGraphMessage_eq, layerMessage_referenceIndex]

end SphincsSecurity.Concrete.RetainedResidual
