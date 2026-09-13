import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Hypertree.FrontierGameProjection
import SphincsSecurity.Proof.Hypertree.FrontierOracleMask
namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] frontierTreeNode referenceEncodingSearch boundaryEval

variable (parameter : PublicParameter) (words : OtsReferenceWords)
  (f g : QueryImpl HashSpec Id) (h : AgreeOutsideOtsPrefixes parameter words f g)

include h

theorem eval_frontierTreeNode_eq_of_agree (lay : Layer) (tree : TreeIndex)
    (frontier : LeafIndex → ChainIndex → Digest) (level nodeIdx : Nat) :
    evalWithAnswerFn f (frontierTreeNode parameter lay tree (words lay tree) frontier level nodeIdx) =
      evalWithAnswerFn g (frontierTreeNode parameter lay tree (words lay tree) frontier level nodeIdx) := by
  apply eval_frontierTreeNode_congr
  · intro leaf chainIdx step hstep input
    exact congrArg truncateHash (h.chain lay tree leaf chainIdx step hstep (digestBytes input))
  · intro leaf payload
    exact congrArg truncateHash (h.other (.leaf lay tree leaf) (by simp only [hashDomainFields]; decide) payload)
  · intro level nodeIdx payload
    exact congrArg truncateHash (h.other (.node lay tree level nodeIdx) (by simp only [hashDomainFields]; decide) payload)

theorem eval_frontierTreePath_eq_of_agree (lay : Layer) (tree : TreeIndex)
    (frontier : LeafIndex → ChainIndex → Digest) (leaf : LeafIndex) :
    evalWithAnswerFn f (frontierTreePath parameter lay tree (words lay tree) frontier leaf) =
      evalWithAnswerFn g (frontierTreePath parameter lay tree (words lay tree) frontier leaf) := by
  simp only [frontierTreePath, evalWithAnswerFn_sequenceFin]
  funext level
  split_ifs
  · exact eval_frontierTreeNode_eq_of_agree parameter words f g h lay tree frontier _ _
  · rfl

theorem eval_ftsNode_eq_of_agree (index : Index) (tree : FtsTree) (secret : FtsLeaf → Digest)
    (level nodeIdx : Nat) :
    evalWithAnswerFn f (ftsNode parameter index tree secret level nodeIdx) =
      evalWithAnswerFn g (ftsNode parameter index tree secret level nodeIdx) := by
  induction level generalizing nodeIdx with
  | zero =>
      simp only [ftsNode_zero_eq, ftsLeafHash, eval_tweakableHash]
      exact congrArg truncateHash (h.other (.ftsLeaf index tree _) (by simp only [hashDomainFields]; decide) _)
  | succ level ih =>
      simp only [ftsNode_succ_eq, evalWithAnswerFn_bind, ih, eval_tweakableHash]
      exact congrArg truncateHash (h.other (.ftsNode index tree (level + 1) nodeIdx) (by simp only [hashDomainFields]; decide) _)

theorem eval_ftsKey_eq_of_agree (index : Index) (secret : FtsTree → FtsLeaf → Digest) :
    evalWithAnswerFn f (ftsKey parameter index secret) = evalWithAnswerFn g (ftsKey parameter index secret) := by
  simp only [ftsKey, evalWithAnswerFn_bind, evalWithAnswerFn_sequenceFin,
    eval_ftsNode_eq_of_agree parameter words f g h, eval_tweakableHash]
  exact congrArg truncateHash (h.other (.ftsRoots index) (by simp only [hashDomainFields]; decide) _)

theorem eval_ftsOpen_eq_of_agree (index : Index) (leaves : IndexGroup → FtsLeaf)
    (secret : FtsTree → FtsLeaf → Digest) :
    evalWithAnswerFn f (ftsOpen parameter index leaves secret) =
      evalWithAnswerFn g (ftsOpen parameter index leaves secret) := by
  simp only [ftsOpen, evalWithAnswerFn_sequenceFin, eval_ftsNode_eq_of_agree parameter words f g h]

theorem eval_frontierLayerMessage_eq_of_agree (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (frontier : OtsFrontierValues) (index : Index) (lay : Layer) :
    evalWithAnswerFn f (frontierLayerMessage parameter ftsSecret words frontier index lay) =
      evalWithAnswerFn g (frontierLayerMessage parameter ftsSecret words frontier index lay) := by
  unfold frontierLayerMessage
  split_ifs
  · exact eval_frontierTreeNode_eq_of_agree parameter words f g h _ _ _ _ _
  · exact eval_ftsKey_eq_of_agree parameter words f g h _ _

theorem eval_encode_eq_of_agree (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex)
    (message : Digest) (counter : Counter) :
    evalWithAnswerFn f (encode parameter lay tree leaf message counter) =
      evalWithAnswerFn g (encode parameter lay tree leaf message counter) := by
  simp only [encode, evalWithAnswerFn_bind, evalWithAnswerFn_pure, eval_tweakableHash,
    h.other (.encoding lay tree leaf) (by simp only [hashDomainFields]; decide)]

theorem referenceEncodingSearch_eq_of_agree (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex)
    (message : Digest) (attempts start : Nat) :
    referenceEncodingSearch parameter f lay tree leaf message attempts start =
      referenceEncodingSearch parameter g lay tree leaf message attempts start := by
  induction attempts generalizing start with
  | zero => simp only [referenceEncodingSearch]
  | succ attempts ih =>
      simp only [referenceEncodingSearch, eval_encode_eq_of_agree parameter words f g h, ih]

theorem frontierLayerSearch_eq_of_agree (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (frontier : OtsFrontierValues) (index : Index) (lay : Layer) :
    frontierLayerSearch parameter f ftsSecret words frontier index lay =
      frontierLayerSearch parameter g ftsSecret words frontier index lay := by
  rw [frontierLayerSearch, frontierLayerSearch,
    eval_frontierLayerMessage_eq_of_agree parameter words f g h,
    referenceEncodingSearch_eq_of_agree parameter words f g h]

theorem frontierSignLayer_eq_of_agree (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (frontier : OtsFrontierValues) (index : Index) (lay : Layer) :
    frontierSignLayer parameter f ftsSecret words frontier index lay =
      frontierSignLayer parameter g ftsSecret words frontier index lay := by
  simp only [frontierSignLayer, frontierLayerSearch_eq_of_agree parameter words f g h,
    eval_frontierTreePath_eq_of_agree parameter words f g h]

theorem frontierSignAfterDigest_eq_of_agree (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (frontier : OtsFrontierValues) (randomness : Randomness) (index : Index) (leaves : IndexGroup → FtsLeaf) :
    frontierSignAfterDigest parameter f ftsSecret words frontier randomness index leaves =
      frontierSignAfterDigest parameter g ftsSecret words frontier randomness index leaves := by
  simp only [frontierSignAfterDigest, frontierSignLayer_eq_of_agree parameter words f g h,
    eval_ftsOpen_eq_of_agree parameter words f g h]

theorem frontierRoot_eq_of_agree (frontier : OtsFrontierValues) :
    frontierRoot parameter f words frontier = frontierRoot parameter g words frontier :=
  eval_frontierTreeNode_eq_of_agree parameter words f g h _ _ _ _ _

end SphincsSecurity.Concrete
