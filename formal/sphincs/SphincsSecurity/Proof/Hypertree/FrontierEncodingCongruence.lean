import SphincsSecurity.Proof.Ots.EncodingOracleSplit
import SphincsSecurity.Proof.Hypertree.FrontierSigningOracleCongruence
namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] canonicalEncodingInputs frontierTreeNode referenceEncodingSearch boundaryEval publicDigestLoop

def AgreeOutsideEncoding (parameter : PublicParameter) (f g : QueryImpl HashSpec Id) : Prop :=
  ∀ input, input ∉ canonicalEncodingInputs parameter → f input = g input

theorem AgreeOutsideEncoding.domain {parameter : PublicParameter} {f g : QueryImpl HashSpec Id}
    (h : AgreeOutsideEncoding parameter f g) (domain : HashDomain)
    (htag : (hashDomainFields domain).tag ≠ 4#8) (payload : HashInput) :
    f (tweakableHashInput parameter domain payload) = g (tweakableHashInput parameter domain payload) := by
  apply h
  intro hinput
  rw [canonicalEncodingInputs] at hinput
  simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_image] at hinput
  obtain ⟨position, pair, heq⟩ := hinput
  exact htag (FtsProbeSimulation.tweakableHashInput_tag_eq parameter domain
    (.encoding position.lay position.tree position.leafIdx) payload _ heq.symm)

namespace AgreeOutsideEncoding

variable {parameter : PublicParameter} {f g : QueryImpl HashSpec Id}
  (h : AgreeOutsideEncoding parameter f g)

include h

theorem frontierTreeNode (lay : Layer) (tree : TreeIndex) (words : LeafIndex → Encoding)
    (frontier : LeafIndex → ChainIndex → Digest) (level nodeIdx : Nat) :
    evalWithAnswerFn f (Concrete.frontierTreeNode parameter lay tree words frontier level nodeIdx) =
      evalWithAnswerFn g (Concrete.frontierTreeNode parameter lay tree words frontier level nodeIdx) := by
  apply eval_frontierTreeNode_congr
  · intro leaf chainIdx step _ input
    exact congrArg truncateHash (h.domain (.chain lay tree leaf chainIdx step) (by simp only [hashDomainFields]; decide) (digestBytes input))
  · intro leaf payload
    exact congrArg truncateHash (h.domain (.leaf lay tree leaf) (by simp only [hashDomainFields]; decide) payload)
  · intro level nodeIdx payload
    exact congrArg truncateHash (h.domain (.node lay tree level nodeIdx) (by simp only [hashDomainFields]; decide) payload)

theorem frontierTreePath (lay : Layer) (tree : TreeIndex) (words : LeafIndex → Encoding)
    (frontier : LeafIndex → ChainIndex → Digest) (leaf : LeafIndex) :
    evalWithAnswerFn f (Concrete.frontierTreePath parameter lay tree words frontier leaf) =
      evalWithAnswerFn g (Concrete.frontierTreePath parameter lay tree words frontier leaf) := by
  simp only [Concrete.frontierTreePath, evalWithAnswerFn_sequenceFin]
  funext level
  split_ifs
  · exact h.frontierTreeNode _ _ _ _ _ _
  · rfl

theorem ftsNode (index : Index) (tree : FtsTree) (secret : FtsLeaf → Digest) (level nodeIdx : Nat) :
    evalWithAnswerFn f (Concrete.ftsNode parameter index tree secret level nodeIdx) =
      evalWithAnswerFn g (Concrete.ftsNode parameter index tree secret level nodeIdx) := by
  induction level generalizing nodeIdx with
  | zero =>
      simp only [ftsNode_zero_eq, ftsLeafHash, eval_tweakableHash]
      exact congrArg truncateHash (h.domain (.ftsLeaf index tree _) (by simp only [hashDomainFields]; decide) _)
  | succ level ih =>
      simp only [ftsNode_succ_eq, evalWithAnswerFn_bind, ih, eval_tweakableHash]
      exact congrArg truncateHash (h.domain (.ftsNode index tree (level + 1) nodeIdx) (by simp only [hashDomainFields]; decide) _)

theorem ftsOpen (index : Index) (leaves : IndexGroup → FtsLeaf) (secret : FtsTree → FtsLeaf → Digest) :
    evalWithAnswerFn f (Concrete.ftsOpen parameter index leaves secret) =
      evalWithAnswerFn g (Concrete.ftsOpen parameter index leaves secret) := by
  simp only [Concrete.ftsOpen, evalWithAnswerFn_sequenceFin, h.ftsNode]

theorem publicDigestLoop (root : Digest) (message : Message) (attempts : Nat) :
    fixedBoundaryRun parameter f (Concrete.publicDigestLoop parameter root message attempts) =
      fixedBoundaryRun parameter g (Concrete.publicDigestLoop parameter root message attempts) := by
  have hattempt (randomness : Randomness) :
      boundaryEval parameter f (publicSignAttempt parameter root message randomness) =
        boundaryEval parameter g (publicSignAttempt parameter root message randomness) := by
    have hinput := h.domain .message (by simp only [hashDomainFields]; decide) (messageDigestPayload root message randomness)
    simp [publicSignAttempt, messageDigest, oracleHash, boundaryEval, QueryImpl.withTrace_apply, hinput]
  induction attempts with
  | zero => simp only [Concrete.publicDigestLoop, fixedBoundaryRun_pure]
  | succ attempts ih =>
      rw [Concrete.publicDigestLoop]
      apply fixedBoundaryRun_bind_congr
      · exact fixedBoundaryRun_lift_prob_eq parameter f g sampleRandomness
      · intro randomness
        apply fixedBoundaryRun_bind_congr
        · rw [fixedBoundaryRun_lift_hash, fixedBoundaryRun_lift_hash, hattempt]
        · intro attempt
          cases attempt with
          | none => exact ih
          | some selected => rfl

theorem frontierSignLayer (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (words : OtsReferenceWords) (frontier : OtsFrontierValues) (index : Index) (lay : Layer)
    (hsearch : frontierLayerSearch parameter f ftsSecret words frontier index lay =
      frontierLayerSearch parameter g ftsSecret words frontier index lay) :
    Concrete.frontierSignLayer parameter f ftsSecret words frontier index lay =
      Concrete.frontierSignLayer parameter g ftsSecret words frontier index lay := by
  simp only [Concrete.frontierSignLayer, hsearch, h.frontierTreePath]

theorem frontierSignAfterDigest (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (words : OtsReferenceWords) (frontier : OtsFrontierValues)
    (hsearch : ∀ index lay, frontierLayerSearch parameter f ftsSecret words frontier index lay =
      frontierLayerSearch parameter g ftsSecret words frontier index lay)
    (randomness : Randomness) (index : Index) (leaves : IndexGroup → FtsLeaf) :
    Concrete.frontierSignAfterDigest parameter f ftsSecret words frontier randomness index leaves =
      Concrete.frontierSignAfterDigest parameter g ftsSecret words frontier randomness index leaves := by
  simp only [Concrete.frontierSignAfterDigest, h.frontierSignLayer ftsSecret words frontier _ _ (hsearch _ _),
    h.ftsOpen]

theorem frontierSigningRun (root : Digest) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (words : OtsReferenceWords) (frontier : OtsFrontierValues)
    (hsearch : ∀ index lay, frontierLayerSearch parameter f ftsSecret words frontier index lay =
      frontierLayerSearch parameter g ftsSecret words frontier index lay) (message : Message) :
    Concrete.frontierSigningRun parameter root f ftsSecret words frontier message =
      Concrete.frontierSigningRun parameter root g ftsSecret words frontier message := by
  simp only [Concrete.frontierSigningRun, frontierSigningRecord, h.publicDigestLoop,
    h.frontierSignAfterDigest ftsSecret words frontier hsearch]

theorem frontierRoot (words : OtsReferenceWords) (frontier : OtsFrontierValues) :
    Concrete.frontierRoot parameter f words frontier = Concrete.frontierRoot parameter g words frontier :=
  h.frontierTreeNode _ _ _ _ _ _

end AgreeOutsideEncoding

end SphincsSecurity.Concrete
