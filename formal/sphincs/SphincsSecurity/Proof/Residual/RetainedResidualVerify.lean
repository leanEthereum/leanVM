import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Residual.RetainedResidualRecovery
namespace SphincsSecurity.Concrete.RetainedResidual

open _root_.OracleComp OracleSpec CanonicalProbeRouting
attribute [local instance] Classical.propDecidable
attribute [local irreducible] hashInputs canonicalEncodingInputs canonicalGraphInputs instFintypePosition
  signDigestLoop signAfterDigest sequenceFin chainWalk
set_option backward.isDefEq.respectTransparency false

theorem Context.root_value {inputs : Finset HashInput} (context : Context inputs) :
    canonicalGraphRoot context.graph = honestNode context.oracle context.key.parameter topLayer rootTree
      (context.key.otsSecret topLayer rootTree) (layerHeight topLayer) 0 := by
  rw [← context.graph_eq, canonicalGraphLabels_root]
  rfl

theorem Compatible.layer_frame_reference {inputs : Finset HashInput} {context : Context inputs} {memory : Memory}
    (hcompatible : Compatible context memory) (index : Index) (signature : Signature) (lay : Layer)
    (message target leafValue : Digest)
    (hword : TargetSum.Valid (context.words lay (treeIndexAt index lay) (leafIndexAt index lay)))
    (hframe : LayerFrame context.oracle memory.external.cache context.key.parameter index signature lay message target leafValue)
    (hfold : foldValue context.oracle context.key.parameter lay (treeIndexAt index lay) (leafIndexAt index lay)
      (signaturePath signature lay) leafValue (layerHeight lay) =
      honestNode context.oracle context.key.parameter lay (treeIndexAt index lay)
        (context.key.otsSecret lay (treeIndexAt index lay)) (layerHeight lay) 0) :
    message = evalWithAnswerFn context.oracle (layerMessage context.key index lay) ∧
      HonestLayerOpening context.oracle context.key.parameter context.key.otsSecret lay
        (treeIndexAt index lay) (leafIndexAt index lay) (evalWithAnswerFn context.oracle (layerMessage context.key index lay))
        (signature.counter lay) (signature.chainValue lay) (signaturePath signature lay) ∧
      CachedRun memory.external.cache context.oracle (otsLeaf context.key.parameter lay (treeIndexAt index lay)
        (leafIndexAt index lay) (evalWithAnswerFn context.oracle (layerMessage context.key index lay))
        (signature.counter lay) (signature.chainValue lay)) := by
  have hhonest := hcompatible.layer_honest lay (treeIndexAt index lay) (leafIndexAt index lay)
    (leafIndexAt_lt index lay) message (signature.counter lay) (signature.chainValue lay) (signaturePath signature lay)
    leafValue hframe.1 hfold hframe.2.2.1 hframe.2.2.2.1
  obtain ⟨_, _, hmessage, _⟩ := hcompatible.layer_reference lay (treeIndexAt index lay) (leafIndexAt index lay)
    message (signature.counter lay) (signature.chainValue lay) (signaturePath signature lay) hword hhonest hframe.2.2.1
  have heq := hmessage.trans (context.layer_message index lay)
  refine ⟨heq, ?_⟩
  rw [← heq]
  exact ⟨hhonest, hframe.2.2.1⟩

theorem Compatible.hypertree_honest {inputs : Finset HashInput} {context : Context inputs} {memory : Memory}
    (hcompatible : Compatible context memory) (hdummy : ∀ lay tree leaf, TargetSum.Valid (context.dummy lay tree leaf))
    (hroot : context.key.root = canonicalGraphRoot context.graph) (index : Index) (leaves : IndexGroup → FtsLeaf)
    (signature : Signature)
    (hverify : evalWithAnswerFn context.oracle
      (verifyLayers context.key.parameter index signature numLayers
        (evalWithAnswerFn context.oracle (ftsRecover context.key.parameter index leaves signature.ftsSecret signature.ftsPath))) =
      some context.key.root)
    (hlayersRun : CachedRun memory.external.cache context.oracle
      (verifyLayers context.key.parameter index signature numLayers
        (evalWithAnswerFn context.oracle (ftsRecover context.key.parameter index leaves signature.ftsSecret signature.ftsPath))))
    (hftsRun : CachedRun memory.external.cache context.oracle
      (ftsRecover context.key.parameter index leaves signature.ftsSecret signature.ftsPath)) :
    FullyHonestOpening context.oracle memory.external.cache context.key index leaves signature ∧
      ∀ tree, memory.routing.disclosed index tree (leaves (ftsIndexOf tree)) := by
  let ftsPublicKey := evalWithAnswerFn context.oracle
    (ftsRecover context.key.parameter index leaves signature.ftsSecret signature.ftsPath)
  obtain ⟨bottomLeaf, hbottom, middleLeaf, hmiddle, topLeaf, htop⟩ :=
    hypertreeRun_of_verify index signature ftsPublicKey context.key.root hverify hlayersRun
  let middleMessage := foldValue context.oracle context.key.parameter bottomLayer
    (treeIndexAt index bottomLayer) (leafIndexAt index bottomLayer)
    (signaturePath signature bottomLayer) bottomLeaf (layerHeight bottomLayer)
  let topMessage := foldValue context.oracle context.key.parameter middleLayer
    (treeIndexAt index middleLayer) (leafIndexAt index middleLayer)
    (signaturePath signature middleLayer) middleLeaf (layerHeight middleLayer)
  have htopFold : foldValue context.oracle context.key.parameter topLayer
      (treeIndexAt index topLayer) (leafIndexAt index topLayer) (signaturePath signature topLayer) topLeaf
      (layerHeight topLayer) = context.key.root := by
    simpa only [topLayer, verifyLayers_zero_eq, evalWithAnswerFn_pure, Option.some.injEq] using htop.2.1
  have htree : treeIndexAt index topLayer = rootTree := Fin.ext (treeIndexAt_topLayer index)
  have htopRoot : foldValue context.oracle context.key.parameter topLayer
      (treeIndexAt index topLayer) (leafIndexAt index topLayer) (signaturePath signature topLayer) topLeaf
      (layerHeight topLayer) = honestNode context.oracle context.key.parameter topLayer (treeIndexAt index topLayer)
        (context.key.otsSecret topLayer (treeIndexAt index topLayer)) (layerHeight topLayer) 0 := by
    rw [htopFold, hroot, context.root_value, htree]
  have htopOpening := hcompatible.layer_frame_reference index signature topLayer topMessage context.key.root topLeaf
    (context.words_valid hdummy _ _ _) htop htopRoot
  have hmiddleRoot := exact_top_message_eq_middle_root context.oracle context.key index index topMessage
    rfl rfl htopOpening.1.symm
  have hmiddleOpening := hcompatible.layer_frame_reference index signature middleLayer middleMessage context.key.root middleLeaf
    (context.words_valid hdummy _ _ _) hmiddle hmiddleRoot
  have hbottomRoot := exact_middle_message_eq_bottom_root context.oracle context.key index index middleMessage
    rfl rfl hmiddleOpening.1.symm
  have hbottomOpening := hcompatible.layer_frame_reference index signature bottomLayer ftsPublicKey context.key.root bottomLeaf
    (context.words_valid hdummy _ _ _) hbottom hbottomRoot
  have hftsKey := exact_bottom_message_eq_fts_key context.oracle context.key index index ftsPublicKey
    rfl rfl hbottomOpening.1.symm
  have hftsHonest := hcompatible.ftsRecover_honest index leaves signature.ftsSecret signature.ftsPath hftsKey hftsRun
  refine ⟨⟨?_, hftsHonest, hftsRun, ?_⟩,
    hcompatible.ftsRecover_disclosed index leaves signature.ftsSecret signature.ftsPath hftsKey hftsRun⟩
  · intro lay
    fin_cases lay
    · simpa only [topLayer] using htopOpening.2
    · simpa only [middleLayer] using hmiddleOpening.2
    · simpa only [bottomLayer, numLayers] using hbottomOpening.2
  · intro lay
    have hverifier (position : Layer) (message : Digest)
        (hposition : position = bottomLayer ∧ message = ftsPublicKey ∨
          position = middleLayer ∧ message = middleMessage ∨ position = topLayer ∧ message = topMessage) :
        VerifierLayerMessage context.oracle context.key.parameter index leaves signature position message :=
      ⟨bottomLeaf, hbottom.1, middleLeaf, hmiddle.1, hposition⟩
    fin_cases lay
    · rw [show (⟨0, by decide⟩ : Layer) = topLayer from rfl, ← htopOpening.1]
      exact hverifier _ _ (Or.inr (Or.inr ⟨rfl, rfl⟩))
    · rw [show (⟨1, by decide⟩ : Layer) = middleLayer from rfl, ← hmiddleOpening.1]
      exact hverifier _ _ (Or.inr (Or.inl ⟨rfl, rfl⟩))
    · rw [show (⟨2, by decide⟩ : Layer) = bottomLayer from rfl, ← hbottomOpening.1]
      exact hverifier _ _ (Or.inl ⟨rfl, rfl⟩)

theorem Compatible.verify_honest {inputs : Finset HashInput} {context : Context inputs} {memory : Memory}
    (hcompatible : Compatible context memory) (hdummy : ∀ lay tree leaf, TargetSum.Valid (context.dummy lay tree leaf))
    (hroot : context.key.root = canonicalGraphRoot context.graph) (message : Message) (signature : Signature)
    (hverify : evalWithAnswerFn context.oracle (verify ⟨context.key.root, context.key.parameter⟩ message signature) = true)
    (hrun : CachedRun memory.external.cache context.oracle (verify ⟨context.key.root, context.key.parameter⟩ message signature)) :
    ∃ digest, evalWithAnswerFn context.oracle (messageDigest context.key.parameter context.key.root message signature.randomness) = digest ∧
      CachedRun memory.external.cache context.oracle (messageDigest context.key.parameter context.key.root message signature.randomness) ∧
      Admissible digest ∧
      FullyHonestOpening context.oracle memory.external.cache context.key (digestIndex digest) (digestLeaves digest) signature ∧
      ∀ tree, memory.routing.disclosed (digestIndex digest) tree (digestLeaves digest (ftsIndexOf tree)) := by
  obtain ⟨digest, hdigest, hdigestRun, hadmissible, hlayers, hftsRun, hlayersRun⟩ :=
    verify_extract ⟨context.key.root, context.key.parameter⟩ message signature hverify hrun
  exact ⟨digest, hdigest, hdigestRun, hadmissible,
    hcompatible.hypertree_honest hdummy hroot (digestIndex digest) (digestLeaves digest) signature hlayers hlayersRun hftsRun⟩

end SphincsSecurity.Concrete.RetainedResidual
