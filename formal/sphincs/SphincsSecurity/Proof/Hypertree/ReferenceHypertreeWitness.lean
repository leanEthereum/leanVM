import SphincsSecurity.Proof.Ots.ReferenceLayerWitness
import SphincsSecurity.Proof.Reference.VerifierTraceDescent
namespace SphincsSecurity.Concrete.OtsVerifierWitness

open _root_.OracleComp OracleSpec OtsContactTrace
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] chainWalk sequenceFin canonicalEncodingInputs canonicalGraphInputs instFintypePosition

variable (f : QueryImpl HashSpec Id) (key : SecretKey) (words : OtsReferenceWords)
  (messages : EncodingPosition → Digest) (selections : ReferenceFamily)

def LayerException (trace : Trace) : Prop :=
  EncodingOutputMatch key.parameter words messages selections trace ∨
    ∃ lay tree leaf, TreeOutputMatch f key.parameter lay tree (key.otsSecret lay tree) trace ∨
      LeafOutputMatch f key.parameter lay tree leaf (key.otsSecret lay tree leaf) trace ∨
        ChainException f key.parameter words lay tree leaf (key.otsSecret lay tree leaf) trace

def ReferenceLayerOpening (index : Index) (signature : Signature) (lay : Layer) : Prop :=
  ∃ selected, selections ⟨lay, treeIndexAt index lay, leafIndexAt index lay⟩ = some selected ∧
    signature.counter lay = BitVec.ofNat counterBits selected.1.val ∧
    evalWithAnswerFn f (encode key.parameter lay (treeIndexAt index lay) (leafIndexAt index lay)
      (evalWithAnswerFn f (layerMessage key index lay)) (signature.counter lay)) = some (words lay (treeIndexAt index lay) (leafIndexAt index lay)) ∧
    (∀ chain, signature.chainValue lay chain = frontier f key.parameter words lay (treeIndexAt index lay) (leafIndexAt index lay)
      (key.otsSecret lay (treeIndexAt index lay) (leafIndexAt index lay)) chain) ∧
    ∀ level, level < layerHeight lay → signaturePath signature lay level =
      honestNode f key.parameter lay (treeIndexAt index lay) (key.otsSecret lay (treeIndexAt index lay)) level
        (Nat.xor ((leafIndexAt index lay).val / 2 ^ level) 1)

theorem layer_frame_reference (index : Index) (signature : Signature) (lay : Layer) (message target leafValue : Digest) (trace : Trace)
    (hvalid : TargetSum.Valid (words lay (treeIndexAt index lay) (leafIndexAt index lay)))
    (hmessages : messages ⟨lay, treeIndexAt index lay, leafIndexAt index lay⟩ = evalWithAnswerFn f (layerMessage key index lay))
    (hclean : ¬LayerException f key words messages selections trace)
    (hframe : LayerFrame f (recordedCache f trace) key.parameter index signature lay message target leafValue)
    (hfold : foldValue f key.parameter lay (treeIndexAt index lay) (leafIndexAt index lay) (signaturePath signature lay) leafValue (layerHeight lay) =
      honestNode f key.parameter lay (treeIndexAt index lay) (key.otsSecret lay (treeIndexAt index lay)) (layerHeight lay) 0) :
    message = evalWithAnswerFn f (layerMessage key index lay) ∧ ReferenceLayerOpening f key words selections index signature lay := by
  cases hencode : evalWithAnswerFn f (encode key.parameter lay (treeIndexAt index lay) (leafIndexAt index lay) message (signature.counter lay)) with
  | none =>
      have hots := hframe.1
      simp only [otsLeaf, evalWithAnswerFn_bind, hencode, evalWithAnswerFn_pure, reduceCtorEq] at hots
  | some candidate =>
      have h := layer_reference_classification f key.parameter words messages selections lay (treeIndexAt index lay)
        (key.otsSecret lay (treeIndexAt index lay)) (leafIndexAt index lay) (leafIndexAt_lt index lay) (signaturePath signature lay)
        message (signature.counter lay) (signature.chainValue lay) candidate leafValue trace hvalid hencode hframe.1 hfold
        ((recordedCache_run_iff f trace _).mp hframe.2.2.1) ((recordedCache_run_iff f trace _).mp hframe.2.2.2.1)
      rcases h with ⟨selected, hs, hm, hc, hw, hv, hp⟩ | ht | hl | hc | he
      · refine ⟨hm.trans hmessages, selected, hs, hc, ?_, hv, hp⟩
        rw [← hm.trans hmessages, ← hw]
        exact hencode
      · exact False.elim (hclean (Or.inr ⟨lay, treeIndexAt index lay, leafIndexAt index lay, Or.inl ht⟩))
      · exact False.elim (hclean (Or.inr ⟨lay, treeIndexAt index lay, leafIndexAt index lay, Or.inr (Or.inl hl)⟩))
      · exact False.elim (hclean (Or.inr ⟨lay, treeIndexAt index lay, leafIndexAt index lay, Or.inr (Or.inr hc)⟩))
      · exact False.elim (hclean (Or.inl he))

theorem hypertree_reference (index : Index) (leaves : IndexGroup → FtsLeaf) (signature : Signature) (trace : Trace)
    (hvalid : ∀ lay, TargetSum.Valid (words lay (treeIndexAt index lay) (leafIndexAt index lay)))
    (hmessages : ∀ lay, messages ⟨lay, treeIndexAt index lay, leafIndexAt index lay⟩ = evalWithAnswerFn f (layerMessage key index lay))
    (hroot : key.root = honestNode f key.parameter topLayer rootTree (key.otsSecret topLayer rootTree) (layerHeight topLayer) 0)
    (hclean : ¬LayerException f key words messages selections trace)
    (hverify : evalWithAnswerFn f (verifyLayers key.parameter index signature numLayers (evalWithAnswerFn f (ftsRecover key.parameter index leaves signature.ftsSecret signature.ftsPath))) = some key.root)
    (hrun : ContainsRun f trace (verifyLayers key.parameter index signature numLayers (evalWithAnswerFn f (ftsRecover key.parameter index leaves signature.ftsSecret signature.ftsPath)))) :
    (evalWithAnswerFn f (ftsRecover key.parameter index leaves signature.ftsSecret signature.ftsPath)) = honestFtsKey f key.parameter index (key.ftsSecret index) ∧
      ∀ lay, ReferenceLayerOpening f key words selections index signature lay ∧
        CachedRun (recordedCache f trace) f (otsLeaf key.parameter lay (treeIndexAt index lay) (leafIndexAt index lay)
          (evalWithAnswerFn f (layerMessage key index lay)) (signature.counter lay) (signature.chainValue lay)) ∧
        VerifierLayerMessage f key.parameter index leaves signature lay (evalWithAnswerFn f (layerMessage key index lay)) := by
  obtain ⟨bottomLeaf, hbottom, middleLeaf, hmiddle, topLeaf, htop⟩ := hypertreeRun_of_verify index signature (evalWithAnswerFn f (ftsRecover key.parameter index leaves signature.ftsSecret signature.ftsPath)) key.root hverify hrun.cached
  let middleMessage := foldValue f key.parameter bottomLayer (treeIndexAt index bottomLayer) (leafIndexAt index bottomLayer)
    (signaturePath signature bottomLayer) bottomLeaf (layerHeight bottomLayer)
  let topMessage := foldValue f key.parameter middleLayer (treeIndexAt index middleLayer) (leafIndexAt index middleLayer)
    (signaturePath signature middleLayer) middleLeaf (layerHeight middleLayer)
  have htopFold : foldValue f key.parameter topLayer (treeIndexAt index topLayer) (leafIndexAt index topLayer)
      (signaturePath signature topLayer) topLeaf (layerHeight topLayer) = key.root := by
    simpa only [topLayer, verifyLayers_zero_eq, evalWithAnswerFn_pure, Option.some.injEq] using htop.2.1
  have htree : treeIndexAt index topLayer = rootTree := Fin.ext (treeIndexAt_topLayer index)
  have htopRoot : foldValue f key.parameter topLayer (treeIndexAt index topLayer) (leafIndexAt index topLayer)
      (signaturePath signature topLayer) topLeaf (layerHeight topLayer) = honestNode f key.parameter topLayer (treeIndexAt index topLayer)
        (key.otsSecret topLayer (treeIndexAt index topLayer)) (layerHeight topLayer) 0 := by
    rw [htopFold, hroot, htree]
  have ht := layer_frame_reference f key words messages selections index signature topLayer topMessage key.root topLeaf trace
    (hvalid _) (hmessages _) hclean htop htopRoot
  have hmRoot := exact_top_message_eq_middle_root f key index index topMessage rfl rfl ht.1.symm
  have hm := layer_frame_reference f key words messages selections index signature middleLayer middleMessage key.root middleLeaf trace
    (hvalid _) (hmessages _) hclean hmiddle hmRoot
  have hbRoot := exact_middle_message_eq_bottom_root f key index index middleMessage rfl rfl hm.1.symm
  have hb := layer_frame_reference f key words messages selections index signature bottomLayer (evalWithAnswerFn f (ftsRecover key.parameter index leaves signature.ftsSecret signature.ftsPath)) key.root bottomLeaf trace
    (hvalid _) (hmessages _) hclean hbottom hbRoot
  refine ⟨exact_bottom_message_eq_fts_key f key index index (evalWithAnswerFn f (ftsRecover key.parameter index leaves signature.ftsSecret signature.ftsPath)) rfl rfl hb.1.symm, ?_⟩
  have hverifier (position : Layer) (value : Digest)
      (hp : position = bottomLayer ∧ value = (evalWithAnswerFn f (ftsRecover key.parameter index leaves signature.ftsSecret signature.ftsPath)) ∨
        position = middleLayer ∧ value = middleMessage ∨ position = topLayer ∧ value = topMessage) :
      VerifierLayerMessage f key.parameter index leaves signature position value :=
    ⟨bottomLeaf, hbottom.1, middleLeaf, hmiddle.1, hp⟩
  have hpack (position : Layer) (value : Digest)
      (he : value = evalWithAnswerFn f (layerMessage key index position))
      (ho : ReferenceLayerOpening f key words selections index signature position)
      (hc : CachedRun (recordedCache f trace) f (otsLeaf key.parameter position (treeIndexAt index position) (leafIndexAt index position)
        value (signature.counter position) (signature.chainValue position)))
      (hv : VerifierLayerMessage f key.parameter index leaves signature position value) :
      ReferenceLayerOpening f key words selections index signature position ∧
        CachedRun (recordedCache f trace) f (otsLeaf key.parameter position (treeIndexAt index position) (leafIndexAt index position)
          (evalWithAnswerFn f (layerMessage key index position)) (signature.counter position) (signature.chainValue position)) ∧
        VerifierLayerMessage f key.parameter index leaves signature position (evalWithAnswerFn f (layerMessage key index position)) := by
    rw [he] at hc hv
    exact ⟨ho, hc, hv⟩
  intro lay
  fin_cases lay
  · simpa only [topLayer] using hpack topLayer topMessage ht.1 ht.2 htop.2.2.1
      (hverifier _ _ (Or.inr (Or.inr ⟨rfl, rfl⟩)))
  · simpa only [middleLayer] using hpack middleLayer middleMessage hm.1 hm.2 hmiddle.2.2.1
      (hverifier _ _ (Or.inr (Or.inl ⟨rfl, rfl⟩)))
  · simpa only [bottomLayer, numLayers] using hpack bottomLayer _ hb.1 hb.2 hbottom.2.2.1
      (hverifier _ _ (Or.inl ⟨rfl, rfl⟩))

theorem hypertree_classification (index : Index) (leaves : IndexGroup → FtsLeaf) (signature : Signature) (trace : Trace)
    (hvalid : ∀ lay, TargetSum.Valid (words lay (treeIndexAt index lay) (leafIndexAt index lay)))
    (hmessages : ∀ lay, messages ⟨lay, treeIndexAt index lay, leafIndexAt index lay⟩ = evalWithAnswerFn f (layerMessage key index lay))
    (hroot : key.root = honestNode f key.parameter topLayer rootTree (key.otsSecret topLayer rootTree) (layerHeight topLayer) 0)
    (hverify : evalWithAnswerFn f (verifyLayers key.parameter index signature numLayers (evalWithAnswerFn f (ftsRecover key.parameter index leaves signature.ftsSecret signature.ftsPath))) = some key.root)
    (hrun : ContainsRun f trace (verifyLayers key.parameter index signature numLayers (evalWithAnswerFn f (ftsRecover key.parameter index leaves signature.ftsSecret signature.ftsPath)))) :
    ((evalWithAnswerFn f (ftsRecover key.parameter index leaves signature.ftsSecret signature.ftsPath)) = honestFtsKey f key.parameter index (key.ftsSecret index) ∧ ∀ lay, ReferenceLayerOpening f key words selections index signature lay ∧
        CachedRun (recordedCache f trace) f (otsLeaf key.parameter lay (treeIndexAt index lay) (leafIndexAt index lay)
          (evalWithAnswerFn f (layerMessage key index lay)) (signature.counter lay) (signature.chainValue lay)) ∧
        VerifierLayerMessage f key.parameter index leaves signature lay (evalWithAnswerFn f (layerMessage key index lay))) ∨
      LayerException f key words messages selections trace := by
  by_cases h : LayerException f key words messages selections trace
  · exact Or.inr h
  · exact Or.inl (hypertree_reference f key words messages selections index leaves signature trace hvalid hmessages hroot h hverify hrun)

end SphincsSecurity.Concrete.OtsVerifierWitness
