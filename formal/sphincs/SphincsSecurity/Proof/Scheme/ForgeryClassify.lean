import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Ots.LayerCompare
/-!
# Classifying an accepted forgery

Descent through the three hypertree layers stops at a bad cache, at a one-time position not covered
exactly by the signing transcript, or at an honest few-time opening.
-/

namespace SphincsSecurity.Concrete

open OracleComp OracleSpec

def VerifierLayerMessage (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (index : Index) (leaves : IndexGroup → FtsLeaf) (signature : Signature)
    (lay : Layer) (message : Digest) : Prop :=
  let ftsPublicKey := evalWithAnswerFn f
    (ftsRecover parameter index leaves signature.ftsSecret signature.ftsPath)
  ∃ bottomLeaf,
    evalWithAnswerFn f (otsLeaf parameter bottomLayer (treeIndexAt index bottomLayer)
        (leafIndexAt index bottomLayer) ftsPublicKey (signature.counter bottomLayer)
        (signature.chainValue bottomLayer)) = some bottomLeaf
      ∧ let middleMessage := foldValue f parameter bottomLayer
          (treeIndexAt index bottomLayer) (leafIndexAt index bottomLayer)
          (signaturePath signature bottomLayer) bottomLeaf (layerHeight bottomLayer)
        ∃ middleLeaf,
          evalWithAnswerFn f (otsLeaf parameter middleLayer (treeIndexAt index middleLayer)
              (leafIndexAt index middleLayer) middleMessage (signature.counter middleLayer)
              (signature.chainValue middleLayer)) = some middleLeaf
            ∧ let topMessage := foldValue f parameter middleLayer
                (treeIndexAt index middleLayer) (leafIndexAt index middleLayer)
                (signaturePath signature middleLayer) middleLeaf (layerHeight middleLayer)
              (lay = bottomLayer ∧ message = ftsPublicKey)
                ∨ (lay = middleLayer ∧ message = middleMessage)
                ∨ (lay = topLayer ∧ message = topMessage)

def FullyHonestOpening (f : QueryImpl HashSpec Id) (cache : QueryCache HashSpec)
    (secretKey : SecretKey) (index : Index) (leaves : IndexGroup → FtsLeaf)
    (signature : Signature) : Prop :=
  (∀ lay, HonestLayerOpening f secretKey.parameter secretKey.otsSecret lay
        (treeIndexAt index lay) (leafIndexAt index lay)
        (evalWithAnswerFn f (layerMessage secretKey index lay)) (signature.counter lay)
        (signature.chainValue lay) (signaturePath signature lay)
      ∧ CachedRun cache f (otsLeaf secretKey.parameter lay (treeIndexAt index lay)
        (leafIndexAt index lay) (evalWithAnswerFn f (layerMessage secretKey index lay))
        (signature.counter lay) (signature.chainValue lay)))
    ∧ (∀ tree,
      signature.ftsSecret tree = secretKey.ftsSecret index tree (leaves (ftsIndexOf tree))
        ∧ ∀ level (hlevel : level < ftsTreeHeight), signature.ftsPath tree ⟨level, hlevel⟩
          = honestFtsNode f secretKey.parameter index tree (secretKey.ftsSecret index tree) level
            (Nat.xor ((leaves (ftsIndexOf tree)).val / 2 ^ level) 1))
    ∧ CachedRun cache f
      (ftsRecover secretKey.parameter index leaves signature.ftsSecret signature.ftsPath)
    ∧ ∀ lay, VerifierLayerMessage f secretKey.parameter index leaves signature lay
      (evalWithAnswerFn f (layerMessage secretKey index lay))

theorem middleTree_eq_of_top_position_eq (leftIndex rightIndex : Index)
    (htree : treeIndexAt leftIndex topLayer = treeIndexAt rightIndex topLayer)
    (hleaf : leafIndexAt leftIndex topLayer = leafIndexAt rightIndex topLayer) :
    treeIndexAt leftIndex middleLayer = treeIndexAt rightIndex middleLayer := by
  apply Fin.ext
  rw [layers_link_top leftIndex, layers_link_top rightIndex, congrArg Fin.val htree,
    congrArg Fin.val hleaf]

theorem bottomTree_eq_of_middle_position_eq (leftIndex rightIndex : Index)
    (htree : treeIndexAt leftIndex middleLayer = treeIndexAt rightIndex middleLayer)
    (hleaf : leafIndexAt leftIndex middleLayer = leafIndexAt rightIndex middleLayer) :
    treeIndexAt leftIndex bottomLayer = treeIndexAt rightIndex bottomLayer := by
  apply Fin.ext
  rw [layers_link_middle leftIndex, layers_link_middle rightIndex, congrArg Fin.val htree,
    congrArg Fin.val hleaf]

theorem exact_top_message_eq_middle_root (f : QueryImpl HashSpec Id) (secretKey : SecretKey)
    (signedIndex forgedIndex : Index) (message : Digest)
    (htree : treeIndexAt signedIndex topLayer = treeIndexAt forgedIndex topLayer)
    (hleaf : leafIndexAt signedIndex topLayer = leafIndexAt forgedIndex topLayer)
    (hmessage : evalWithAnswerFn f (layerMessage secretKey signedIndex topLayer) = message) :
    message = honestNode f secretKey.parameter middleLayer
      (treeIndexAt forgedIndex middleLayer)
      (secretKey.otsSecret middleLayer (treeIndexAt forgedIndex middleLayer))
      (layerHeight middleLayer) 0 := by
  have hnext := middleTree_eq_of_top_position_eq signedIndex forgedIndex htree hleaf
  rw [← hmessage, layerMessage_of_lt secretKey signedIndex topLayer (by decide)]
  simp only [show (⟨topLayer.val + 1, by decide⟩ : Layer) = middleLayer from rfl, hnext]
  change evalWithAnswerFn f (treeNode secretKey.parameter middleLayer
    (treeIndexAt forgedIndex middleLayer)
    (secretKey.otsSecret middleLayer (treeIndexAt forgedIndex middleLayer))
    (layerHeight middleLayer) 0) = _
  rfl

theorem exact_middle_message_eq_bottom_root (f : QueryImpl HashSpec Id) (secretKey : SecretKey)
    (signedIndex forgedIndex : Index) (message : Digest)
    (htree : treeIndexAt signedIndex middleLayer = treeIndexAt forgedIndex middleLayer)
    (hleaf : leafIndexAt signedIndex middleLayer = leafIndexAt forgedIndex middleLayer)
    (hmessage : evalWithAnswerFn f (layerMessage secretKey signedIndex middleLayer) = message) :
    message = honestNode f secretKey.parameter bottomLayer
      (treeIndexAt forgedIndex bottomLayer)
      (secretKey.otsSecret bottomLayer (treeIndexAt forgedIndex bottomLayer))
      (layerHeight bottomLayer) 0 := by
  have hnext := bottomTree_eq_of_middle_position_eq signedIndex forgedIndex htree hleaf
  rw [← hmessage, layerMessage_of_lt secretKey signedIndex middleLayer (by decide)]
  simp only [show (⟨middleLayer.val + 1, by decide⟩ : Layer) = bottomLayer from rfl, hnext]
  change evalWithAnswerFn f (treeNode secretKey.parameter bottomLayer
    (treeIndexAt forgedIndex bottomLayer)
    (secretKey.otsSecret bottomLayer (treeIndexAt forgedIndex bottomLayer))
    (layerHeight bottomLayer) 0) = _
  rfl

theorem exact_bottom_message_eq_fts_key (f : QueryImpl HashSpec Id) (secretKey : SecretKey)
    (signedIndex forgedIndex : Index) (message : Digest)
    (htree : treeIndexAt signedIndex bottomLayer = treeIndexAt forgedIndex bottomLayer)
    (hleaf : leafIndexAt signedIndex bottomLayer = leafIndexAt forgedIndex bottomLayer)
    (hmessage : evalWithAnswerFn f (layerMessage secretKey signedIndex bottomLayer) = message) :
    message = honestFtsKey f secretKey.parameter forgedIndex (secretKey.ftsSecret forgedIndex) := by
  have hindex := index_eq_of_bottom_position_eq htree hleaf
  subst signedIndex
  rw [← hmessage, layerMessage_bottomLayer]
  rfl

end SphincsSecurity.Concrete
