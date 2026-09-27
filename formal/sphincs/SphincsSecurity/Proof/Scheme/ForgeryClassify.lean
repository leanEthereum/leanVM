import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Ots.LayerCompare
/-!
# Classifying an accepted forgery

Descent through the five hypertree layers stops at a bad cache, at a one-time position not covered
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
    evalWithAnswerFn f (otsLeafAttempt parameter bottomLayer (treeIndexAt index bottomLayer)
        (leafIndexAt index bottomLayer) ftsPublicKey (signature.counter bottomLayer)
        (signature.chainValue bottomLayer)) = some bottomLeaf
      ∧ let thirdMessage := foldValue f parameter bottomLayer
          (treeIndexAt index bottomLayer) (leafIndexAt index bottomLayer)
          (signaturePath signature bottomLayer) bottomLeaf (layerHeight bottomLayer)
        ∃ thirdLeaf,
          evalWithAnswerFn f (otsLeafAttempt parameter thirdLayer (treeIndexAt index thirdLayer)
              (leafIndexAt index thirdLayer) thirdMessage (signature.counter thirdLayer)
              (signature.chainValue thirdLayer)) = some thirdLeaf
            ∧ let secondMessage := foldValue f parameter thirdLayer
                (treeIndexAt index thirdLayer) (leafIndexAt index thirdLayer)
                (signaturePath signature thirdLayer) thirdLeaf (layerHeight thirdLayer)
              ∃ secondLeaf,
                evalWithAnswerFn f (otsLeafAttempt parameter secondLayer (treeIndexAt index secondLayer)
                    (leafIndexAt index secondLayer) secondMessage (signature.counter secondLayer)
                    (signature.chainValue secondLayer)) = some secondLeaf
                  ∧ let middleMessage := foldValue f parameter secondLayer
                      (treeIndexAt index secondLayer) (leafIndexAt index secondLayer)
                      (signaturePath signature secondLayer) secondLeaf (layerHeight secondLayer)
                    ∃ middleLeaf,
                      evalWithAnswerFn f (otsLeafAttempt parameter middleLayer (treeIndexAt index middleLayer)
                          (leafIndexAt index middleLayer) middleMessage (signature.counter middleLayer)
                          (signature.chainValue middleLayer)) = some middleLeaf
                        ∧ let topMessage := foldValue f parameter middleLayer
                            (treeIndexAt index middleLayer) (leafIndexAt index middleLayer)
                            (signaturePath signature middleLayer) middleLeaf (layerHeight middleLayer)
                          (lay = bottomLayer ∧ message = ftsPublicKey)
                            ∨ (lay = thirdLayer ∧ message = thirdMessage)
                            ∨ (lay = secondLayer ∧ message = secondMessage)
                            ∨ (lay = middleLayer ∧ message = middleMessage)
                            ∨ (lay = topLayer ∧ message = topMessage)

def FullyHonestOpening (f : QueryImpl HashSpec Id) (cache : QueryCache HashSpec)
    (secretKey : SecretKey) (index : Index) (leaves : IndexGroup → FtsLeaf)
    (signature : Signature) : Prop :=
  (∀ lay, HonestLayerOpening f secretKey.parameter secretKey.otsSecret lay
        (treeIndexAt index lay) (leafIndexAt index lay)
        (evalWithAnswerFn f (layerMessage secretKey index lay)) (signature.counter lay)
        (signature.chainValue lay) (signaturePath signature lay)
      ∧ CachedRun cache f (otsLeafAttempt secretKey.parameter lay (treeIndexAt index lay)
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

theorem nextTree_eq_of_position_eq (leftIndex rightIndex : Index) (lay : Layer)
    (hnext : lay.val + 1 < numLayers)
    (htree : treeIndexAt leftIndex lay = treeIndexAt rightIndex lay)
    (hleaf : leafIndexAt leftIndex lay = leafIndexAt rightIndex lay) :
    treeIndexAt leftIndex ⟨lay.val + 1, hnext⟩ =
      treeIndexAt rightIndex ⟨lay.val + 1, hnext⟩ := by
  apply Fin.ext
  rw [layers_link_next leftIndex lay hnext, layers_link_next rightIndex lay hnext, congrArg Fin.val htree,
    congrArg Fin.val hleaf]

theorem exact_layer_message_eq_next_root (f : QueryImpl HashSpec Id) (secretKey : SecretKey)
    (signedIndex forgedIndex : Index) (lay : Layer) (hnext : lay.val + 1 < numLayers)
    (message : Digest)
    (htree : treeIndexAt signedIndex lay = treeIndexAt forgedIndex lay)
    (hleaf : leafIndexAt signedIndex lay = leafIndexAt forgedIndex lay)
    (hmessage : evalWithAnswerFn f (layerMessage secretKey signedIndex lay) = message) :
    message = honestNode f secretKey.parameter ⟨lay.val + 1, hnext⟩
      (treeIndexAt forgedIndex ⟨lay.val + 1, hnext⟩)
      (secretKey.otsSecret ⟨lay.val + 1, hnext⟩
        (treeIndexAt forgedIndex ⟨lay.val + 1, hnext⟩))
      (layerHeight ⟨lay.val + 1, hnext⟩) 0 := by
  have hnextTree := nextTree_eq_of_position_eq signedIndex forgedIndex lay hnext htree hleaf
  rw [← hmessage, layerMessage_of_lt secretKey signedIndex lay hnext]
  simp only [hnextTree]
  change evalWithAnswerFn f (treeNode secretKey.parameter ⟨lay.val + 1, hnext⟩
    (treeIndexAt forgedIndex ⟨lay.val + 1, hnext⟩)
    (secretKey.otsSecret ⟨lay.val + 1, hnext⟩
      (treeIndexAt forgedIndex ⟨lay.val + 1, hnext⟩))
    (layerHeight ⟨lay.val + 1, hnext⟩) 0) = _
  rfl

theorem exact_top_message_eq_middle_root (f : QueryImpl HashSpec Id) (secretKey : SecretKey)
    (signedIndex forgedIndex : Index) (message : Digest)
    (htree : treeIndexAt signedIndex topLayer = treeIndexAt forgedIndex topLayer)
    (hleaf : leafIndexAt signedIndex topLayer = leafIndexAt forgedIndex topLayer)
    (hmessage : evalWithAnswerFn f (layerMessage secretKey signedIndex topLayer) = message) :
    message = honestNode f secretKey.parameter middleLayer
      (treeIndexAt forgedIndex middleLayer)
      (secretKey.otsSecret middleLayer (treeIndexAt forgedIndex middleLayer))
      (layerHeight middleLayer) 0 := by
  simpa only [topLayer, middleLayer] using
    exact_layer_message_eq_next_root f secretKey signedIndex forgedIndex topLayer (by decide)
      message htree hleaf hmessage

theorem exact_middle_message_eq_second_root (f : QueryImpl HashSpec Id) (secretKey : SecretKey)
    (signedIndex forgedIndex : Index) (message : Digest)
    (htree : treeIndexAt signedIndex middleLayer = treeIndexAt forgedIndex middleLayer)
    (hleaf : leafIndexAt signedIndex middleLayer = leafIndexAt forgedIndex middleLayer)
    (hmessage : evalWithAnswerFn f (layerMessage secretKey signedIndex middleLayer) = message) :
    message = honestNode f secretKey.parameter secondLayer
      (treeIndexAt forgedIndex secondLayer)
      (secretKey.otsSecret secondLayer (treeIndexAt forgedIndex secondLayer))
      (layerHeight secondLayer) 0 := by
  simpa only [middleLayer, secondLayer] using
    exact_layer_message_eq_next_root f secretKey signedIndex forgedIndex middleLayer (by decide)
      message htree hleaf hmessage

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
