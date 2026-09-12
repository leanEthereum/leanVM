import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Scheme.Cached
import SphincsSecurity.Proof.Scheme.Charge
import SphincsSecurity.Proof.Hypertree.Hypertree
/-!
# Deterministic forgery descent

At one hypertree layer, acceptance at the honest root either creates `Bad`, or the supplied chain
values and authentication path are exactly the honest values selected by the decoded codeword.
-/

namespace SphincsSecurity.Concrete

open OracleComp OracleSpec

variable {f : QueryImpl HashSpec Id} {parameter : PublicParameter}
  {otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest}
  {ftsSecret : Index → FtsTree → FtsLeaf → Digest}
  {cache : QueryCache HashSpec}

theorem verify_extract (publicKey : PublicKey) (message : Message) (signature : Signature)
    (hverify : evalWithAnswerFn f (verify publicKey message signature) = true)
    (hrun : CachedRun cache f (verify publicKey message signature)) :
    ∃ digest : MessageDigest,
      evalWithAnswerFn f
          (messageDigest publicKey.parameter publicKey.root message signature.randomness) = digest
        ∧ CachedRun cache f
          (messageDigest publicKey.parameter publicKey.root message signature.randomness)
        ∧ Admissible digest
        ∧ let index := digestIndex digest
          let leaves := digestLeaves digest
          let ftsPublicKey := evalWithAnswerFn f
            (ftsRecover publicKey.parameter index leaves signature.ftsSecret signature.ftsPath)
          evalWithAnswerFn f
              (verifyLayers publicKey.parameter index signature numLayers ftsPublicKey)
              = some publicKey.root
            ∧ CachedRun cache f
              (ftsRecover publicKey.parameter index leaves signature.ftsSecret signature.ftsPath)
            ∧ CachedRun cache f
              (verifyLayers publicKey.parameter index signature numLayers ftsPublicKey) := by
  let digest := evalWithAnswerFn f
    (messageDigest publicKey.parameter publicKey.root message signature.randomness)
  have hadmissible : Admissible digest := by
    by_contra hnot
    rw [verify_eq, evalWithAnswerFn_bind] at hverify
    simp only [digest] at hnot
    rw [if_pos hnot] at hverify
    simp at hverify
  let index := digestIndex digest
  let leaves := digestLeaves digest
  let ftsPublicKey := evalWithAnswerFn f
    (ftsRecover publicKey.parameter index leaves signature.ftsSecret signature.ftsPath)
  have hlayers : evalWithAnswerFn f
      (verifyLayers publicKey.parameter index signature numLayers ftsPublicKey)
      = some publicKey.root := by
    rw [verify_eq, evalWithAnswerFn_bind] at hverify
    simp only [digest, hadmissible, not_true_eq_false, if_false, evalWithAnswerFn_bind] at hverify
    cases hresult : evalWithAnswerFn f
        (verifyLayers publicKey.parameter index signature numLayers ftsPublicKey) with
    | none =>
        rw [hresult] at hverify
        simp at hverify
    | some root =>
        rw [hresult] at hverify
        simp only [evalWithAnswerFn_pure, decide_eq_true_eq] at hverify
        simp [hverify]
  rw [verify_eq] at hrun
  have hmessageRun := hrun.bind_left
  have hafterDigest := hrun.bind_right
  simp only [digest, hadmissible, not_true_eq_false, if_false] at hafterDigest
  change CachedRun cache f (do
    let ftsPublicKey ←
      ftsRecover publicKey.parameter index leaves signature.ftsSecret signature.ftsPath
    match ← verifyLayers publicKey.parameter index signature numLayers ftsPublicKey with
    | none => pure false
    | some root => pure (decide (root = publicKey.root))) at hafterDigest
  have hfts : CachedRun cache f
      (ftsRecover publicKey.parameter index leaves signature.ftsSecret signature.ftsPath) :=
    hafterDigest.bind_left
  have hlayersRun : CachedRun cache f
      (verifyLayers publicKey.parameter index signature numLayers ftsPublicKey) := by
    have := hafterDigest.bind_right.bind_left
    simpa only [ftsPublicKey] using this
  exact ⟨digest, rfl, hmessageRun, hadmissible, hlayers, hfts, hlayersRun⟩

theorem verifyLayers_succ_extract_cached (index : Index) (signature : Signature)
    (remaining : Nat) (hlayer : remaining < numLayers) (message target : Digest)
    (hverify : evalWithAnswerFn f
      (verifyLayers parameter index signature (remaining + 1) message) = some target)
    (hrun : CachedRun cache f
      (verifyLayers parameter index signature (remaining + 1) message)) :
    ∃ leafValue,
      let lay : Layer := ⟨remaining, hlayer⟩
      let tree := treeIndexAt index lay
      let leafIdx := leafIndexAt index lay
      let rootValue := foldValue f parameter lay tree leafIdx (signaturePath signature lay)
        leafValue (layerHeight lay)
      evalWithAnswerFn f (otsLeaf parameter lay tree leafIdx message (signature.counter lay)
          (signature.chainValue lay)) = some leafValue
        ∧ evalWithAnswerFn f (verifyLayers parameter index signature remaining rootValue)
          = some target
        ∧ CachedRun cache f (otsLeaf parameter lay tree leafIdx message (signature.counter lay)
          (signature.chainValue lay))
        ∧ CachedRun cache f (treeFold parameter lay tree leafIdx (signaturePath signature lay)
          (layerHeight lay) leafValue)
        ∧ CachedRun cache f (verifyLayers parameter index signature remaining rootValue) := by
  obtain ⟨leafValue, hleaf, hrest⟩ :=
    verifyLayers_succ_extract f parameter index signature remaining hlayer message target hverify
  rw [verifyLayers_succ_eq, dif_pos hlayer] at hrun
  have hots := hrun.bind_left
  have hafter := hrun.bind_right
  rw [hleaf] at hafter
  exact ⟨leafValue, hleaf, hrest, hots, hafter.bind_left, hafter.bind_right⟩

def LayerFrame (f : QueryImpl HashSpec Id) (cache : QueryCache HashSpec)
    (parameter : PublicParameter) (index : Index) (signature : Signature)
    (lay : Layer) (message target leafValue : Digest) : Prop :=
  evalWithAnswerFn f
        (otsLeaf parameter lay (treeIndexAt index lay) (leafIndexAt index lay) message
          (signature.counter lay) (signature.chainValue lay)) = some leafValue
      ∧ evalWithAnswerFn f
        (verifyLayers parameter index signature lay.val
          (foldValue f parameter lay (treeIndexAt index lay) (leafIndexAt index lay)
            (signaturePath signature lay) leafValue (layerHeight lay))) = some target
      ∧ CachedRun cache f
        (otsLeaf parameter lay (treeIndexAt index lay) (leafIndexAt index lay) message
          (signature.counter lay) (signature.chainValue lay))
      ∧ CachedRun cache f
        (treeFold parameter lay (treeIndexAt index lay) (leafIndexAt index lay)
          (signaturePath signature lay) (layerHeight lay) leafValue)
      ∧ CachedRun cache f
        (verifyLayers parameter index signature lay.val
          (foldValue f parameter lay (treeIndexAt index lay) (leafIndexAt index lay)
            (signaturePath signature lay) leafValue (layerHeight lay)))

def LayerRun (f : QueryImpl HashSpec Id) (cache : QueryCache HashSpec)
    (parameter : PublicParameter) (index : Index) (signature : Signature)
    (lay : Layer) (message target : Digest) : Prop :=
  ∃ leafValue, LayerFrame f cache parameter index signature lay message target leafValue

theorem layerRun_of_verify (index : Index) (signature : Signature)
    (lay : Layer) (message target : Digest)
    (hverify : evalWithAnswerFn f
      (verifyLayers parameter index signature (lay.val + 1) message) = some target)
    (hrun : CachedRun cache f
      (verifyLayers parameter index signature (lay.val + 1) message)) :
    LayerRun f cache parameter index signature lay message target := by
  obtain ⟨leafValue, hleaf, hnext, hleafRun, hfoldRun, hnextRun⟩ :=
    verifyLayers_succ_extract_cached (f := f) (cache := cache) index signature lay.val lay.isLt
      message target hverify hrun
  exact ⟨leafValue, hleaf, hnext, hleafRun, hfoldRun, hnextRun⟩

def HypertreeRun (f : QueryImpl HashSpec Id) (cache : QueryCache HashSpec)
    (parameter : PublicParameter) (index : Index) (signature : Signature)
    (message target : Digest) : Prop :=
  ∃ bottomLeaf,
    LayerFrame f cache parameter index signature bottomLayer message target bottomLeaf
      ∧ let middleMessage := foldValue f parameter bottomLayer
          (treeIndexAt index bottomLayer) (leafIndexAt index bottomLayer)
          (signaturePath signature bottomLayer) bottomLeaf (layerHeight bottomLayer)
        ∃ middleLeaf,
          LayerFrame f cache parameter index signature middleLayer middleMessage target middleLeaf
            ∧ let topMessage := foldValue f parameter middleLayer
                (treeIndexAt index middleLayer) (leafIndexAt index middleLayer)
                (signaturePath signature middleLayer) middleLeaf (layerHeight middleLayer)
              LayerRun f cache parameter index signature topLayer topMessage target

theorem hypertreeRun_of_verify (index : Index) (signature : Signature)
    (message target : Digest)
    (hverify : evalWithAnswerFn f
      (verifyLayers parameter index signature numLayers message) = some target)
    (hrun : CachedRun cache f
      (verifyLayers parameter index signature numLayers message)) :
    HypertreeRun f cache parameter index signature message target := by
  have hbottom := layerRun_of_verify (f := f) (cache := cache) index signature bottomLayer
    message target (by simpa only [numLayers, bottomLayer] using hverify)
    (by simpa only [numLayers, bottomLayer] using hrun)
  obtain ⟨bottomLeaf, hbottom⟩ := hbottom
  let middleMessage := foldValue f parameter bottomLayer
    (treeIndexAt index bottomLayer) (leafIndexAt index bottomLayer)
    (signaturePath signature bottomLayer) bottomLeaf (layerHeight bottomLayer)
  have hmiddle := layerRun_of_verify (f := f) (cache := cache) index signature middleLayer
    middleMessage target (by
      simpa only [middleMessage, bottomLayer, middleLayer, numLayers] using hbottom.2.1)
    (by simpa only [middleMessage, bottomLayer, middleLayer, numLayers] using hbottom.2.2.2.2)
  obtain ⟨middleLeaf, hmiddle⟩ := hmiddle
  let topMessage := foldValue f parameter middleLayer
    (treeIndexAt index middleLayer) (leafIndexAt index middleLayer)
    (signaturePath signature middleLayer) middleLeaf (layerHeight middleLayer)
  have htop := layerRun_of_verify (f := f) (cache := cache) index signature topLayer
    topMessage target (by simpa only [topMessage, middleLayer, topLayer] using hmiddle.2.1)
    (by simpa only [topMessage, middleLayer, topLayer] using hmiddle.2.2.2.2)
  exact ⟨bottomLeaf, hbottom, middleLeaf, hmiddle, htop⟩

def HonestLayerOpening (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex) (message : Digest)
    (counter : Counter) (values : ChainIndex → Digest) (path : Nat → Digest) : Prop :=
  ∃ codeword : Encoding,
    evalWithAnswerFn f (encode parameter lay tree leafIdx message counter) = some codeword
      ∧ (∀ chainIdx, values chainIdx
        = honestChain f parameter lay tree leafIdx chainIdx
          (otsSecret lay tree leafIdx chainIdx) (codeword chainIdx).val)
      ∧ ∀ level, level < layerHeight lay → path level
        = honestNode f parameter lay tree (otsSecret lay tree) level
          (Nat.xor (leafIdx.val / 2 ^ level) 1)

end SphincsSecurity.Concrete
