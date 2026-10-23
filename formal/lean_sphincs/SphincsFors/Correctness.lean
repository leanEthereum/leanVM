import SphincsFors.Pruning
import SphincsFors.Uniform

/-! Signer/verifier correctness for the one-layer candidate and every pruned subtree. -/

open OracleComp

set_option maxHeartbeats 250000

namespace SphincsFors.Completeness

open Concrete Seeded

attribute [local irreducible] digestAttemptLimit encodingAttemptLimit
attribute [local semireducible] Concrete.verify

variable (f : QueryImpl HashSpec Id) [Params]

def layerMessageValue (secretKey : Seeded.SecretKey) (index : Index) (lay : Layer) : Digest :=
  evalWithAnswerFn f (Seeded.layerMessage secretKey index lay : OracleComp HashSpec Digest)

theorem signLayer_spec (secretKey : Seeded.SecretKey) (index : Index) (lay : Layer)
    {part : LayerSignature lay}
    (h : evalWithAnswerFn f (Seeded.signLayer secretKey index lay
        : OracleComp HashSpec (Option (LayerSignature lay))) = some part) :
    evalWithAnswerFn f (otsSign secretKey.parameter lay (treeIndexAt index lay)
        (leafIndexAt index lay) secretKey.seed (layerMessageValue f secretKey index lay)
        : OracleComp HashSpec (Option (Counter × (ChainIndex → Digest))))
        = some (part.counter, part.chainValues)
      ∧ part.path = evalWithAnswerFn f (Seeded.treePath secretKey.parameter lay
          (treeIndexAt index lay) secretKey.seed (leafIndexAt index lay)
          : OracleComp HashSpec (Fin (layerHeight lay) → Digest)) := by
  simp only [layerMessageValue, Seeded.signLayer, evalWithAnswerFn_bind] at h ⊢
  cases hots : evalWithAnswerFn f (otsSign secretKey.parameter lay (treeIndexAt index lay)
      (leafIndexAt index lay) secretKey.seed
      (evalWithAnswerFn f (Seeded.layerMessage secretKey index lay : OracleComp HashSpec Digest))
      : OracleComp HashSpec (Option (Counter × (ChainIndex → Digest)))) with
  | none =>
      rw [hots] at h
      simp at h
  | some result =>
      rw [hots] at h
      simp only [evalWithAnswerFn_bind, evalWithAnswerFn_pure, Option.some.injEq] at h
      subst h
      exact ⟨rfl, rfl⟩

omit [Params] in
theorem only_layer (lay : Layer) : lay = topLayer := by
  apply Fin.ext
  have h : lay.val < 1 := lay.isLt
  change lay.val = 0
  omega

omit [Params] in
theorem treeIndexAt_eq (index : Index) (lay : Layer) : treeIndexAt index lay = rootTree := rfl

omit [Params] in
theorem leafIndexAt_eq (index : Index) (lay : Layer) : leafIndexAt index lay = index := by
  rw [only_layer lay]
  apply Fin.ext
  have hindex := index.isLt
  simp [leafIndexAt, heightBelow, heightAbove, topLayer, layerHeight,
    totalHeight, maxLayerHeight] at hindex ⊢
  omega

omit [Params] in
theorem digestIndex_truncate (first second : HashOutput) :
    digestIndex (truncateMessageDigest first second) = blockIndex first := by
  unfold digestIndex blockIndex
  congr 1
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hi26 : i < 26 := hi
  rw [BitVec.getLsbD_extractLsb', BitVec.getLsbD_extractLsb',
    getLsbD_truncateMessageDigest, Nat.zero_add, ite_eq_left hi26]
  rfl

def digestValue (secretKey : Seeded.SecretKey) (message : Message) (randomness : Randomness) :
    MessageDigest :=
  evalWithAnswerFn f (messageDigest secretKey.parameter secretKey.root message randomness
    : OracleComp HashSpec MessageDigest)

omit [Params] in
theorem digestValue_index (secretKey : Seeded.SecretKey) (message : Message)
    (randomness : Randomness) :
    digestIndex (digestValue f secretKey message randomness) =
      blockIndex (evalWithAnswerFn f (messageDigestCall secretKey.parameter secretKey.root
        message randomness 0 : OracleComp HashSpec HashOutput)) := by
  simp only [digestValue, messageDigest, evalWithAnswerFn_bind, evalWithAnswerFn_pure,
    digestIndex_truncate]

theorem signDigestLoop_spec (secretKey : Seeded.SecretKey) (message : Message) :
    ∀ (attempts : Nat) (trial : Randomness) {randomness : Randomness} {index : Index},
      evalWithAnswerFn f (Seeded.signDigestLoop secretKey message attempts trial
        : OracleComp HashSpec (Option (Randomness × Index))) = some (randomness, index) →
      Landed secretKey.parameter (digestIndex (digestValue f secretKey message randomness)) := by
  intro attempts
  induction attempts with
  | zero => intro trial randomness index h; simp [Seeded.signDigestLoop] at h
  | succ attempts ih =>
      intro trial randomness index h
      simp only [Seeded.signDigestLoop, Seeded.signAttempt, evalWithAnswerFn_bind] at h
      split at h
      next hl =>
        simp only [evalWithAnswerFn_pure, Option.some.injEq, Prod.mk.injEq] at h
        rw [digestValue_index, ← h.1]
        by_contra hh
        simp only [ite_eq_right hh, evalWithAnswerFn_pure] at hl
        contradiction
      next => exact ih (trial + 1) h

omit [Params] in
theorem sequenceLayers_spec {α : Layer → Type}
    (computation : (lay : Layer) → OracleComp HashSpec (Option (α lay)))
    {layers : (lay : Layer) → α lay}
    (h : evalWithAnswerFn f (sequenceLayers computation) = some layers) :
    ∀ lay, evalWithAnswerFn f (computation lay) = some (layers lay) := by
  simp only [sequenceLayers, evalWithAnswerFn_bind] at h
  cases ht : evalWithAnswerFn f (computation topLayer) with
  | none => simp [ht] at h
  | some top =>
      simp only [ht, evalWithAnswerFn_pure] at h
      obtain rfl := Option.some.inj h
      intro lay
      rw [only_layer lay]
      exact ht

attribute [local irreducible] Seeded.signDigestLoop Seeded.signLayer Seeded.ftsOpen
  Seeded.treePath Seeded.treeNode Seeded.ftsNode sequenceFin Seeded.ftsKey Seeded.treeRoot
  Seeded.spineNode

theorem sign_spec (secretKey : Seeded.SecretKey) (message : Message) {signature : Signature}
    (h : evalWithAnswerFn f (Seeded.sign secretKey message
        : OracleComp HashSpec (Option Signature)) = some signature) :
    Landed secretKey.parameter (digestIndex (digestValue f secretKey message signature.randomness))
      ∧ signature.ftsSecret = (fun tree => ftsSecret f secretKey.parameter
          (digestIndex (digestValue f secretKey message signature.randomness)) tree
          (digestLeaves (digestValue f secretKey message signature.randomness) (ftsIndexOf tree))
          secretKey.seed)
      ∧ signature.ftsPath = evalWithAnswerFn f (Seeded.ftsOpen secretKey.parameter
          (digestIndex (digestValue f secretKey message signature.randomness))
          (digestLeaves (digestValue f secretKey message signature.randomness)) secretKey.seed
          : OracleComp HashSpec (FtsTree → Fin ftsTreeHeight → Digest))
      ∧ ∀ lay : Layer, evalWithAnswerFn f (Seeded.signLayer secretKey
          (digestIndex (digestValue f secretKey message signature.randomness)) lay
          : OracleComp HashSpec (Option (LayerSignature lay))) = some (signature.layers lay) := by
  rw [Seeded.sign, evalWithAnswerFn_bind, evalWithAnswerFn_bind] at h
  split at h
  next randomness index hloop =>
      have hland := signDigestLoop_spec f secretKey message digestAttemptLimit _ hloop
      rw [evalWithAnswerFn_bind, evalWithAnswerFn_bind, evalWithAnswerFn_bind,
        evalWithAnswerFn_bind] at h
      split at h
      next layers hlayers =>
          simp only [evalWithAnswerFn_pure, Option.some.injEq] at h
          subst h
          exact ⟨hland, by simp only [eval_sequenceFin]; rfl, rfl,
            fun lay => sequenceLayers_spec f _ hlayers lay⟩
      next => exact absurd h (by simp)
  next => exact absurd h (by simp)

/-- The accepting counter recovers the honest leaf, and its pruned path recovers the root. -/
theorem eval_layer (secretKey : Seeded.SecretKey) (index : Index) (lay : Layer)
    (hland : Landed secretKey.parameter index) (signature : Signature)
    (h : evalWithAnswerFn f (Seeded.signLayer secretKey index lay
        : OracleComp HashSpec (Option (LayerSignature lay))) = some (signature.layers lay)) :
    evalWithAnswerFn f (otsLeaf secretKey.parameter lay (treeIndexAt index lay)
        (leafIndexAt index lay) (layerMessageValue f secretKey index lay)
        (signature.layers lay).counter (signature.layers lay).chainValues
        : OracleComp HashSpec (Option Digest))
      = some (node f secretKey.parameter lay (treeIndexAt index lay) secretKey.seed 0 index.val)
    ∧ evalWithAnswerFn f (treeFold secretKey.parameter lay (treeIndexAt index lay)
        (leafIndexAt index lay) (signaturePath signature lay) (layerHeight lay)
        (node f secretKey.parameter lay (treeIndexAt index lay) secretKey.seed 0 index.val)
        : OracleComp HashSpec Digest)
      = evalWithAnswerFn f (treeRoot secretKey.parameter lay (treeIndexAt index lay)
          secretKey.seed : OracleComp HashSpec Digest) := by
  obtain ⟨hots, hpath⟩ := signLayer_spec f secretKey index lay h
  refine ⟨?_, ?_⟩
  · rw [eval_otsLeaf_of_otsSign f secretKey.parameter lay (treeIndexAt index lay)
      (leafIndexAt index lay) secretKey.seed _ hots,
      ← congrArg Fin.val (leafIndexAt_eq index lay), node_zero]
  · rw [leafIndexAt_eq] at hpath ⊢
    apply eval_treeFold_pruned_path f _ _ _ _ _ hland
    intro level hlevel
    rw [signaturePath, dite_eq_left hlevel, hpath]

/-- Every successful signature verifies under every fixed hash function, for any pruning height. -/
theorem verify_of_parts (secretKey : Seeded.SecretKey) (message : Message) {signature : Signature}
    (hroot : secretKey.root = evalWithAnswerFn f (Seeded.treeRoot secretKey.parameter topLayer
      rootTree secretKey.seed : OracleComp HashSpec Digest))
    (hparts :
    Landed secretKey.parameter (digestIndex (digestValue f secretKey message signature.randomness))
      ∧ signature.ftsSecret = (fun tree => ftsSecret f secretKey.parameter
          (digestIndex (digestValue f secretKey message signature.randomness)) tree
          (digestLeaves (digestValue f secretKey message signature.randomness) (ftsIndexOf tree))
          secretKey.seed)
      ∧ signature.ftsPath = evalWithAnswerFn f (Seeded.ftsOpen secretKey.parameter
          (digestIndex (digestValue f secretKey message signature.randomness))
          (digestLeaves (digestValue f secretKey message signature.randomness)) secretKey.seed
          : OracleComp HashSpec (FtsTree → Fin ftsTreeHeight → Digest))
      ∧ ∀ lay : Layer, evalWithAnswerFn f (Seeded.signLayer secretKey
          (digestIndex (digestValue f secretKey message signature.randomness)) lay
          : OracleComp HashSpec (Option (LayerSignature lay))) = some (signature.layers lay) ) :
    evalWithAnswerFn f (Concrete.verify ⟨secretKey.root, secretKey.parameter⟩ message signature
      : OracleComp HashSpec Bool) = true := by
  obtain ⟨hland, hsecrets, hpaths, hlayers⟩ := hparts
  set digest := digestValue f secretKey message signature.randomness
  set index := digestIndex digest with hindex
  have hkey : evalWithAnswerFn f (ftsRecover secretKey.parameter index (digestLeaves digest)
      signature.ftsSecret signature.ftsPath : OracleComp HashSpec Digest)
      = layerMessageValue f secretKey index topLayer := by
    rw [hsecrets, hpaths, eval_ftsRecover]
    rfl
  obtain ⟨hleaf, hfold⟩ := eval_layer f secretKey index topLayer hland signature (hlayers _)
  have hfold' : evalWithAnswerFn f (treeFold secretKey.parameter topLayer (treeIndexAt index topLayer)
      (leafIndexAt index topLayer) (signaturePath signature topLayer) (layerHeight topLayer)
      (node f secretKey.parameter topLayer (treeIndexAt index topLayer) secretKey.seed 0 index.val)
        : OracleComp HashSpec Digest) = secretKey.root := by
    rw [hfold, treeIndexAt_eq, ← hroot]
  have hdig : evalWithAnswerFn f (messageDigest secretKey.parameter secretKey.root message
      signature.randomness : OracleComp HashSpec MessageDigest) = digest := rfl
  rw [Concrete.verify]
  simp only [evalWithAnswerFn_bind, hdig, ← hindex, hkey]
  rw [show numLayers = 0 + 1 from rfl, verifyLayers, dite_eq_left (by decide : 0 < numLayers)]
  simp only [topLayer] at hleaf hfold'
  simp only [topLayer, evalWithAnswerFn_bind, hleaf, hfold', verifyLayers,
    evalWithAnswerFn_pure, decide_true]

/-- Every successful signature verifies under every fixed hash function, for any pruning height. -/
theorem verify_of_sign (secretKey : Seeded.SecretKey) (message : Message) {signature : Signature}
    (hroot : secretKey.root = evalWithAnswerFn f (Seeded.treeRoot secretKey.parameter topLayer
      rootTree secretKey.seed : OracleComp HashSpec Digest))
    (h : evalWithAnswerFn f (Seeded.sign secretKey message
        : OracleComp HashSpec (Option Signature)) = some signature) :
    evalWithAnswerFn f (Concrete.verify ⟨secretKey.root, secretKey.parameter⟩ message signature
      : OracleComp HashSpec Bool) = true := by
  exact verify_of_parts f secretKey message hroot (sign_spec f secretKey message h)

/-- Key generation supplies the root invariant used by `verify_of_sign`. -/
theorem correct (seed : MasterSeed) (publicKey : PublicKey) (secretKey : Seeded.SecretKey)
    (message : Message) (signature : Signature)
    (hkey : evalWithAnswerFn f (Seeded.keygenFromSeed seed) = (publicKey, secretKey))
    (hsign : evalWithAnswerFn f (Seeded.sign secretKey message
      : OracleComp HashSpec (Option Signature)) = some signature) :
    evalWithAnswerFn f (Concrete.verify publicKey message signature
      : OracleComp HashSpec Bool) = true := by
  simp only [Seeded.keygenFromSeed, evalWithAnswerFn_bind, evalWithAnswerFn_pure,
    Prod.mk.injEq] at hkey
  generalize hparameter : evalWithAnswerFn f
    (deriveKey 0 .parameter seed : OracleComp HashSpec Digest) = parameter at hkey
  generalize hrootval : evalWithAnswerFn f
    (treeRoot parameter topLayer rootTree seed : OracleComp HashSpec Digest) = root at hkey
  obtain ⟨hpk, hsk⟩ := hkey
  subst publicKey
  subst secretKey
  exact verify_of_sign f ⟨seed, parameter, root⟩ message hrootval.symm hsign

end SphincsFors.Completeness
