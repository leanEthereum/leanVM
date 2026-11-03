import FORS.Scheme.Pruning
import FORS.Scheme.DigestView

/-! Signer/verifier correctness for every height and shape: every layer, every pruned subtree. -/

open OracleComp

set_option maxHeartbeats 250000

namespace FORS.Completeness

variable [Params]

open Concrete Seeded

attribute [local irreducible] digestAttemptLimit encodingAttemptLimit
attribute [local semireducible] Concrete.verify

variable (f : QueryImpl HashSpec Id)

def layerMessageValue (secretKey : Seeded.SecretKey) (index : Index) (lay : Layer) : HashInput :=
  evalWithAnswerFn f (Seeded.layerMessage secretKey index lay : OracleComp HashSpec HashInput)

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
      (evalWithAnswerFn f (Seeded.layerMessage secretKey index lay : OracleComp HashSpec HashInput))
      : OracleComp HashSpec (Option (Counter × (ChainIndex → Digest)))) with
  | none =>
      rw [hots] at h
      simp at h
  | some result =>
      rw [hots] at h
      simp only [evalWithAnswerFn_bind, evalWithAnswerFn_pure, Option.some.injEq] at h
      subst h
      exact ⟨rfl, rfl⟩

/-- The top layer's tree on the path of every index is the root tree. -/
theorem treeIndexAt_top (index : Index) : treeIndexAt index topLayer = rootTree := by
  apply Fin.ext
  change index.val / 2 ^ (heightBelow topLayer + layerHeight topLayer) = 0
  rw [layerHeight_top, maxLayerHeight_add]
  exact Nat.div_eq_of_lt index.isLt

/-- The message of a layer above the bottom one is the root of the tree below on the path. -/
theorem layerMessageValue_above (secretKey : Seeded.SecretKey) (index : Index) (lay : Layer)
    (hbelow : lay.val + 1 < numLayers) :
    layerMessageValue f secretKey index lay = rootPayload (evalWithAnswerFn f
      (Seeded.treeRoot secretKey.parameter ⟨lay.val + 1, hbelow⟩
        (treeIndexAt index ⟨lay.val + 1, hbelow⟩) secretKey.seed : OracleComp HashSpec Digest)) := by
  simp only [layerMessageValue, Seeded.layerMessage, Seeded.keyMessage, dif_pos hbelow,
    evalWithAnswerFn_bind, evalWithAnswerFn_pure, childTree_path_above index lay hbelow]

/-- The message of the bottom layer is the FORS key. -/
theorem layerMessageValue_bottom (secretKey : Seeded.SecretKey) (index : Index) :
    layerMessageValue f secretKey index bottomLayer = rootsPayload (evalWithAnswerFn f
      (Seeded.forsKey secretKey.parameter index secretKey.seed : OracleComp HashSpec ForsKey)) := by
  have h : ¬(bottomLayer.val + 1 < numLayers) := by
    change ¬(numLayers - 1 + 1 < numLayers); have := numLayers_pos; omega
  simp only [layerMessageValue, Seeded.layerMessage, Seeded.keyMessage, dif_neg h,
    evalWithAnswerFn_bind, evalWithAnswerFn_pure, childTree_path_bottom]

def digestValue (secretKey : Seeded.SecretKey) (message : Message) (randomness : Randomness) :
    MessageDigest :=
  evalWithAnswerFn f (messageDigest secretKey.parameter secretKey.root message randomness
    : OracleComp HashSpec MessageDigest)

theorem digestValue_index (secretKey : Seeded.SecretKey) (message : Message)
    (randomness : Randomness) :
    digestIndex (digestValue f secretKey message randomness) =
      blockIndex (evalWithAnswerFn f (messageDigestCall secretKey.parameter secretKey.root
        message randomness firstCall : OracleComp HashSpec HashOutput)) := by
  simp only [digestValue, messageDigest, evalWithAnswerFn_bind, evalWithAnswerFn_pure,
    eval_sequenceFin, Concrete.digestIndex_truncate]

theorem signDigestLoop_spec (secretKey : Seeded.SecretKey) (message : Message) (step : Randomness) :
    ∀ (attempts : Nat) (start : Randomness) {randomness : Randomness} {index : Index},
      evalWithAnswerFn f (Seeded.signDigestLoop secretKey message step attempts start
        : OracleComp HashSpec (Option (Randomness × Index))) = some (randomness, index) →
      Landed secretKey.parameter (digestIndex (digestValue f secretKey message randomness)) := by
  intro attempts
  induction attempts with
  | zero => intro start randomness index h; simp [Seeded.signDigestLoop] at h
  | succ attempts ih =>
      intro start randomness index h
      simp only [Seeded.signDigestLoop, Seeded.signAttempt, evalWithAnswerFn_bind] at h
      split at h
      next hl =>
        simp only [evalWithAnswerFn_pure, Option.some.injEq, Prod.mk.injEq] at h
        rw [digestValue_index, ← h.1]
        by_contra hh
        simp only [if_neg hh, evalWithAnswerFn_pure] at hl
        contradiction
      next => exact ih (start + step) h

theorem sequenceDep_spec : ∀ {n : Nat} {α : Fin n → Type}
    (computation : (i : Fin n) → OracleComp HashSpec (Option (α i))) {results : (i : Fin n) → α i},
    evalWithAnswerFn f (sequenceDep computation) = some results →
      ∀ i, evalWithAnswerFn f (computation i) = some (results i)
  | 0, _, _, _, _ => fun i => Fin.elim0 i
  | n + 1, α, computation, results, h => by
      simp only [sequenceDep, evalWithAnswerFn_bind] at h
      cases hhead : evalWithAnswerFn f (computation 0) with
      | none => rw [hhead] at h; simp at h
      | some head =>
          rw [hhead] at h
          simp only [evalWithAnswerFn_bind] at h
          cases htail : evalWithAnswerFn f
              (sequenceDep (α := fun i => α i.succ) fun i => computation i.succ) with
          | none => rw [htail] at h; simp at h
          | some tail =>
              rw [htail] at h
              simp only [evalWithAnswerFn_pure, Option.some.injEq] at h
              subst h
              intro i
              refine Fin.cases ?_ (fun j => ?_) i
              · simpa using hhead
              · simpa using sequenceDep_spec (α := fun i => α i.succ) (fun i => computation i.succ)
                  htail j

/-- `some` of every value when every computation succeeds, `none` otherwise. -/
def allSome {n : Nat} {α : Fin n → Type} (values : (i : Fin n) → Option (α i)) :
    Option ((i : Fin n) → α i) :=
  if h : ∀ i, (values i).isSome then some fun i => (values i).get (h i) else none

theorem allSome_map {n : Nat} {α β : Fin n → Type} (values : (i : Fin n) → Option (α i))
    (g : (i : Fin n) → α i → β i) :
    (allSome fun i => (values i).map (g i)) = (allSome values).map fun found i => g i (found i) := by
  unfold allSome
  by_cases h : ∀ i, (values i).isSome
  · rw [dif_pos h, dif_pos (fun i => by simpa using h i)]
    simp only [Option.map_some]
    congr 1
    funext i
    exact Option.get_map
  · rw [dif_neg h, dif_neg (fun h' => h fun i => by simpa using h' i)]
    rfl

theorem eval_sequenceDep : ∀ {n : Nat} {α : Fin n → Type}
    (computation : (i : Fin n) → OracleComp HashSpec (Option (α i))),
    evalWithAnswerFn f (sequenceDep computation) = allSome fun i => evalWithAnswerFn f (computation i)
  | 0, _, _ => by
      simp only [sequenceDep, evalWithAnswerFn_pure, allSome]
      rw [dif_pos (fun i => Fin.elim0 i)]
      congr 1
      funext i
      exact Fin.elim0 i
  | n + 1, α, computation => by
      simp only [sequenceDep, evalWithAnswerFn_bind]
      have ih := eval_sequenceDep (α := fun i => α i.succ) fun i => computation i.succ
      cases hhead : evalWithAnswerFn f (computation 0) with
      | none =>
          simp only [evalWithAnswerFn_pure, allSome]
          rw [dif_neg (fun h => by simpa [hhead] using h 0)]
      | some head =>
          simp only [evalWithAnswerFn_bind, ih, allSome]
          by_cases hall : ∀ i : Fin n, (evalWithAnswerFn f (computation i.succ)).isSome
          · rw [dif_pos hall]
            simp only [evalWithAnswerFn_pure]
            have hall' : ∀ i : Fin (n + 1), (evalWithAnswerFn f (computation i)).isSome := by
              intro i
              refine Fin.cases ?_ (fun j => hall j) i
              simp [hhead]
            rw [dif_pos hall']
            congr 1
            funext i
            refine Fin.cases ?_ (fun j => ?_) i
            · simp [hhead]
            · simp
          · rw [dif_neg hall]
            simp only [evalWithAnswerFn_pure]
            rw [dif_neg (fun h => hall fun i => h i.succ)]

theorem sequenceLayers_spec {α : Layer → Type}
    (computation : (lay : Layer) → OracleComp HashSpec (Option (α lay)))
    {layers : (lay : Layer) → α lay}
    (h : evalWithAnswerFn f (sequenceLayers computation) = some layers) :
    ∀ lay, evalWithAnswerFn f (computation lay) = some (layers lay) :=
  sequenceDep_spec f computation h

attribute [local irreducible] Seeded.signDigestLoop Seeded.signLayer Seeded.forsOpen
  Seeded.treePath Seeded.treeNode sequenceFin Seeded.forsKey Seeded.treeRoot
  Seeded.spineNode

theorem sign_spec (secretKey : Seeded.SecretKey) (message : Message) {signature : Signature}
    (h : evalWithAnswerFn f (Seeded.sign secretKey message
        : OracleComp HashSpec (Option Signature)) = some signature) :
    Landed secretKey.parameter (digestIndex (digestValue f secretKey message signature.randomness))
      ∧ signature.fors = evalWithAnswerFn f (Seeded.forsOpen secretKey.parameter
          (digestIndex (digestValue f secretKey message signature.randomness))
          (digestLeaves (digestValue f secretKey message signature.randomness)) secretKey.seed
          : OracleComp HashSpec (FTree → TreeOpening))
      ∧ ∀ lay : Layer, evalWithAnswerFn f (Seeded.signLayer secretKey
          (digestIndex (digestValue f secretKey message signature.randomness)) lay
          : OracleComp HashSpec (Option (LayerSignature lay))) = some (signature.layers lay) := by
  rw [Seeded.sign, evalWithAnswerFn_bind, evalWithAnswerFn_bind] at h
  split at h
  next randomness index hloop =>
      have hland := signDigestLoop_spec f secretKey message _ digestAttemptLimit _ hloop
      rw [evalWithAnswerFn_bind, evalWithAnswerFn_bind, evalWithAnswerFn_bind] at h
      split at h
      next layers hlayers =>
          simp only [evalWithAnswerFn_pure, Option.some.injEq] at h
          subst h
          exact ⟨hland, rfl, fun lay => sequenceLayers_spec f _ hlayers lay⟩
      next => exact absurd h (by simp)
  next => exact absurd h (by simp)

/-- The accepting counter recovers the honest leaf, and its pruned path recovers the root of the
layer's tree. -/
theorem eval_layer (secretKey : Seeded.SecretKey) (index : Index) (lay : Layer)
    (hland : Landed secretKey.parameter index) (signature : Signature)
    (h : evalWithAnswerFn f (Seeded.signLayer secretKey index lay
        : OracleComp HashSpec (Option (LayerSignature lay))) = some (signature.layers lay)) :
    evalWithAnswerFn f (otsLeaf secretKey.parameter lay (treeIndexAt index lay)
        (leafIndexAt index lay) (layerMessageValue f secretKey index lay)
        (signature.layers lay).counter (signature.layers lay).chainValues
        : OracleComp HashSpec (Option Digest))
      = some (node f secretKey.parameter lay (treeIndexAt index lay) secretKey.seed 0
          (leafIndexAt index lay).val)
    ∧ evalWithAnswerFn f (treeFold secretKey.parameter lay (treeIndexAt index lay)
        (leafIndexAt index lay) (signaturePath signature lay) (layerHeight lay)
        (node f secretKey.parameter lay (treeIndexAt index lay) secretKey.seed 0
          (leafIndexAt index lay).val) : OracleComp HashSpec Digest)
      = evalWithAnswerFn f (treeRoot secretKey.parameter lay (treeIndexAt index lay)
          secretKey.seed : OracleComp HashSpec Digest) := by
  obtain ⟨hots, hpath⟩ := signLayer_spec f secretKey index lay h
  refine ⟨?_, ?_⟩
  · rw [eval_otsLeaf_of_otsSign f secretKey.parameter lay (treeIndexAt index lay)
      (leafIndexAt index lay) secretKey.seed _ hots, node_zero]
  · apply eval_treeFold_pruned_path f _ _ _ _ _ (kept_leafIndexAt secretKey.parameter index hland lay)
    intro level hlevel
    rw [signaturePath, dif_pos hlevel, hpath]

/-- The walk up the layers from layer `r` reaches the root of the top layer's tree. -/
theorem eval_verifyLayers (secretKey : Seeded.SecretKey) (index : Index)
    (hland : Landed secretKey.parameter index) (signature : Signature)
    (hlayers : ∀ lay : Layer, evalWithAnswerFn f (Seeded.signLayer secretKey index lay
      : OracleComp HashSpec (Option (LayerSignature lay))) = some (signature.layers lay)) :
    ∀ (r : Nat) (hr : r < numLayers),
      evalWithAnswerFn f (verifyLayers secretKey.parameter index signature (r + 1)
          (layerMessageValue f secretKey index ⟨r, hr⟩) : OracleComp HashSpec (Option Digest)) =
        some (evalWithAnswerFn f (treeRoot secretKey.parameter topLayer rootTree secretKey.seed
          : OracleComp HashSpec Digest)) := by
  intro r
  induction r with
  | zero =>
      intro hr
      obtain ⟨hleaf, hfold⟩ := eval_layer f secretKey index ⟨0, hr⟩ hland signature (hlayers _)
      rw [verifyLayers, dif_pos hr]
      simp only [evalWithAnswerFn_bind, hleaf, hfold, if_pos, evalWithAnswerFn_pure]
      rw [show (⟨0, hr⟩ : Layer) = topLayer from rfl, treeIndexAt_top]
  | succ r ih =>
      intro hr
      obtain ⟨hleaf, hfold⟩ := eval_layer f secretKey index ⟨r + 1, hr⟩ hland signature (hlayers _)
      rw [verifyLayers, dif_pos hr]
      simp only [evalWithAnswerFn_bind, hleaf, hfold, Nat.add_one_ne_zero, if_false]
      have habove := layerMessageValue_above f secretKey index ⟨r, by omega⟩ hr
      rw [← habove]
      exact ih (by omega)

/-- Every successful signature verifies under every fixed hash function, for every height, shape
and pruning height. -/
theorem verify_of_parts (secretKey : Seeded.SecretKey) (message : Message) {signature : Signature}
    (hroot : secretKey.root = evalWithAnswerFn f (Seeded.treeRoot secretKey.parameter topLayer
      rootTree secretKey.seed : OracleComp HashSpec Digest))
    (hparts :
    Landed secretKey.parameter (digestIndex (digestValue f secretKey message signature.randomness))
      ∧ signature.fors = evalWithAnswerFn f (Seeded.forsOpen secretKey.parameter
          (digestIndex (digestValue f secretKey message signature.randomness))
          (digestLeaves (digestValue f secretKey message signature.randomness)) secretKey.seed
          : OracleComp HashSpec (FTree → TreeOpening))
      ∧ ∀ lay : Layer, evalWithAnswerFn f (Seeded.signLayer secretKey
          (digestIndex (digestValue f secretKey message signature.randomness)) lay
          : OracleComp HashSpec (Option (LayerSignature lay))) = some (signature.layers lay)) :
    evalWithAnswerFn f (Concrete.verify ⟨secretKey.root, secretKey.parameter⟩ message signature
      : OracleComp HashSpec Bool) = true := by
  obtain ⟨hland, hfors, hlayers⟩ := hparts
  set digest := digestValue f secretKey message signature.randomness
  set index := digestIndex digest with hindex
  have hkey : rootsPayload (evalWithAnswerFn f (forsRecover secretKey.parameter index
      (digestLeaves digest) signature.fors : OracleComp HashSpec ForsKey)) =
      layerMessageValue f secretKey index bottomLayer := by
    rw [hfors, eval_forsRecover, layerMessageValue_bottom]
  have hwalk : evalWithAnswerFn f (verifyLayers secretKey.parameter index signature numLayers
      (layerMessageValue f secretKey index bottomLayer) : OracleComp HashSpec (Option Digest)) =
      some (evalWithAnswerFn f (treeRoot secretKey.parameter topLayer rootTree secretKey.seed
        : OracleComp HashSpec Digest)) := by
    have h := eval_verifyLayers f secretKey index hland signature hlayers (numLayers - 1)
      bottomLayer.isLt
    rwa [Nat.sub_add_cancel numLayers_pos] at h
  have hdig : evalWithAnswerFn f (messageDigest secretKey.parameter secretKey.root message
      signature.randomness : OracleComp HashSpec MessageDigest) = digest := rfl
  rw [Concrete.verify]
  simp only [evalWithAnswerFn_bind, hdig, ← hindex, hkey]
  rw [hwalk, ← hroot]
  simp

/-- Every successful signature verifies under every fixed hash function, for any pruning height. -/
theorem verify_of_sign (secretKey : Seeded.SecretKey) (message : Message) {signature : Signature}
    (hroot : secretKey.root = evalWithAnswerFn f (Seeded.treeRoot secretKey.parameter topLayer
      rootTree secretKey.seed : OracleComp HashSpec Digest))
    (h : evalWithAnswerFn f (Seeded.sign secretKey message
        : OracleComp HashSpec (Option Signature)) = some signature) :
    evalWithAnswerFn f (Concrete.verify ⟨secretKey.root, secretKey.parameter⟩ message signature
      : OracleComp HashSpec Bool) = true := by
  exact verify_of_parts f secretKey message hroot (sign_spec f secretKey message h)

/-- **Correctness.** Key generation supplies the root invariant used by `verify_of_sign`: every
successful signature verifies, under every fixed hash function and every pruning height. -/
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

/-- Successful assembly has the same WOTS, FORS and path invariants as seeded signing. -/
theorem finishSign_spec (secretKey : Seeded.SecretKey) (message : Message)
    (randomness : Randomness) {signature : Signature}
    (hland : Landed secretKey.parameter (digestIndex (digestValue f secretKey message randomness)))
    (h : evalWithAnswerFn f (Seeded.finishSign secretKey message randomness) = some signature) :
    Landed secretKey.parameter (digestIndex (digestValue f secretKey message signature.randomness))
      ∧ signature.fors = evalWithAnswerFn f (Seeded.forsOpen secretKey.parameter
          (digestIndex (digestValue f secretKey message signature.randomness))
          (digestLeaves (digestValue f secretKey message signature.randomness)) secretKey.seed
          : OracleComp HashSpec (FTree → TreeOpening))
      ∧ ∀ lay : Layer, evalWithAnswerFn f (Seeded.signLayer secretKey
          (digestIndex (digestValue f secretKey message signature.randomness)) lay
          : OracleComp HashSpec (Option (LayerSignature lay))) = some (signature.layers lay) := by
  rw [Seeded.finishSign, evalWithAnswerFn_bind, evalWithAnswerFn_bind,
    evalWithAnswerFn_bind] at h
  split at h
  next layers hlayers =>
    simp only [evalWithAnswerFn_pure, Option.some.injEq] at h
    subst h
    exact ⟨hland, rfl, fun lay => sequenceLayers_spec f _ hlayers lay⟩
  next => exact absurd h (by simp)

end FORS.Completeness
