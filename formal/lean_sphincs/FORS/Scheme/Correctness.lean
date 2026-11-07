import FORS.Scheme.Pruning
import FORS.Scheme.DigestView
import FORS.Scheme.Landing

/-! Signer/verifier correctness for every height and shape: every layer, every kept subtree. -/

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
  simp only [layerMessageValue, Seeded.signLayer, Seeded.signLayerWith, evalWithAnswerFn_bind] at h ⊢
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

/-- The message of the bottom layer is the FORS public key. -/
theorem layerMessageValue_bottom (secretKey : Seeded.SecretKey) (index : Index) :
    layerMessageValue f secretKey index bottomLayer = rootPayload (evalWithAnswerFn f
      (Seeded.forsKey secretKey.parameter index secretKey.seed : OracleComp HashSpec Digest)) := by
  have h : ¬(bottomLayer.val + 1 < numLayers) := by
    change ¬(numLayers - 1 + 1 < numLayers); have := numLayers_pos; omega
  simp only [layerMessageValue, Seeded.layerMessage, Seeded.keyMessage, dif_neg h,
    evalWithAnswerFn_bind, evalWithAnswerFn_pure, childTree_path_bottom]

def digestValue (secretKey : Seeded.SecretKey) (message : Message) (randomness : Randomness) :
    MessageDigest :=
  evalWithAnswerFn f (messageDigest secretKey.parameter secretKey.root message randomness
    : OracleComp HashSpec MessageDigest)

theorem signDigestLoop_spec (secretKey : Seeded.SecretKey) (message : Message) (step : Randomness) :
    ∀ (attempts : Nat) (start : Randomness) {randomness : Randomness} {index : Index},
      evalWithAnswerFn f (Seeded.signDigestLoop secretKey message step attempts start
        : OracleComp HashSpec (Option (Randomness × Index))) = some (randomness, index) →
      Landed secretKey.parameter (digestIndex (digestValue f secretKey message randomness)) :=
  fun _ _ _ _ _ => landed_full _ _

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

theorem allSome_spec {n : Nat} {α : Fin n → Type} {values : (i : Fin n) → Option (α i)}
    {results : (i : Fin n) → α i} (h : allSome values = some results) : ∀ i, values i = some (results i) := by
  unfold allSome at h
  split at h
  next hall =>
      simp only [Option.some.injEq] at h
      subst h
      intro i
      simp
  next => exact absurd h (by simp)

/-- The threaded sequence of computations each started from `state` at its index, every one below
the first handing the next the state of the index below it, is the sequence of their values. -/
theorem eval_sequenceThread {σ : Type} (state : Nat → σ) : ∀ {n : Nat} {α : Fin n → Type}
    (computation : (i : Fin n) → σ → OracleComp HashSpec (Option (α i × σ))),
    (∀ (i : Fin n) (value : α i) (next : σ), i.val ≠ 0 →
      evalWithAnswerFn f (computation i (state i.val)) = some (value, next) → next = state (i.val - 1)) →
    evalWithAnswerFn f (sequenceThread computation (state (n - 1))) =
      allSome fun i => (evalWithAnswerFn f (computation i (state i.val))).map Prod.fst
  | 0, _, _, _ => by
      simp only [sequenceThread, evalWithAnswerFn_pure, allSome]
      rw [dif_pos (fun i => Fin.elim0 i)]
      congr 1
      funext i
      exact Fin.elim0 i
  | n + 1, α, computation, hnext => by
      have ih := eval_sequenceThread state (α := fun i => α i.castSucc)
        (fun i => computation i.castSucc) (fun i => hnext i.castSucc)
      rw [Nat.add_sub_cancel]
      simp only [sequenceThread, evalWithAnswerFn_bind]
      cases hhead : evalWithAnswerFn f (computation (Fin.last n) (state n)) with
      | none =>
          simp only [evalWithAnswerFn_pure, allSome]
          rw [dif_neg (fun h => by simpa [hhead] using h (Fin.last n))]
      | some pair =>
          obtain ⟨last, next⟩ := pair
          have hstate : evalWithAnswerFn f (sequenceThread (α := fun i => α i.castSucc)
              (fun i => computation i.castSucc) next) =
              allSome fun i : Fin n => (evalWithAnswerFn f (computation i.castSucc
                (state i.val))).map Prod.fst := by
            rcases Nat.eq_zero_or_pos n with hn | hn
            · subst hn
              simp only [sequenceThread, evalWithAnswerFn_pure, allSome]
              rw [dif_pos (fun i => Fin.elim0 i)]
              congr 1
              funext i
              exact Fin.elim0 i
            · rw [hnext (Fin.last n) last next (by simp; omega) hhead]
              exact ih
          simp only [evalWithAnswerFn_bind, hstate, allSome]
          by_cases hall : ∀ i : Fin n,
              ((evalWithAnswerFn f (computation i.castSucc (state i.val))).map Prod.fst).isSome
          · rw [dif_pos hall]
            simp only [evalWithAnswerFn_pure]
            have hall' : ∀ i : Fin (n + 1),
                ((evalWithAnswerFn f (computation i (state i.val))).map Prod.fst).isSome := by
              intro i
              refine Fin.lastCases ?_ (fun j => by simpa using hall j) i
              simp [hhead]
            rw [dif_pos hall']
            congr 1
            funext i
            refine Fin.lastCases ?_ (fun j => ?_) i
            · simp [hhead]
            · simp
          · rw [dif_neg hall]
            simp only [evalWithAnswerFn_pure]
            rw [dif_neg (fun h => hall fun i => by simpa using h i.castSucc)]

/-- The accepting counter recovers the honest leaf, and the path folds to the root of the layer's
tree, for a layer signature on its own. -/
theorem eval_layerRecover (secretKey : Seeded.SecretKey) (index : Index) (lay : Layer)
    (hland : Landed secretKey.parameter index) {part : LayerSignature lay}
    (h : evalWithAnswerFn f (Seeded.signLayer secretKey index lay
        : OracleComp HashSpec (Option (LayerSignature lay))) = some part) :
    evalWithAnswerFn f (layerRecover secretKey.parameter index lay
        (layerMessageValue f secretKey index lay) part : OracleComp HashSpec (Option Digest))
      = some (evalWithAnswerFn f (treeRoot secretKey.parameter lay (treeIndexAt index lay)
          secretKey.seed : OracleComp HashSpec Digest)) := by
  obtain ⟨hots, hpath⟩ := signLayer_spec f secretKey index lay h
  have hleaf : evalWithAnswerFn f (otsLeaf secretKey.parameter lay (treeIndexAt index lay)
      (leafIndexAt index lay) (layerMessageValue f secretKey index lay) part.counter part.chainValues
      : OracleComp HashSpec (Option Digest)) =
      some (node f secretKey.parameter lay (treeIndexAt index lay) secretKey.seed 0
        (leafIndexAt index lay).val) := by
    rw [eval_otsLeaf_of_otsSign f secretKey.parameter lay (treeIndexAt index lay)
      (leafIndexAt index lay) secretKey.seed _ hots, node_zero]
  have hfold : evalWithAnswerFn f (treeFold secretKey.parameter lay (treeIndexAt index lay)
      (leafIndexAt index lay) (partPath part) (layerHeight lay)
      (node f secretKey.parameter lay (treeIndexAt index lay) secretKey.seed 0
        (leafIndexAt index lay).val) : OracleComp HashSpec Digest) =
      evalWithAnswerFn f (treeRoot secretKey.parameter lay (treeIndexAt index lay)
        secretKey.seed : OracleComp HashSpec Digest) := by
    apply eval_treeFold_pruned_path f _ _ _ _ _ (kept_leafIndexAt secretKey.parameter index hland lay)
    intro level hlevel
    rw [partPath, dif_pos hlevel, hpath]
  simp only [layerRecover, evalWithAnswerFn_bind, hleaf, hfold, evalWithAnswerFn_pure]

/-- The layer above a layer below the top. -/
def aboveLayer (lay : Layer) (h : lay.val ≠ 0) : Layer := ⟨lay.val - 1, by have := lay.isLt; omega⟩

/-- What the key of a layer signs, as a digest: the root of the tree below, or the FORS public key
at the bottom layer. -/
def belowValue (secretKey : Seeded.SecretKey) (index : Index) (lay : Layer) : Digest :=
  if hbelow : lay.val + 1 < numLayers then
    evalWithAnswerFn f (Seeded.treeRoot secretKey.parameter ⟨lay.val + 1, hbelow⟩
      (treeIndexAt index ⟨lay.val + 1, hbelow⟩) secretKey.seed : OracleComp HashSpec Digest)
  else evalWithAnswerFn f (Seeded.forsKey secretKey.parameter index secretKey.seed
    : OracleComp HashSpec Digest)

theorem rootPayload_belowValue (secretKey : Seeded.SecretKey) (index : Index) (lay : Layer) :
    rootPayload (belowValue f secretKey index lay) = layerMessageValue f secretKey index lay := by
  unfold belowValue
  by_cases hbelow : lay.val + 1 < numLayers
  · rw [dif_pos hbelow, layerMessageValue_above f secretKey index lay hbelow]
  · rw [dif_neg hbelow]
    have hlay : lay = bottomLayer := Fin.ext (by change lay.val = numLayers - 1; omega)
    subst hlay
    rw [layerMessageValue_bottom]

/-- Above a layer below the top, what is signed is that layer's root. -/
theorem belowValue_aboveLayer (secretKey : Seeded.SecretKey) (index : Index) (lay : Layer)
    (h : lay.val ≠ 0) :
    belowValue f secretKey index (aboveLayer lay h) = evalWithAnswerFn f (Seeded.treeRoot
      secretKey.parameter lay (treeIndexAt index lay) secretKey.seed : OracleComp HashSpec Digest) := by
  have hbelow : (aboveLayer lay h).val + 1 < numLayers := by
    simp only [aboveLayer]; have := lay.isLt; omega
  have hlay : (⟨(aboveLayer lay h).val + 1, hbelow⟩ : Layer) = lay :=
    Fin.ext (by simp only [aboveLayer]; omega)
  unfold belowValue
  rw [dif_pos hbelow, hlay]

/-- One step of the signer from the honest value below its layer: the layer's signature, and the
honest value below the layer above (the same value at the top, which has none above). -/
theorem eval_layerStep (secretKey : Seeded.SecretKey) (index : Index)
    (hland : Landed secretKey.parameter index) (lay : Layer) :
    evalWithAnswerFn f (Seeded.layerStep secretKey index lay (belowValue f secretKey index lay)
        : OracleComp HashSpec (Option (LayerSignature lay × Digest))) =
      (evalWithAnswerFn f (Seeded.signLayer secretKey index lay
          : OracleComp HashSpec (Option (LayerSignature lay)))).map fun part =>
        (part, if h : lay.val = 0 then belowValue f secretKey index lay
          else belowValue f secretKey index (aboveLayer lay h)) := by
  have hsign : evalWithAnswerFn f (Seeded.signLayer secretKey index lay
      : OracleComp HashSpec (Option (LayerSignature lay))) =
      evalWithAnswerFn f (Seeded.signLayerWith secretKey index lay
        (rootPayload (belowValue f secretKey index lay))
        : OracleComp HashSpec (Option (LayerSignature lay))) := by
    rw [rootPayload_belowValue]
    simp only [Seeded.signLayer, evalWithAnswerFn_bind, layerMessageValue]
  rw [Seeded.layerStep, evalWithAnswerFn_bind]
  cases hpart : evalWithAnswerFn f (Seeded.signLayerWith secretKey index lay
      (rootPayload (belowValue f secretKey index lay))
      : OracleComp HashSpec (Option (LayerSignature lay))) with
  | none => simp [hsign, hpart]
  | some part =>
      have hspec : evalWithAnswerFn f (Seeded.signLayer secretKey index lay
          : OracleComp HashSpec (Option (LayerSignature lay))) = some part := hsign.trans hpart
      rw [hsign, hpart]
      dsimp only
      by_cases htop : lay.val = 0
      · simp [htop]
      · rw [if_neg htop, dif_neg htop, rootPayload_belowValue]
        simp only [evalWithAnswerFn_bind, eval_layerRecover f secretKey index lay hland hspec,
          evalWithAnswerFn_pure, Option.map_some, belowValue_aboveLayer]

/-- The signer's layers, threaded from the FORS public key up, are the layers' signatures. -/
theorem eval_signLayers (secretKey : Seeded.SecretKey) (index : Index)
    (hland : Landed secretKey.parameter index) :
    evalWithAnswerFn f (sequenceThread (fun lay below => Seeded.layerStep secretKey index lay below)
        (evalWithAnswerFn f (Seeded.forsKey secretKey.parameter index secretKey.seed
          : OracleComp HashSpec Digest))
        : OracleComp HashSpec (Option ((lay : Layer) → LayerSignature lay))) =
      allSome fun lay => evalWithAnswerFn f (Seeded.signLayer secretKey index lay
        : OracleComp HashSpec (Option (LayerSignature lay))) := by
  let state : Nat → Digest := fun v =>
    if h : v < numLayers then belowValue f secretKey index ⟨v, h⟩ else 0
  have hstate : ∀ lay : Layer, state lay.val = belowValue f secretKey index lay := fun lay => by
    simp only [state, dif_pos lay.isLt]
  have hbottom : evalWithAnswerFn f (Seeded.forsKey secretKey.parameter index secretKey.seed
      : OracleComp HashSpec Digest) = state (numLayers - 1) := by
    rw [show numLayers - 1 = bottomLayer.val from rfl, hstate, belowValue,
      dif_neg (by change ¬(numLayers - 1 + 1 < numLayers); omega)]
  rw [hbottom, eval_sequenceThread f state (fun lay below => Seeded.layerStep secretKey index lay below)]
  · congr 1
    funext lay
    rw [hstate lay, eval_layerStep f secretKey index hland lay, Option.map_map]
    cases evalWithAnswerFn f (Seeded.signLayer secretKey index lay
      : OracleComp HashSpec (Option (LayerSignature lay))) <;> rfl
  · intro lay part next hlay h
    rw [hstate lay, eval_layerStep f secretKey index hland lay] at h
    simp only [Option.map_eq_some_iff, Prod.mk.injEq] at h
    obtain ⟨_, _, _, hnext⟩ := h
    rw [← hnext, dif_neg hlay, ← hstate]
    rfl

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
      simp only [evalWithAnswerFn_bind, eval_forsPublicKey_forsRecover] at h
      rw [eval_signLayers f secretKey _ (landed_full _ _)] at h
      split at h
      next layers hlayers =>
          simp only [evalWithAnswerFn_pure, Option.some.injEq] at h
          subst h
          exact ⟨hland, rfl, allSome_spec hlayers⟩
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
  have hkey : rootPayload (evalWithAnswerFn f (forsPublicKey secretKey.parameter index
      (evalWithAnswerFn f (forsRecover secretKey.parameter index (digestLeaves digest) signature.fors
        : OracleComp HashSpec ForsKey)) : OracleComp HashSpec Digest)) =
      layerMessageValue f secretKey index bottomLayer := by
    rw [hfors, eval_forsPublicKey_forsRecover, layerMessageValue_bottom]
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
    (derivePublicSeed seed : OracleComp HashSpec PublicParameter) = parameter at hkey
  generalize hprf : evalWithAnswerFn f
    (derivePrf seed : OracleComp HashSpec HashOutput) = prf at hkey
  generalize hrootval : evalWithAnswerFn f
    (treeRoot parameter topLayer rootTree seed : OracleComp HashSpec Digest) = root at hkey
  obtain ⟨hpk, hsk⟩ := hkey
  subst publicKey
  subst secretKey
  exact verify_of_sign f ⟨seed, prf, parameter, root⟩ message hrootval.symm hsign

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
  rw [Seeded.finishSign] at h
  simp only [evalWithAnswerFn_bind, eval_forsPublicKey_forsRecover] at h
  rw [eval_signLayers f secretKey _ (landed_full _ _)] at h
  split at h
  next layers hlayers =>
    simp only [evalWithAnswerFn_pure, Option.some.injEq] at h
    subst h
    exact ⟨hland, rfl, allSome_spec hlayers⟩
  next => exact absurd h (by simp)

end FORS.Completeness
