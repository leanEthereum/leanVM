import FORS.LazyRun.FixedRun
import FORS.Classification.Reference
import FORS.Classification.Hidden

/-! Accepted-signature classification, walking down the layers. At each layer the verifier's fold
equals the honest root of the layer's tree on the forgery's path (the public root at the top):
either the tree classification gives a hit, or the WOTS+C classification of the layer's key gives
an exception, or the key's message is the canonical one, which makes the fold of the layer below
the honest root of its tree. At the bottom the canonical message is the FORS key. Every
exception other than a tree hit is at a key on the path of a landed index. -/

open OracleComp OracleSpec

namespace FORS.Security.SignatureWitness
open Concrete PrunedGraph

attribute [local irreducible] messageDigest forsRecover otsLeaf treeFold
  Seeded.forsKey Seeded.treeRoot Seeded.treePath chainWalk encode

variable [Params]

/-- The three WOTS exceptions at the key of layer `lay` of the forgery's path. -/
def WotsException (f : QueryImpl HashSpec Id) (pk : PublicKey) (seed : MasterSeed)
    (message : Message) (signature : Signature) (lay : Layer) : Prop :=
  let leaf := index f pk message signature
  let inputs := trace f pk message signature
  ReferenceChoice.EncodingMatch f pk.parameter lay (keyTree leaf lay) (keyLeaf leaf lay)
    (canonicalMessage f pk.parameter seed leaf lay) inputs ∨
  Wots.LeafOutputMatch f pk.parameter lay (keyTree leaf lay) (keyLeaf leaf lay)
    (Completeness.otsSecret f pk.parameter lay (keyTree leaf lay) (keyLeaf leaf lay) seed) inputs ∨
  Wots.ChainException f pk.parameter lay (keyTree leaf lay) (keyLeaf leaf lay)
    (chosenWord f pk.parameter seed leaf lay)
    (Completeness.otsSecret f pk.parameter lay (keyTree leaf lay) (keyLeaf leaf lay) seed) inputs

/-- A canonical WOTS and tree opening at every layer of a landed index whose FORS openings recover
the canonical FORS key. -/
def RecoveredOpening (f : QueryImpl HashSpec Id) (pk : PublicKey) (seed : MasterSeed)
    (message : Message) (signature : Signature) (referenceCounter : Layer → Counter) : Prop :=
  let leaf := index f pk message signature
  Landed pk.parameter leaf ∧
    (∀ lay, CanonicalLayer f pk seed leaf signature lay (referenceCounter lay)
      (chosenWord f pk.parameter seed leaf lay)) ∧
    verificationFors f pk message signature = canonicalFors f pk.parameter seed leaf

/-- At a crossing above the top layer's kept subtree, the forged path enters at the boundary node. -/
theorem crossing_boundary (parameter : PublicParameter) (leaf reference : LeafIndex)
    (hreference : Kept parameter topLayer reference) (level : Nat) (hlower : keptHeight topLayer ≤ level)
    (hparent : leaf.val / 2 ^ (level + 1) = reference.val / 2 ^ (level + 1))
    (hbit : leaf.val.testBit level ≠ reference.val.testBit level) :
    leaf.val / 2 ^ level = boundaryIndex parameter level := by
  have hpos : keptPosition parameter topLayer = subtreePosition parameter := if_pos rfl
  have hspine : reference.val / 2 ^ level = spineIndex parameter level := by
    have hsum : keptHeight topLayer + (level - keptHeight topLayer) = level := Nat.add_sub_of_le hlower
    rw [← hsum, Completeness.kept_div parameter topLayer reference hreference, hpos]
    simp only [spineIndex, Nat.add_sub_cancel_left]
  unfold boundaryIndex
  rw [← hspine]
  have hl : (leaf.val / 2 ^ level) / 2 = (reference.val / 2 ^ level) / 2 := by
    rw [Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul, ← Nat.pow_succ]
    exact hparent
  have hbl : (leaf.val / 2 ^ level) % 2 ≠ (reference.val / 2 ^ level) % 2 := by
    intro heq
    apply hbit
    rw [Nat.testBit_eq_decide_div_mod_eq, Nat.testBit_eq_decide_div_mod_eq, heq]
  apply Nat.eq_of_testBit_eq
  intro bit
  show (leaf.val / 2 ^ level).testBit bit = ((reference.val / 2 ^ level) ^^^ 1).testBit bit
  rw [Nat.testBit_xor]
  cases bit with
  | zero =>
      simp only [Nat.testBit_zero]
      have h1 := Nat.mod_two_eq_zero_or_one (leaf.val / 2 ^ level)
      have h2 := Nat.mod_two_eq_zero_or_one (reference.val / 2 ^ level)
      rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;> simp_all
  | succ bit =>
      rw [Nat.testBit_succ, Nat.testBit_succ, hl]
      simp [Nat.testBit_succ]

/-- The outside-subtree witness of the top layer's root tree, with the surrogate's exact boundary
address. -/
theorem outside_witness_address (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (seed : MasterSeed) (leaf reference : LeafIndex) (path : Nat → Digest) (value : Digest)
    (hb : 0 < keptHeight topLayer) (hreference : Kept parameter topLayer reference)
    (houtside : ¬Kept parameter topLayer leaf) (hleaf : leaf.val < 2 ^ layerHeight topLayer)
    (hrange : reference.val < 2 ^ layerHeight topLayer)
    (hfold : evalWithAnswerFn f (treeFold parameter topLayer rootTree leaf path (layerHeight topLayer) value :
      OracleComp HashSpec Digest) =
      evalWithAnswerFn f (Seeded.treeRoot parameter topLayer rootTree seed : OracleComp HashSpec Digest)) :
    (∃ level, level < layerHeight topLayer ∧
      MerkleMatch f parameter (fun height index => .node topLayer rootTree height index)
        leaf.val reference.val path (canonicalTreePath f parameter topLayer rootTree seed reference)
        value (Completeness.node f parameter topLayer rootTree seed 0 reference.val) level) ∨
    ∃ level, level < layerHeight topLayer ∧
      SurrogatePreimage f parameter topLayer rootTree seed leaf path value level ∧
      leaf.val / 2 ^ level = boundaryIndex parameter level := by
  have hparent : leaf.val / 2 ^ layerHeight topLayer = reference.val / 2 ^ layerHeight topLayer := by
    rw [Nat.div_eq_of_lt hleaf, Nat.div_eq_of_lt hrange]
  have hroot := canonicalTreePath_root f parameter topLayer rootTree seed reference hreference
  have hfold' : merkleValue f parameter (fun height index => .node topLayer rootTree height index)
      leaf.val path value (layerHeight topLayer) =
      merkleValue f parameter (fun height index => .node topLayer rootTree height index)
        reference.val (canonicalTreePath f parameter topLayer rootTree seed reference)
        (Completeness.node f parameter topLayer rootTree seed 0 reference.val) (layerHeight topLayer) := by
    rw [hroot, merkleValue, merkleFold_treeFold]
    exact hfold
  rcases merkleFold_classification f parameter (fun height index => .node topLayer rootTree height index)
    leaf.val reference.val path (canonicalTreePath f parameter topLayer rootTree seed reference)
    value (Completeness.node f parameter topLayer rootTree seed 0 reference.val) (layerHeight topLayer)
    hparent hfold' with hgood | ⟨level, hlevel, hparent, hbit, hcross⟩ | hmatch
  · have heq : leaf = reference := Fin.ext hgood.1
    exact False.elim (houtside (heq ▸ hreference))
  · have hlower : keptHeight topLayer ≤ level := by
      by_contra hnot
      have hle : level + 1 ≤ keptHeight topLayer := by omega
      have hquot := quotient_eq_above hle hparent
      apply houtside
      unfold Kept
      exact hquot.trans hreference
    have hpositive : 0 < level := lt_of_lt_of_le hb hlower
    refine Or.inr ⟨level, hlevel, ⟨hlower, hpositive, ?_⟩,
      crossing_boundary parameter leaf reference hreference level hlower hparent hbit⟩
    rw [← merkleValue_succ, Nat.sub_add_cancel (by omega : 1 ≤ level), hcross,
      canonicalTreePath_surrogate f parameter topLayer rootTree seed reference level hlower hlevel]
  · exact Or.inl hmatch

/-- The verifier's tree exception at the layer `j` steps above the bottom: a match against the
honest tree of a retained tree at a kept reference leaf, or at the top layer a surrogate preimage at
its boundary address. -/
def TreeHit (f : QueryImpl HashSpec Id) (pk : PublicKey) (seed : MasterSeed)
    (message : Message) (signature : Signature) (j : Nat) : Prop :=
  let leaf := index f pk message signature
  let lay := layerUp j
  TreeActive pk.parameter lay (keyTree leaf lay) ∧
  ∃ value, layerLeaf f pk.parameter leaf signature lay (verificationMessage f pk message signature j) =
      some value ∧
    ContainsRun f (trace f pk message signature)
      (treeFold pk.parameter lay (keyTree leaf lay) (keyLeaf leaf lay) (signaturePath signature lay)
        (layerHeight lay) value) ∧
    ((∃ reference : LeafIndex, KeyActive pk.parameter lay (keyTree leaf lay) reference ∧
        ∃ level, level < layerHeight lay ∧
      MerkleMatch f pk.parameter (fun height index => .node lay (keyTree leaf lay) height index)
        (keyLeaf leaf lay).val reference.val (signaturePath signature lay)
        (canonicalTreePath f pk.parameter lay (keyTree leaf lay) seed reference)
        value (Completeness.node f pk.parameter lay (keyTree leaf lay) seed 0 reference.val) level) ∨
    (lay = topLayer ∧ ∃ level, level < layerHeight lay ∧
      SurrogatePreimage f pk.parameter lay (keyTree leaf lay) seed (keyLeaf leaf lay)
        (signaturePath signature lay) value level ∧
      (keyLeaf leaf lay).val / 2 ^ level = boundaryIndex pk.parameter level))

/-- The canonical opening of one layer with its chosen counter. -/
def ChosenLayer (f : QueryImpl HashSpec Id) (pk : PublicKey) (seed : MasterSeed)
    (message : Message) (signature : Signature) (lay : Layer) : Prop :=
  let leaf := index f pk message signature
  ∃ counter, chosenCounter f pk.parameter seed leaf lay = some counter ∧
    CanonicalLayer f pk seed leaf signature lay counter (chosenWord f pk.parameter seed leaf lay)

/-- **One layer of the walk.** If the fold of the layer `j` steps above the bottom is the honest root
of its tree on the path of a landed index, the layer is canonical and its key's message is the
canonical one, or the layer has a tree hit or a WOTS exception. -/
theorem layer_step (f : QueryImpl HashSpec Id) (pk : PublicKey) (seed : MasterSeed)
    (message : Message) (signature : Signature)
    (hverified : evalWithAnswerFn f (Concrete.verify pk message signature : OracleComp HashSpec Bool) = true)
    (hland : Landed pk.parameter (index f pk message signature)) (j : Nat) (hj : j < numLayers)
    (hfold : walkFold f pk.parameter (index f pk message signature) signature
        (verificationFors f pk message signature) j =
      evalWithAnswerFn f (Seeded.treeRoot pk.parameter (layerUp j)
        (keyTree (index f pk message signature) (layerUp j)) seed : OracleComp HashSpec Digest)) :
    (ChosenLayer f pk seed message signature (layerUp j) ∧
        verificationMessage f pk message signature j =
          canonicalMessage f pk.parameter seed (index f pk message signature) (layerUp j)) ∨
      TreeHit f pk seed message signature j ∨
      WotsException f pk seed message signature (layerUp j) := by
  obtain ⟨-, hlayers⟩ := verified_layers f pk message signature hverified
  have hidx : verificationIndex f pk message signature = index f pk message signature := rfl
  simp only [hidx] at hlayers
  obtain ⟨⟨value, hvalue⟩, hrunLeaf, hrunFold⟩ := hlayers j hj
  set leaf := index f pk message signature with hleafdef
  set lay := layerUp j with hlaydef
  change layerLeaf f pk.parameter leaf signature lay (verificationMessage f pk message signature j) =
    some value at hvalue
  have hfold' : evalWithAnswerFn f (treeFold pk.parameter lay (keyTree leaf lay) (keyLeaf leaf lay)
      (signaturePath signature lay) (layerHeight lay) value : OracleComp HashSpec Digest) =
      evalWithAnswerFn f (Seeded.treeRoot pk.parameter lay (keyTree leaf lay) seed :
        OracleComp HashSpec Digest) := by
    rw [← hfold]
    change _ = layerFold f pk.parameter leaf signature lay
      ((layerLeaf f pk.parameter leaf signature lay (verificationMessage f pk message signature j)).getD 0)
    rw [hvalue, Option.getD_some]
    rfl
  have hrunFold' : ContainsRun f (trace f pk message signature)
      (treeFold pk.parameter lay (keyTree leaf lay) (keyLeaf leaf lay) (signaturePath signature lay)
        (layerHeight lay) value) := by
    have h := hrunFold
    change ContainsRun f _ (treeFold pk.parameter lay (keyTree leaf lay) (keyLeaf leaf lay)
      (signaturePath signature lay) (layerHeight lay)
      ((layerLeaf f pk.parameter leaf signature lay (verificationMessage f pk message signature j)).getD 0)) at h
    rwa [hvalue, Option.getD_some] at h
  have hkept : Kept pk.parameter lay (keyLeaf leaf lay) :=
    Completeness.kept_leafIndexAt pk.parameter leaf hland lay
  have hactive : KeyActive pk.parameter lay (keyTree leaf lay) (keyLeaf leaf lay) := ⟨leaf, hland, rfl, rfl⟩
  rcases inside_subtree_treeFold_witness f pk.parameter lay (keyTree leaf lay) seed (keyLeaf leaf lay)
      (signaturePath signature lay) value hkept hfold' with hopen | hmatch
  · have hcanonical : evalWithAnswerFn f (otsLeaf pk.parameter lay (keyTree leaf lay) (keyLeaf leaf lay)
        (verificationMessage f pk message signature j) (signature.layers lay).counter
        (signature.layers lay).chainValues : OracleComp HashSpec (Option Digest)) =
        some (Wots.canonicalLeaf f pk.parameter lay (keyTree leaf lay) (keyLeaf leaf lay)
          (Completeness.otsSecret f pk.parameter lay (keyTree leaf lay) (keyLeaf leaf lay) seed)) :=
      hvalue.trans (congrArg some (hopen.1.trans (canonical_wots_leaf f pk.parameter seed _ _ _)))
    obtain ⟨candidate, hencode⟩ : ∃ candidate, evalWithAnswerFn f
        (encode pk.parameter lay (keyTree leaf lay) (keyLeaf leaf lay)
          (verificationMessage f pk message signature j) (signature.layers lay).counter :
          OracleComp HashSpec (Option Encoding)) = some candidate := by
      cases henc : evalWithAnswerFn f
          (encode pk.parameter lay (keyTree leaf lay) (keyLeaf leaf lay)
            (verificationMessage f pk message signature j) (signature.layers lay).counter :
            OracleComp HashSpec (Option Encoding)) with
      | none =>
          simp only [otsLeaf, evalWithAnswerFn_bind, henc, evalWithAnswerFn_pure,
            reduceCtorEq] at hcanonical
      | some candidate => exact ⟨candidate, rfl⟩
    rcases ReferenceChoice.otsLeaf_classification f pk.parameter lay (keyTree leaf lay) (keyLeaf leaf lay)
        (canonicalMessage f pk.parameter seed leaf lay)
        (Completeness.otsSecret f pk.parameter lay (keyTree leaf lay) (keyLeaf leaf lay) seed)
        (verificationMessage f pk message signature j) (signature.layers lay).counter
        (signature.layers lay).chainValues candidate (trace f pk message signature)
        hencode hrunLeaf hcanonical with
      ⟨counter, hselected, hmsg, hcounter, hvalues⟩ | hencoding | hleafMatch | hchain
    · refine Or.inl ⟨⟨counter, ?_, hcounter, funext hvalues, ?_⟩, hmsg⟩
      · simp only [chosenCounter, ← hleafdef, hselected, Option.map_some]
      · funext level
        have hp := hopen.2 level.val level.isLt
        simpa only [signaturePath, canonicalTreePath, dif_pos level.isLt] using hp
    · exact Or.inr (Or.inr (Or.inl hencoding))
    · exact Or.inr (Or.inr (Or.inr (Or.inl hleafMatch)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr hchain)))
  · exact Or.inr (Or.inl ⟨⟨leaf, hland, rfl⟩, value, hvalue, hrunFold',
      Or.inl ⟨keyLeaf leaf lay, hactive, hmatch⟩⟩)

/-- **The walk down the layers.** If the fold of the layer `j` steps above the bottom is the honest
root of its tree on the path of a landed index, then the layers up to `j` are canonical and the
FORS key is recovered, or some layer up to `j` has a tree hit or a WOTS exception. -/
theorem walk_classification (f : QueryImpl HashSpec Id) (pk : PublicKey) (seed : MasterSeed)
    (message : Message) (signature : Signature)
    (hverified : evalWithAnswerFn f (Concrete.verify pk message signature : OracleComp HashSpec Bool) = true)
    (hland : Landed pk.parameter (index f pk message signature)) :
    ∀ j, j < numLayers →
      walkFold f pk.parameter (index f pk message signature) signature
          (verificationFors f pk message signature) j =
        evalWithAnswerFn f (Seeded.treeRoot pk.parameter (layerUp j)
          (keyTree (index f pk message signature) (layerUp j)) seed : OracleComp HashSpec Digest) →
      ((∀ j', j' ≤ j → ChosenLayer f pk seed message signature (layerUp j')) ∧
          verificationFors f pk message signature = canonicalFors f pk.parameter seed
            (index f pk message signature)) ∨
        (∃ j', j' ≤ j ∧ TreeHit f pk seed message signature j') ∨
        (∃ j', j' ≤ j ∧ WotsException f pk seed message signature (layerUp j')) := by
  intro j
  induction j with
  | zero =>
      intro hj hfold
      rcases layer_step f pk seed message signature hverified hland 0 hj hfold with
        ⟨hchosen, hmsg⟩ | htree | hwots
      · left
        refine ⟨fun j' hj' => by rw [Nat.le_zero.mp hj']; exact hchosen, ?_⟩
        rw [canonicalMessage_bottom] at hmsg
        exact rootsPayload_injective hmsg
      · exact Or.inr (Or.inl ⟨0, le_rfl, htree⟩)
      · exact Or.inr (Or.inr ⟨0, le_rfl, hwots⟩)
  | succ j ih =>
      intro hj hfold
      rcases layer_step f pk seed message signature hverified hland (j + 1) hj hfold with
        ⟨hchosen, hmsg⟩ | htree | hwots
      · rw [canonicalMessage_succ f pk.parameter seed _ j hj] at hmsg
        have hbelow : walkFold f pk.parameter (index f pk message signature) signature
            (verificationFors f pk message signature) j =
            evalWithAnswerFn f (Seeded.treeRoot pk.parameter (layerUp j)
              (keyTree (index f pk message signature) (layerUp j)) seed : OracleComp HashSpec Digest) := by
          have h : rootPayload (walkFold f pk.parameter (index f pk message signature) signature
              (verificationFors f pk message signature) j) = _ := hmsg
          exact bytesLE_injective h
        rcases ih (by omega) hbelow with ⟨hall, hfors⟩ | ⟨j', hj', htree⟩ | ⟨j', hj', hwots⟩
        · refine Or.inl ⟨fun j' hj' => ?_, hfors⟩
          rcases Nat.lt_or_ge j' (j + 1) with hlt | hge
          · exact hall j' (by omega)
          · rw [show j' = j + 1 by omega]; exact hchosen
        · exact Or.inr (Or.inl ⟨j', by omega, htree⟩)
        · exact Or.inr (Or.inr ⟨j', by omega, hwots⟩)
      · exact Or.inr (Or.inl ⟨j + 1, le_rfl, htree⟩)
      · exact Or.inr (Or.inr ⟨j + 1, le_rfl, hwots⟩)

/-- **Recovered canonical FORS key, a tree hit, or a WOTS exception on the path of a landed
index.** -/
theorem accepted_recovered_classification (f : QueryImpl HashSpec Id) (pk : PublicKey)
    (seed : MasterSeed) (message : Message) (signature : Signature) (hb : 0 < keptHeight topLayer)
    (hroot : pk.root = evalWithAnswerFn f
      (Seeded.treeRoot pk.parameter topLayer rootTree seed : OracleComp HashSpec Digest))
    (hverified : evalWithAnswerFn f
      (Concrete.verify pk message signature : OracleComp HashSpec Bool) = true) :
    (∃ counter : Layer → Counter,
      (∀ lay, chosenCounter f pk.parameter seed (index f pk message signature) lay = some (counter lay)) ∧
      RecoveredOpening f pk seed message signature counter) ∨
    (∃ j, j < numLayers ∧ TreeHit f pk seed message signature j) ∨
    (Landed pk.parameter (index f pk message signature) ∧
      ∃ lay, WotsException f pk seed message signature lay) := by
  obtain ⟨hpk, hlayers⟩ := verified_layers f pk message signature hverified
  have hidx : verificationIndex f pk message signature = index f pk message signature := rfl
  simp only [hidx] at hlayers hpk
  set leaf := index f pk message signature with hleafdef
  have htop : layerUp (numLayers - 1) = topLayer := layerUp_top
  have hd : numLayers - 1 < numLayers := Nat.sub_lt numLayers_pos Nat.one_pos
  have hfoldTop : walkFold f pk.parameter leaf signature (verificationFors f pk message signature)
      (numLayers - 1) = evalWithAnswerFn f (Seeded.treeRoot pk.parameter (layerUp (numLayers - 1))
        (keyTree leaf (layerUp (numLayers - 1))) seed : OracleComp HashSpec Digest) := by
    rw [htop]
    simp only [keyTree, Completeness.treeIndexAt_top, ← hroot]
    exact hpk
  by_cases hland : Landed pk.parameter leaf
  · rcases walk_classification f pk seed message signature hverified hland (numLayers - 1) hd hfoldTop with
      ⟨hall, hfors⟩ | ⟨j, hj, htree⟩ | ⟨j, hj, hwots⟩
    · have hchosen : ∀ lay, ChosenLayer f pk seed message signature lay := by
        intro lay
        have hlay : layerUp (numLayers - 1 - lay.val) = lay := by
          apply Fin.ext; simp only [layerUp]; have := lay.isLt; omega
        rw [← hlay]
        exact hall _ (by omega)
      choose counter hcounter hcanon using hchosen
      exact Or.inl ⟨counter, hcounter, hland, hcanon, hfors⟩
    · exact Or.inr (Or.inl ⟨j, by omega, htree⟩)
    · exact Or.inr (Or.inr ⟨hland, layerUp j, hwots⟩)
  · obtain ⟨⟨value, hvalue⟩, -, hrunFold⟩ := hlayers (numLayers - 1) hd
    obtain ⟨landed, hlanded⟩ := exists_landed pk.parameter
    rw [htop] at hvalue hrunFold
    have hfold' : evalWithAnswerFn f (treeFold pk.parameter topLayer rootTree (keyLeaf leaf topLayer)
        (signaturePath signature topLayer) (layerHeight topLayer) value : OracleComp HashSpec Digest) =
        evalWithAnswerFn f (Seeded.treeRoot pk.parameter topLayer rootTree seed :
          OracleComp HashSpec Digest) := by
      rw [← hroot, ← hpk]
      unfold walkFold
      rw [htop]
      change _ = layerFold f pk.parameter leaf signature topLayer
        ((layerLeaf f pk.parameter leaf signature topLayer
          (verificationMessage f pk message signature (numLayers - 1))).getD 0)
      rw [hvalue, Option.getD_some]
      unfold layerFold
      rw [Completeness.treeIndexAt_top]
    have hrunFold' : ContainsRun f (trace f pk message signature)
        (treeFold pk.parameter topLayer rootTree (keyLeaf leaf topLayer) (signaturePath signature topLayer)
          (layerHeight topLayer) value) := by
      have h := hrunFold
      rw [hvalue, Option.getD_some, Completeness.treeIndexAt_top] at h
      exact h
    have houtside : ¬Kept pk.parameter topLayer (keyLeaf leaf topLayer) :=
      fun h => hland (Completeness.landed_of_kept_top pk.parameter leaf h)
    have hhit : TreeHit f pk seed message signature (numLayers - 1) := by
      unfold TreeHit
      simp only [keyTree, keyLeaf]
      rw [htop, Completeness.treeIndexAt_top]
      refine ⟨treeActive_rootTree pk.parameter, value, hvalue, hrunFold', ?_⟩
      rcases outside_witness_address f pk.parameter seed (keyLeaf leaf topLayer)
          (leafIndexAt landed topLayer) (signaturePath signature topLayer) value hb
          (Completeness.kept_leafIndexAt pk.parameter landed hlanded topLayer) houtside
          (Completeness.leafIndexAt_lt leaf topLayer) (Completeness.leafIndexAt_lt landed topLayer)
          hfold' with hmatch | hsurrogate
      · exact Or.inl ⟨leafIndexAt landed topLayer,
          ⟨landed, hlanded, by rw [Completeness.treeIndexAt_top], rfl⟩, hmatch⟩
      · exact Or.inr ⟨rfl, hsurrogate⟩
    exact Or.inr (Or.inl ⟨numLayers - 1, hd, hhit⟩)

/-- **Canonical opening, a tree hit, or an exception on the path of a landed index.** -/
theorem accepted_full_classification (f : QueryImpl HashSpec Id) (pk : PublicKey)
    (seed : MasterSeed) (message : Message) (signature : Signature) (hb : 0 < keptHeight topLayer)
    (hroot : pk.root = evalWithAnswerFn f
      (Seeded.treeRoot pk.parameter topLayer rootTree seed : OracleComp HashSpec Digest))
    (hverified : evalWithAnswerFn f
      (Concrete.verify pk message signature : OracleComp HashSpec Bool) = true) :
    (∃ counter : Layer → Counter,
      (∀ lay, chosenCounter f pk.parameter seed (index f pk message signature) lay = some (counter lay)) ∧
      CanonicalOpening f pk seed message signature counter
        (chosenWord f pk.parameter seed (index f pk message signature))) ∨
    (∃ j, j < numLayers ∧ TreeHit f pk seed message signature j) ∨
    (Landed pk.parameter (index f pk message signature) ∧
      ((∃ lay, WotsException f pk seed message signature lay) ∨ ForsException f pk seed message signature)) := by
  rcases accepted_recovered_classification f pk seed message signature hb hroot hverified with
    ⟨counter, hcounter, hland, hlayers, hfors⟩ | htree | ⟨hland, hwots⟩
  · rcases Fors.recover_classification f pk.parameter (index f pk message signature) seed
        (digestLeaves (verificationDigest f pk message signature)) signature.fors
        hfors with hforsOpening | hforsException
    · exact Or.inl ⟨counter, hcounter, hland, hlayers, hforsOpening⟩
    · refine Or.inr (Or.inr ⟨hland, Or.inr ⟨hforsException, ?_⟩⟩)
      obtain ⟨input, canonicalInput, hinput, hne, hout⟩ :=
        Fors.Exception.queried_output_match f pk.parameter (index f pk message signature) seed
          (digestLeaves (verificationDigest f pk message signature)) signature.fors
          hforsException
      exact ⟨input, canonicalInput, verification_fors_run f pk message signature input hinput, hne, hout⟩
  · exact Or.inr (Or.inl htree)
  · exact Or.inr (Or.inr ⟨hland, Or.inl hwots⟩)

end FORS.Security.SignatureWitness


namespace FORS.Security.HiddenBridge

variable [Params]

open Concrete Completeness Graph GraphCorrectness TargetAssignment

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
attribute [local instance] Classical.propDecidable


/-- The structural reference table of a consistent preparation. -/
noncomputable def graphTable (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (seed : MasterSeed) (labels : CanonicalGraphLabels) : TargetAssignment.Table :=
  referenceTable parameter (otsSecrets f parameter seed) (ftsSecrets f parameter seed)
    (PrunedGraph.active parameter) (PrunedGraph.boundary parameter (surrogates f parameter seed)) labels

section Hits

variable (f : QueryImpl HashSpec Id) (parameter : PublicParameter) (seed : MasterSeed)
  (labels : CanonicalGraphLabels)

theorem active_hit (position : Position) (hactive : PrunedGraph.active parameter position)
    (payload : HashInput)
    (hne : tweakableHashInput parameter position.domain payload ≠
      canonicalGraphInput parameter (otsSecrets f parameter seed) (ftsSecrets f parameter seed)
        position labels)
    (hout : truncateHash (f (tweakableHashInput parameter position.domain payload)) =
      truncateHash (labels position)) :
    truncateHash (f (tweakableHashInput parameter position.domain payload)) ∈
      targets parameter (graphTable f parameter seed labels)
        (tweakableHashInput parameter position.domain payload) := by
  unfold graphTable
  rw [targets_at_entry parameter _ position.domain payload _
    (referenceTable_active parameter _ _ _ _ labels position hactive)]
  rw [if_neg (fun h => hne (Option.some.inj h).symm)]
  rw [hout]
  exact Finset.mem_singleton_self _

variable (hconsistent : Consistent f parameter seed labels)

include hconsistent in
theorem leafOutput_hit (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex)
    (hactive : PrunedGraph.KeyActive parameter lay tree leaf) (trace : List HashInput)
    (h : Wots.LeafOutputMatch f parameter lay tree leaf
      (Completeness.otsSecret f parameter lay tree leaf seed) trace) :
    ∃ input ∈ trace, truncateHash (f input) ∈
      targets parameter (graphTable f parameter seed labels) input := by
  obtain ⟨endpoints, hne, hmem, hout⟩ := h
  refine ⟨_, hmem, active_hit f parameter seed labels (.leaf lay tree leaf) hactive _ ?_ ?_⟩
  · rw [leaf_input f parameter seed labels hconsistent lay tree leaf hactive]
    intro heq
    exact hne (tweakableInput_injective heq).2.2
  · change truncateHash (f (tweakableHashInput parameter (.leaf lay tree leaf)
      (leafPayload endpoints))) = _
    rw [hout, leaf_value f parameter seed labels hconsistent lay tree leaf hactive,
      SignatureWitness.canonical_wots_leaf]

include hconsistent in
theorem chainOutput_hit (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex)
    (hactive : PrunedGraph.KeyActive parameter lay tree leaf) (trace : List HashInput)
    (h : Wots.ChainOutputMatch f parameter lay tree leaf
      (Completeness.otsSecret f parameter lay tree leaf seed) trace) :
    ∃ input ∈ trace, truncateHash (f input) ∈
      targets parameter (graphTable f parameter seed labels) input := by
  obtain ⟨index, step, payload, hmem, hne, hout⟩ := h
  refine ⟨_, hmem, active_hit f parameter seed labels (.chain lay tree leaf index step) hactive _ ?_ ?_⟩
  · rw [chain_input f parameter seed labels hconsistent lay tree leaf hactive index step]
    intro heq
    exact hne (bytesLE_injective (tweakableInput_injective heq).2.2)
  · change truncateHash (f (tweakableHashInput parameter (.chain lay tree leaf index step)
      (bytesLE 16 payload))) = _
    rw [hout, chain_value f parameter seed labels hconsistent lay tree leaf hactive index step]
    rfl

theorem active_hit' (position : Position) (hactive : PrunedGraph.active parameter position)
    (input : HashInput) (hdom : ∃ payload, input = tweakableHashInput parameter position.domain payload)
    (hne : input ≠ canonicalGraphInput parameter (otsSecrets f parameter seed) (ftsSecrets f parameter seed)
        position labels)
    (hout : truncateHash (f input) = truncateHash (labels position)) :
    truncateHash (f input) ∈ targets parameter (graphTable f parameter seed labels) input := by
  obtain ⟨payload, rfl⟩ := hdom
  exact active_hit f parameter seed labels position hactive payload hne hout

include hconsistent in
theorem forsException_hit (index : Index) (leaves : FTree → FLeaf) (opening : FTree → TreeOpening)
    (h : Fors.Exception f parameter index seed leaves opening) :
    ∃ input ∈ queriedInputs f (forsRecover parameter index leaves opening : OracleComp HashSpec ForsKey),
      truncateHash (f input) ∈ targets parameter (graphTable f parameter seed labels) input := by
  have hcanon : ∀ κ (leaf : FLeaf), Fors.leafValue f parameter index κ leaf
      (Completeness.forsSecretValue f parameter index κ seed leaf) =
        Completeness.forsLeafValue f parameter index κ seed leaf := fun κ leaf => by
    rw [Fors.leafValue_canonical, Completeness.forsNodeValue_zero]
  rcases h with ⟨κ, hne, heq⟩ | ⟨κ, level, hlevel, -, hneq, hout⟩
  · refine ⟨_, Fors.leafInput_mem f parameter index leaves opening κ,
      active_hit f parameter seed labels (.fleaf index κ (leaves κ)) trivial _ ?_ ?_⟩
    · rw [fleaf_input f parameter seed labels index κ (leaves κ)]
      intro hinput
      exact hne (bytesLE_injective (tweakableInput_injective hinput).2.2)
    · rw [fleaf_value f parameter seed labels hconsistent, ← hcanon, ← heq]
      simp only [Fors.leafValue, forsLeafHash, Completeness.eval_tweakableHash]
      rfl
  · have hfolded := hlevel
    have hlevel : level < forsHeight := by omega
    have hl1 : level + 1 ≤ forsHeight := hlevel
    rw [hcanon] at hneq hout
    refine ⟨_, Fors.nodeInput_mem f parameter index leaves opening κ level hfolded,
      active_hit' f parameter seed labels (forsPosition index κ (level + 1) hl1
        ⟨(leaves κ).val / 2 ^ (level + 1), (Nat.div_le_self _ _).trans_lt (leaves κ).isLt⟩)
        trivial _ ?_ ?_ ?_⟩
    · have hdom : Fors.forsDomain index κ (level + 1) ((leaves κ).val / 2 ^ (level + 1)) =
          HashDomain.forsNode index κ ⟨level, by omega⟩
            ⟨(leaves κ).val / 2 ^ (level + 1), (Nat.div_le_self _ _).trans_lt (leaves κ).isLt⟩ := by
        rw [Fors.forsDomain, dif_pos ⟨by omega, by omega⟩]
        congr 2
        exact Nat.mod_eq_of_lt ((Nat.div_le_self _ _).trans_lt (leaves κ).isLt)
      exact ⟨_, by simp only [merkleInput]; rw [hdom]; rfl⟩
    · rw [fors_path_input f parameter seed labels hconsistent index κ _ level hlevel]
      exact hneq
    · rw [fors_path_value f parameter seed labels hconsistent index κ _ (level + 1) hl1]
      exact hout

include hconsistent in
theorem treeHit_hit (hboundary : BoundaryCorrect f parameter seed labels) (pk : PublicKey)
    (hparameter : pk.parameter = parameter) (message : Message) (signature : Signature) (j : Nat)
    (h : SignatureWitness.TreeHit f pk seed message signature j) :
    ∃ input ∈ SignatureWitness.trace f pk message signature,
      truncateHash (f input) ∈ targets parameter (graphTable f parameter seed labels) input := by
  subst hparameter
  obtain ⟨-, value, -, hrun, hcase⟩ := h
  generalize hlay : layerUp j = lay at hrun hcase
  generalize htree : SignatureWitness.keyTree (SignatureWitness.index f pk message signature) lay = tree
    at hrun hcase
  generalize hleaf : SignatureWitness.keyLeaf (SignatureWitness.index f pk message signature) lay = leaf
    at hrun hcase
  generalize hpath : signaturePath signature lay = path at hrun hcase
  have hmem : ∀ level, level < layerHeight lay →
      merkleInput f pk.parameter (fun height index => .node lay tree height index) leaf.val path
        value level ∈ SignatureWitness.trace f pk message signature := by
    intro level hlevel
    apply hrun
    rw [← merkleFold_treeFold]
    exact merkleInput_mem f pk.parameter _ leaf.val path value (layerHeight lay) level hlevel
  rcases hcase with ⟨reference, hreference, level, hlevel, hparent, hne, hout⟩ |
    ⟨hlaytop, level, hlevel, ⟨hlower, hpositive, hsurrogate⟩, haddress⟩
  · refine ⟨_, hmem level hlevel, ?_⟩
    have hpos := active_hit f pk.parameter seed labels
      (treePosition lay tree (level + 1) (hlevel.trans_le (layerHeight_le lay))
        ⟨reference.val / 2 ^ (level + 1), (Nat.div_le_self _ _).trans_lt reference.isLt⟩)
      (tree_path_active pk.parameter lay tree reference hreference (level + 1) hlevel)
      (orderedPayload (leaf.val.testBit level)
        (merkleValue f pk.parameter (fun height index => .node lay tree height index) leaf.val
          path value level) (path level))
      (by
        rw [tree_path_input f pk.parameter seed labels hconsistent hboundary lay tree reference
          hreference level hlevel]
        intro heq
        apply hne
        unfold merkleInput
        rw [hparent]
        exact heq)
      (by
        rw [tree_path_value f pk.parameter seed labels hconsistent hboundary lay tree reference
          hreference (level + 1) hlevel]
        change truncateHash (f (tweakableHashInput pk.parameter
          (.node lay tree (level + 1) (reference.val / 2 ^ (level + 1))) _)) = _
        rw [← hparent]
        exact hout)
    unfold merkleInput
    rw [hparent]
    exact hpos
  · subst hlaytop
    have htop : tree = rootTree := by
      rw [← htree]; exact Completeness.treeIndexAt_top _
    subst htop
    refine ⟨_, hmem (level - 1) (by omega), ?_⟩
    have hlevel' : level < maxLayerHeight := hlevel.trans_le (layerHeight_le _)
    have hentry := PrunedGraph.referenceTable_surrogate pk.parameter (otsSecrets f pk.parameter seed)
      (ftsSecrets f pk.parameter seed) (surrogates f pk.parameter seed) labels topLayer rootTree
      ⟨level, hlevel'⟩ hpositive rfl rfl hlower
    have hinput : merkleInput f pk.parameter (fun height index => .node topLayer rootTree height index)
        leaf.val path value (level - 1) =
        tweakableHashInput pk.parameter (.node topLayer rootTree level (boundaryIndex pk.parameter level))
          (orderedPayload (leaf.val.testBit (level - 1))
            (merkleValue f pk.parameter (fun height index => .node topLayer rootTree height index)
              leaf.val path value (level - 1)) (path (level - 1))) := by
      simp only [merkleInput, Nat.sub_add_cancel hpositive, haddress]
    rw [hinput]
    unfold graphTable
    rw [targets_at_entry _ _ _ _ _ hentry]
    simp only [reduceCtorEq, ↓reduceIte, Finset.mem_singleton]
    rw [← hinput]
    exact hsurrogate

end Hits

theorem encoding_fields_injective {key key' : OtsKey}
    (h : hashDomainFields (.encoding key.1 key.2.1 key.2.2) =
      hashDomainFields (.encoding key'.1 key'.2.1 key'.2.2)) : key = key' := by
  have hd := hashFields_injective (by trivial) (by trivial) h
  simp only [HashDomain.encoding.injEq] at hd
  obtain ⟨h1, h2, h3⟩ := hd
  obtain ⟨_, _, _⟩ := key
  obtain ⟨_, _, _⟩ := key'
  simp_all

/-- The key of an encoding tweak. -/
noncomputable def encodingAt (fields : TweakFields) : Option OtsKey :=
  if h : ∃ key : OtsKey, fields = hashDomainFields (.encoding key.1 key.2.1 key.2.2) then
    some h.choose else none

theorem encodingAt_encoding (key : OtsKey) :
    encodingAt (hashDomainFields (.encoding key.1 key.2.1 key.2.2)) = some key := by
  have hex : ∃ key' : OtsKey, hashDomainFields (.encoding key.1 key.2.1 key.2.2) =
      hashDomainFields (.encoding key'.1 key'.2.1 key'.2.2) := ⟨key, rfl⟩
  unfold encodingAt
  rw [dif_pos hex]
  exact congrArg some (encoding_fields_injective hex.choose_spec).symm

attribute [local irreducible] encodingAt

/-- The message of every key read from the graph labels: the root label of the tree below, or the
FORS key label at the bottom. For a retained key it is the key's canonical message. -/
def labelMessage (labels : CanonicalGraphLabels) (key : OtsKey) : HashInput :=
  (GraphView.publicData labels fun _ => 0).keyMessage key.1 key.2.1 key.2.2

/-- One encoding target per key, at its label message, exempting its canonical search input. -/
noncomputable def encodingEntry (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (labels : CanonicalGraphLabels) : TargetAssignment.Table := fun fields =>
  (encodingAt fields).map fun key =>
    ⟨ReferenceChoice.exemptInput f parameter key.1 key.2.1 key.2.2 (labelMessage labels key),
      ReferenceChoice.target f parameter key.1 key.2.1 key.2.2 (labelMessage labels key)⟩

/-- Structural targets at graph addresses, encoding targets elsewhere. -/
noncomputable def fullTable (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (seed : MasterSeed) (labels : CanonicalGraphLabels) : TargetAssignment.Table := fun fields =>
  match positionAt fields with
  | some _ => graphTable f parameter seed labels fields
  | none => encodingEntry f parameter labels fields

theorem graph_targets_subset (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (seed : MasterSeed) (labels : CanonicalGraphLabels) (input : HashInput) :
    targets parameter (graphTable f parameter seed labels) input ⊆
      targets parameter (fullTable f parameter seed labels) input := by
  unfold targets
  cases hfields : parseFields parameter input with
  | none => exact Finset.Subset.refl _
  | some fields =>
      dsimp only
      cases hposition : positionAt fields with
      | some position => simp only [fullTable, hposition]; exact Finset.Subset.refl _
      | none =>
          have hnone : graphTable f parameter seed labels fields = none := by
            simp only [graphTable, referenceTable, hposition]
          simp only [hnone]
          exact Finset.empty_subset _

theorem encoding_positionAt (key : OtsKey) :
    positionAt (hashDomainFields (.encoding key.1 key.2.1 key.2.2)) = none := by
  cases h : positionAt (hashDomainFields (.encoding key.1 key.2.1 key.2.2)) with
  | none => rfl
  | some position =>
      have hp := (positionAt_some_iff _ position).mp h
      have hd := hashFields_injective (Position.domain_inRange position) (by trivial) hp
      cases position <;> simp [Position.domain] at hd

attribute [local irreducible] ReferenceChoice.exemptInput ReferenceChoice.target
  ReferenceChoice.selection encodingAttemptLimit

theorem encodingMatch_hit (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (seed : MasterSeed) (labels : CanonicalGraphLabels) (key : OtsKey) (trace : List HashInput)
    (h : ReferenceChoice.EncodingMatch f parameter key.1 key.2.1 key.2.2
      (labelMessage labels key) trace) :
    ∃ input ∈ trace, truncateHash (f input) ∈
      targets parameter (fullTable f parameter seed labels) input := by
  obtain ⟨message, counter, hexempt, hmem, hout⟩ := h
  refine ⟨_, hmem, ?_⟩
  have hentry : fullTable f parameter seed labels (hashDomainFields (.encoding key.1 key.2.1 key.2.2)) =
      some ⟨ReferenceChoice.exemptInput f parameter key.1 key.2.1 key.2.2
          (labelMessage labels key),
        ReferenceChoice.target f parameter key.1 key.2.1 key.2.2 (labelMessage labels key)⟩ := by
    simp only [fullTable, encoding_positionAt, encodingEntry, encodingAt_encoding, Option.map_some]
  have hexempt' : ¬ReferenceChoice.exemptInput f parameter key.1 key.2.1 key.2.2
      (labelMessage labels key) =
        some (tweakableHashInput parameter (.encoding key.1 key.2.1 key.2.2)
          (message ++ bytesLE 4 counter)) := hexempt
  unfold Wots.encodingInput
  rw [targets_at_entry _ _ _ _ _ hentry]
  simp only []
  rw [if_neg hexempt']
  exact Finset.mem_singleton.mpr hout

end FORS.Security.HiddenBridge
