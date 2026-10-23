import Sphincs.BridgeFixedRun
import Sphincs.SecurityReferenceSignature
import Sphincs.SecurityHiddenWitness

set_option backward.isDefEq.respectTransparency false

/-! Accepted-signature classification retaining that every non-tree exception is at a
retained leaf. -/

open OracleComp OracleSpec

namespace Sphincs.Security.SignatureWitness
open Concrete

attribute [local irreducible] messageDigest forestRecover otsLeaf treeFold
  Seeded.forestKey Seeded.treeRoot Seeded.treePath chainWalk encode

variable [Params]

/-- The four exceptions at a retained leaf. -/
def LeafException (f : QueryImpl HashSpec Id) (pk : PublicKey) (seed : MasterSeed)
    (message : Message) (signature : Signature) : Prop :=
  let leaf := index f pk message signature
  let inputs := trace f pk message signature
  ReferenceChoice.EncodingMatch f pk.parameter topLayer rootTree leaf
    (canonicalForest f pk.parameter seed leaf) inputs ∨
  Wots.LeafOutputMatch f pk.parameter topLayer rootTree leaf
    (Completeness.otsSecret f pk.parameter topLayer rootTree leaf seed) inputs ∨
  Wots.ChainException f pk.parameter topLayer rootTree leaf (chosenWord f pk.parameter seed leaf)
    (Completeness.otsSecret f pk.parameter topLayer rootTree leaf seed) inputs ∨
  ForestException f pk seed message signature

/-- At a crossing above the retained subtree, the forged path enters at the boundary node. -/
theorem crossing_boundary (parameter : PublicParameter) (leaf reference : LeafIndex)
    (hreference : Landed parameter reference) (level : Nat) (hlower : subtreeHeight ≤ level)
    (hparent : leaf.val / 2 ^ (level + 1) = reference.val / 2 ^ (level + 1))
    (hbit : leaf.val.testBit level ≠ reference.val.testBit level) :
    leaf.val / 2 ^ level = boundaryIndex parameter level := by
  have hspine : reference.val / 2 ^ level = spineIndex parameter level := by
    have hsum : subtreeHeight + (level - subtreeHeight) = level := Nat.add_sub_of_le hlower
    rw [← hsum, Completeness.landed_div parameter reference hreference]
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

/-- The outside-subtree witness, with the surrogate's exact boundary address. -/
theorem outside_witness_address (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (seed : MasterSeed) (leaf reference : LeafIndex) (path : Nat → Digest) (value : Digest)
    (hb : 0 < subtreeHeight) (hreference : Landed parameter reference)
    (houtside : ¬Landed parameter leaf)
    (hfold : evalWithAnswerFn f (treeFold parameter topLayer rootTree leaf path totalHeight value :
      OracleComp HashSpec Digest) =
      evalWithAnswerFn f (Seeded.treeRoot parameter topLayer rootTree seed : OracleComp HashSpec Digest)) :
    (∃ level, level < totalHeight ∧
      MerkleMatch f parameter (fun height index => .node topLayer rootTree height index)
        leaf.val reference.val path (canonicalTreePath f parameter topLayer rootTree seed reference)
        value (Completeness.node f parameter topLayer rootTree seed 0 reference.val) level) ∨
    ∃ level, level < totalHeight ∧
      SurrogatePreimage f parameter topLayer rootTree seed leaf path value level ∧
      leaf.val / 2 ^ level = boundaryIndex parameter level := by
  have hparent : leaf.val / 2 ^ totalHeight = reference.val / 2 ^ totalHeight := by
    have hl : leaf.val < 2 ^ totalHeight := leaf.isLt
    have hr : reference.val < 2 ^ totalHeight := reference.isLt
    rw [Nat.div_eq_of_lt hl, Nat.div_eq_of_lt hr]
  have hroot := canonicalTreePath_root f parameter topLayer rootTree seed reference hreference
  have hfold' : merkleValue f parameter (fun height index => .node topLayer rootTree height index)
      leaf.val path value totalHeight =
      merkleValue f parameter (fun height index => .node topLayer rootTree height index)
        reference.val (canonicalTreePath f parameter topLayer rootTree seed reference)
        (Completeness.node f parameter topLayer rootTree seed 0 reference.val) totalHeight := by
    rw [hroot, merkleValue, merkleFold_treeFold]
    exact hfold
  rcases merkleFold_classification f parameter (fun height index => .node topLayer rootTree height index)
    leaf.val reference.val path (canonicalTreePath f parameter topLayer rootTree seed reference)
    value (Completeness.node f parameter topLayer rootTree seed 0 reference.val) totalHeight hparent hfold'
    with hgood | ⟨level, hlevel, hparent, hbit, hcross⟩ | hmatch
  · have heq : leaf = reference := Fin.ext hgood.1
    exact False.elim (houtside (heq ▸ hreference))
  · have hlower : subtreeHeight ≤ level := by
      by_contra hnot
      have hle : level + 1 ≤ subtreeHeight := by omega
      have hquot := quotient_eq_above hle hparent
      apply houtside
      exact hquot.trans hreference
    have hpositive : 0 < level := lt_of_lt_of_le hb hlower
    refine Or.inr ⟨level, hlevel, ⟨hlower, hpositive, ?_⟩,
      crossing_boundary parameter leaf reference hreference level hlower hparent hbit⟩
    rw [← merkleValue_succ, Nat.sub_add_cancel (by omega : 1 ≤ level), hcross,
      canonicalTreePath_surrogate f parameter topLayer rootTree seed reference level hlower hlevel]
  · exact Or.inl hmatch

/-- The verifier's tree exception, with the WOTS-recovered value it folds and the boundary
address of a surrogate preimage. -/
def TreeHit (f : QueryImpl HashSpec Id) (pk : PublicKey) (seed : MasterSeed)
    (message : Message) (signature : Signature) : Prop :=
  ∃ value, evalWithAnswerFn f (otsLeaf pk.parameter topLayer rootTree (index f pk message signature)
      (verificationForest f pk message signature) (signature.layers topLayer).counter
      (signature.layers topLayer).chainValues : OracleComp HashSpec (Option Digest)) = some value ∧
    ContainsRun f (trace f pk message signature)
      (treeFold pk.parameter topLayer rootTree (index f pk message signature)
        (signaturePath signature topLayer) totalHeight value) ∧
    ((∃ reference : LeafIndex, Landed pk.parameter reference ∧ ∃ level, level < totalHeight ∧
      MerkleMatch f pk.parameter (fun height index => .node topLayer rootTree height index)
        (index f pk message signature).val reference.val (signaturePath signature topLayer)
        (canonicalTreePath f pk.parameter topLayer rootTree seed reference)
        value (Completeness.node f pk.parameter topLayer rootTree seed 0 reference.val) level) ∨
    ∃ level, level < totalHeight ∧
      SurrogatePreimage f pk.parameter topLayer rootTree seed (index f pk message signature)
        (signaturePath signature topLayer) value level ∧
      (index f pk message signature).val / 2 ^ level = boundaryIndex pk.parameter level)

/-- Canonical opening, a tree hit, or a retained-leaf exception. -/
theorem accepted_full_classification (f : QueryImpl HashSpec Id) (pk : PublicKey)
    (seed : MasterSeed) (message : Message) (signature : Signature) (hb : 0 < subtreeHeight)
    (hroot : pk.root = evalWithAnswerFn f
      (Seeded.treeRoot pk.parameter topLayer rootTree seed : OracleComp HashSpec Digest))
    (hverified : evalWithAnswerFn f
      (Concrete.verify pk message signature : OracleComp HashSpec Bool) = true) :
    (∃ counter, chosenCounter f pk.parameter seed (index f pk message signature) = some counter ∧
      CanonicalOpening f pk seed message signature counter
        (chosenWord f pk.parameter seed (index f pk message signature))) ∨
    TreeHit f pk seed message signature ∨
    (Landed pk.parameter (index f pk message signature) ∧
      LeafException f pk seed message signature) := by
  obtain ⟨value, hleaf, hfold, hrunLeaf, hrunTree⟩ := verified_tree f pk message signature hverified
  have hfold' := hfold.trans hroot
  by_cases hland : Landed pk.parameter (index f pk message signature)
  · rcases inside_subtree_treeFold_witness f pk.parameter topLayer rootTree seed
        (index f pk message signature) (signaturePath signature topLayer) value hland hfold' with
      hopen | hmatch
    · have hcanonical : evalWithAnswerFn f (otsLeaf pk.parameter topLayer rootTree
          (index f pk message signature) (verificationForest f pk message signature)
          (signature.layers topLayer).counter (signature.layers topLayer).chainValues :
          OracleComp HashSpec (Option Digest)) =
        some (Wots.canonicalLeaf f pk.parameter topLayer rootTree (index f pk message signature)
          (Completeness.otsSecret f pk.parameter topLayer rootTree (index f pk message signature) seed)) :=
        hleaf.trans (congrArg some (hopen.1.trans (canonical_wots_leaf f pk.parameter seed _)))
      obtain ⟨candidate, hencode⟩ : ∃ candidate, evalWithAnswerFn f
          (encode pk.parameter topLayer rootTree (index f pk message signature)
            (verificationForest f pk message signature) (signature.layers topLayer).counter :
            OracleComp HashSpec (Option Encoding)) = some candidate := by
        cases henc : evalWithAnswerFn f
            (encode pk.parameter topLayer rootTree (index f pk message signature)
              (verificationForest f pk message signature) (signature.layers topLayer).counter :
              OracleComp HashSpec (Option Encoding)) with
        | none =>
            simp only [otsLeaf, evalWithAnswerFn_bind, henc, evalWithAnswerFn_pure,
              reduceCtorEq] at hcanonical
        | some candidate => exact ⟨candidate, rfl⟩
      rcases ReferenceChoice.otsLeaf_classification f pk.parameter topLayer rootTree
          (index f pk message signature) (canonicalForest f pk.parameter seed (index f pk message signature))
          (Completeness.otsSecret f pk.parameter topLayer rootTree (index f pk message signature) seed)
          (verificationForest f pk message signature) (signature.layers topLayer).counter
          (signature.layers topLayer).chainValues candidate (trace f pk message signature)
          hencode hrunLeaf hcanonical with
        ⟨counter, hselected, hfors, hcounter, hvalues⟩ | hencoding | hleafMatch | hchain
      · rcases Forest.recover_classification f pk.parameter (index f pk message signature) seed
            (digestMarks (verificationDigest f pk message signature)) signature.forest
            hfors with hforsOpening | hforsException
        · refine Or.inl ⟨counter, ?_, hland, hcounter, funext hvalues, ?_, hforsOpening⟩
          · simp only [chosenCounter, hselected, Option.map_some]
          · funext level
            have hp := hopen.2 level.val level.isLt
            simpa only [index, signaturePath, canonicalTreePath, dite_eq_left level.isLt] using hp
        · refine Or.inr (Or.inr ⟨hland, Or.inr (Or.inr (Or.inr ⟨hforsException, ?_⟩))⟩)
          obtain ⟨input, canonicalInput, hinput, hne, hout⟩ :=
            Forest.Exception.queried_output_match f pk.parameter (index f pk message signature) seed
              (digestMarks (verificationDigest f pk message signature)) signature.forest
              hforsException
          exact ⟨input, canonicalInput, verification_forest_run f pk message signature input hinput, hne, hout⟩
      · exact Or.inr (Or.inr ⟨hland, Or.inl hencoding⟩)
      · exact Or.inr (Or.inr ⟨hland, Or.inr (Or.inl hleafMatch)⟩)
      · exact Or.inr (Or.inr ⟨hland, Or.inr (Or.inr (Or.inl hchain))⟩)
    · exact Or.inr (Or.inl ⟨value, hleaf, hrunTree,
        Or.inl ⟨index f pk message signature, hland, hmatch⟩⟩)
  · let reference := keptLeafEquiv pk.parameter ⟨0, Nat.two_pow_pos _⟩
    rcases outside_witness_address f pk.parameter seed (index f pk message signature) reference.val
        (signaturePath signature topLayer) value hb reference.property hland hfold' with
      hmatch | hsurrogate
    · exact Or.inr (Or.inl ⟨value, hleaf, hrunTree, Or.inl ⟨reference.val, reference.property, hmatch⟩⟩)
    · exact Or.inr (Or.inl ⟨value, hleaf, hrunTree, Or.inr hsurrogate⟩)

end Sphincs.Security.SignatureWitness

namespace Sphincs.Security.HiddenBridge

open Concrete Completeness Graph GraphCorrectness TargetAssignment

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
attribute [local instance] Classical.propDecidable

variable [Params]

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
  rw [ite_eq_right (fun h => hne (Option.some.inj h).symm)]
  rw [hout]
  exact Finset.mem_singleton_self _

variable (hconsistent : Consistent f parameter seed labels)

include hconsistent in
theorem leafOutput_hit (leaf : LeafIndex) (hland : Landed parameter leaf) (trace : List HashInput)
    (h : Wots.LeafOutputMatch f parameter topLayer rootTree leaf
      (Completeness.otsSecret f parameter topLayer rootTree leaf seed) trace) :
    ∃ input ∈ trace, truncateHash (f input) ∈
      targets parameter (graphTable f parameter seed labels) input := by
  obtain ⟨endpoints, hne, hmem, hout⟩ := h
  refine ⟨_, hmem, active_hit f parameter seed labels (.leaf topLayer rootTree leaf) hland _ ?_ ?_⟩
  · rw [leaf_input f parameter seed labels hconsistent topLayer rootTree leaf hland]
    intro heq
    exact hne (tweakableInput_injective heq).2.2
  · change truncateHash (f (tweakableHashInput parameter (.leaf topLayer rootTree leaf)
      (leafPayload endpoints))) = _
    rw [hout, leaf_value f parameter seed labels hconsistent topLayer rootTree leaf hland,
      SignatureWitness.canonical_wots_leaf]

include hconsistent in
theorem chainOutput_hit (leaf : LeafIndex) (hland : Landed parameter leaf) (trace : List HashInput)
    (h : Wots.ChainOutputMatch f parameter topLayer rootTree leaf
      (Completeness.otsSecret f parameter topLayer rootTree leaf seed) trace) :
    ∃ input ∈ trace, truncateHash (f input) ∈
      targets parameter (graphTable f parameter seed labels) input := by
  obtain ⟨index, step, payload, hmem, hne, hout⟩ := h
  refine ⟨_, hmem, active_hit f parameter seed labels (.chain topLayer rootTree leaf index step) hland _ ?_ ?_⟩
  · rw [chain_input f parameter seed labels hconsistent topLayer rootTree leaf hland index step]
    intro heq
    exact hne (bytesLE_injective (tweakableInput_injective heq).2.2)
  · change truncateHash (f (tweakableHashInput parameter (.chain topLayer rootTree leaf index step)
      (bytesLE 16 payload))) = _
    rw [hout, chain_value f parameter seed labels hconsistent topLayer rootTree leaf hland index step]
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
theorem fchain_input_consistent (index : Index) (c : Coord) (s : SuperIdx) (j : SubIdx) (a : ChildIdx)
    (i : FChain) (t : FStep) :
    canonicalGraphInput parameter (otsSecrets f parameter seed) (ftsSecrets f parameter seed)
      (.fchain index c s j a i t) labels =
    tweakableHashInput parameter (.fchain index c s j a i t)
      (bytesLE 16 (Forest.honestChain f parameter index c s j a i
        (Completeness.forestSecret f parameter index c s j a i seed) t.val)) := by
  refine fchain_input f parameter seed labels index c s j a i t (fun hpos => ?_)
  rw [fchain_value f parameter seed labels hconsistent]
  congr 1
  simp only
  omega

include hconsistent in
theorem forestException_hit (index : Index) (marks : Coord → CoordMark) (opening : Coord → CoordOpening)
    (h : Forest.Exception f parameter index seed marks opening) :
    ∃ input ∈ queriedInputs f (forestRecover parameter index marks opening : OracleComp HashSpec Digest),
      truncateHash (f input) ∈ targets parameter (graphTable f parameter seed labels) input := by
  rcases h with ⟨c, j, i, offset, hoffset, hlt, hne, heq⟩ | ⟨c, j, hne, heq⟩ |
      ⟨c, j, level, hlevel, -, hneq, hout⟩ | ⟨c, hne, heq⟩ | ⟨c, level, hlevel, -, hneq, hout⟩ | ⟨hne, heq⟩
  · refine ⟨_, Forest.chainInput_mem f parameter index marks opening c j i offset hlt hoffset,
      active_hit f parameter seed labels (.fchain index c (marks c).super j ((marks c).child j) i
        ⟨chainTop - (lut ((marks c).word j) i).val + offset, hoffset⟩) trivial _ ?_ ?_⟩
    · rw [fchain_input_consistent f parameter seed labels hconsistent]
      intro hinput
      exact hne (bytesLE_injective (tweakableInput_injective hinput).2.2)
    · rw [fchain_value f parameter seed labels hconsistent]
      exact heq
  · refine ⟨_, Forest.childLeafInput_mem f parameter index marks opening c j,
      active_hit f parameter seed labels (.childLeaf index c (marks c).super j ((marks c).child j)) trivial _ ?_ ?_⟩
    · rw [childLeaf_input f parameter seed labels hconsistent]
      intro hinput
      exact hne (childPayload_injective (tweakableInput_injective hinput).2.2)
    · rw [childLeaf_value f parameter seed labels hconsistent]
      exact heq
  · have hfolded := hlevel
    have hlevel : level < subHeight := Nat.lt_of_lt_of_le hfolded (by decide)
    have hl1 : level + 1 ≤ subHeight := hlevel
    refine ⟨_, Forest.subNodeInput_mem f parameter index marks opening c j level hfolded,
      active_hit' f parameter seed labels (subPosition index c (marks c).super j (level + 1) hl1
        ⟨((marks c).child j).val / 2 ^ (level + 1), (Nat.div_le_self _ _).trans_lt ((marks c).child j).isLt⟩)
        trivial _ ?_ ?_ ?_⟩
    · have hdom : Forest.subDomain index c (marks c).super j (level + 1) (((marks c).child j).val / 2 ^ (level + 1)) =
          HashDomain.subNode index c (marks c).super j ⟨level, by omega⟩
            ⟨((marks c).child j).val / 2 ^ (level + 1), (Nat.div_le_self _ _).trans_lt ((marks c).child j).isLt⟩ := by
        rw [Forest.subDomain, dite_eq_left ⟨by omega, by omega⟩]
        congr 2
        exact Nat.mod_eq_of_lt ((Nat.div_le_self _ _).trans_lt ((marks c).child j).isLt)
      exact ⟨_, by simp only [merkleInput]; rw [hdom]; rfl⟩
    · rw [sub_path_input f parameter seed labels hconsistent index c _ j _ level hlevel]
      exact hneq
    · rw [sub_path_value f parameter seed labels hconsistent index c _ j _ (level + 1) hl1]
      exact hout
  · refine ⟨_, Forest.superInput_mem f parameter index marks opening c,
      active_hit f parameter seed labels (.superChild index c (marks c).super) trivial _ ?_ ?_⟩
    · rw [super_input f parameter seed labels hconsistent]
      intro hinput
      exact hne (tweakableInput_injective hinput).2.2
    · rw [super_value f parameter seed labels hconsistent]
      exact heq
  · have hfolded := hlevel
    have hlevel : level < topHeight := Nat.lt_of_lt_of_le hfolded (by decide)
    have hl1 : level + 1 ≤ topHeight := hlevel
    refine ⟨_, Forest.topNodeInput_mem f parameter index marks opening c level hfolded,
      active_hit' f parameter seed labels (topPosition index c (level + 1) hl1
        ⟨(marks c).super.val / 2 ^ (level + 1), (Nat.div_le_self _ _).trans_lt (marks c).super.isLt⟩)
        trivial _ ?_ ?_ ?_⟩
    · have hdom : Forest.topDomain index c (level + 1) ((marks c).super.val / 2 ^ (level + 1)) =
          HashDomain.topNode index c ⟨level, by omega⟩
            ⟨(marks c).super.val / 2 ^ (level + 1), (Nat.div_le_self _ _).trans_lt (marks c).super.isLt⟩ := by
        rw [Forest.topDomain, dite_eq_left ⟨by omega, by omega⟩]
        congr 2
        exact Nat.mod_eq_of_lt ((Nat.div_le_self _ _).trans_lt (marks c).super.isLt)
      exact ⟨_, by simp only [merkleInput]; rw [hdom]; rfl⟩
    · rw [top_path_input f parameter seed labels hconsistent index c _ level hlevel]
      exact hneq
    · rw [top_path_value f parameter seed labels hconsistent index c _ (level + 1) hl1]
      exact hout
  · refine ⟨_, Forest.rootsInput_mem f parameter index marks opening,
      active_hit f parameter seed labels (.roots index) trivial _ ?_ ?_⟩
    · rw [roots_input f parameter seed labels hconsistent index]
      intro hinput
      exact hne (tweakableInput_injective hinput).2.2
    · rw [forest_key_value f parameter seed labels hconsistent index]
      exact heq

include hconsistent in
theorem treeHit_hit (hboundary : BoundaryCorrect f parameter seed labels) (pk : PublicKey)
    (hparameter : pk.parameter = parameter) (message : Message) (signature : Signature)
    (h : SignatureWitness.TreeHit f pk seed message signature) :
    ∃ input ∈ SignatureWitness.trace f pk message signature,
      truncateHash (f input) ∈ targets parameter (graphTable f parameter seed labels) input := by
  subst hparameter
  obtain ⟨value, -, hrun, hcase⟩ := h
  generalize hleaf : SignatureWitness.index f pk message signature = leaf at hrun hcase
  generalize hpath : signaturePath signature topLayer = path at hrun hcase
  have hmem : ∀ level, level < totalHeight →
      merkleInput f pk.parameter (fun height index => .node topLayer rootTree height index) leaf.val path
        value level ∈ SignatureWitness.trace f pk message signature := by
    intro level hlevel
    apply hrun
    rw [← merkleFold_treeFold]
    exact merkleInput_mem f pk.parameter _ leaf.val path value totalHeight level hlevel
  rcases hcase with ⟨reference, hreference, level, hlevel, hparent, hne, hout⟩ |
    ⟨level, hlevel, ⟨hlower, hpositive, hsurrogate⟩, haddress⟩
  · refine ⟨_, hmem level hlevel, ?_⟩
    have hpos := active_hit f pk.parameter seed labels
      (treePosition topLayer rootTree (level + 1) hlevel
        ⟨reference.val / 2 ^ (level + 1), (Nat.div_le_self _ _).trans_lt reference.isLt⟩)
      (tree_path_active pk.parameter topLayer rootTree reference hreference (level + 1) hlevel)
      (orderedPayload (leaf.val.testBit level)
        (merkleValue f pk.parameter (fun height index => .node topLayer rootTree height index) leaf.val
          path value level) (path level))
      (by
        rw [tree_path_input f pk.parameter seed labels hconsistent hboundary topLayer rootTree reference
          hreference level hlevel]
        intro heq
        apply hne
        unfold merkleInput
        rw [hparent]
        exact heq)
      (by
        rw [tree_path_value f pk.parameter seed labels hconsistent hboundary topLayer rootTree reference
          hreference (level + 1) hlevel]
        change truncateHash (f (tweakableHashInput pk.parameter
          (.node topLayer rootTree (level + 1) (reference.val / 2 ^ (level + 1))) _)) = _
        rw [← hparent]
        exact hout)
    unfold merkleInput
    rw [hparent]
    exact hpos
  · refine ⟨_, hmem (level - 1) (by omega), ?_⟩
    have hentry := PrunedGraph.referenceTable_surrogate pk.parameter (otsSecrets f pk.parameter seed)
      (ftsSecrets f pk.parameter seed) (surrogates f pk.parameter seed) labels topLayer rootTree
      ⟨level, hlevel⟩ hpositive hlower
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

omit [Params] in
theorem encoding_fields_injective {leaf leaf' : Index}
    (h : hashDomainFields (.encoding topLayer rootTree leaf) =
      hashDomainFields (.encoding topLayer rootTree leaf')) : leaf = leaf' := by
  have hd := hashFields_injective (by trivial) (by trivial) h
  simp only [HashDomain.encoding.injEq] at hd
  exact hd.2.2

/-- The root-tree leaf of an encoding tweak. -/
noncomputable def encodingAt (fields : TweakFields) : Option Index :=
  if h : ∃ leaf : Index, fields = hashDomainFields (.encoding topLayer rootTree leaf) then
    some h.choose else none

omit [Params] in
theorem encodingAt_encoding (leaf : Index) :
    encodingAt (hashDomainFields (.encoding topLayer rootTree leaf)) = some leaf := by
  have hex : ∃ leaf' : Index, hashDomainFields (.encoding topLayer rootTree leaf) =
      hashDomainFields (.encoding topLayer rootTree leaf') := ⟨leaf, rfl⟩
  unfold encodingAt
  rw [dite_eq_left hex]
  exact congrArg some (encoding_fields_injective hex.choose_spec).symm

attribute [local irreducible] encodingAt

/-- One encoding target per leaf of the root tree, exempting its canonical search input. -/
noncomputable def encodingEntry (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (seed : MasterSeed) : TargetAssignment.Table := fun fields =>
  (encodingAt fields).map fun leaf =>
    ⟨ReferenceChoice.exemptInput f parameter topLayer rootTree leaf
        (SignatureWitness.canonicalForest f parameter seed leaf),
      ReferenceChoice.target f parameter topLayer rootTree leaf
        (SignatureWitness.canonicalForest f parameter seed leaf)⟩

/-- Structural targets at graph addresses, encoding targets elsewhere. -/
noncomputable def fullTable (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (seed : MasterSeed) (labels : CanonicalGraphLabels) : TargetAssignment.Table := fun fields =>
  match positionAt fields with
  | some _ => graphTable f parameter seed labels fields
  | none => encodingEntry f parameter seed fields

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

omit [Params] in
theorem encoding_positionAt (leaf : Index) :
    positionAt (hashDomainFields (.encoding topLayer rootTree leaf)) = none := by
  cases h : positionAt (hashDomainFields (.encoding topLayer rootTree leaf)) with
  | none => rfl
  | some position =>
      have hp := (positionAt_some_iff _ position).mp h
      have hd := hashFields_injective (Position.domain_inRange position) (by trivial) hp
      cases position <;> simp [Position.domain] at hd

attribute [local irreducible] ReferenceChoice.exemptInput ReferenceChoice.target
  ReferenceChoice.selection encodingAttemptLimit

theorem encodingMatch_hit (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (seed : MasterSeed) (labels : CanonicalGraphLabels) (leaf : Index) (trace : List HashInput)
    (h : ReferenceChoice.EncodingMatch f parameter topLayer rootTree leaf
      (SignatureWitness.canonicalForest f parameter seed leaf) trace) :
    ∃ input ∈ trace, truncateHash (f input) ∈
      targets parameter (fullTable f parameter seed labels) input := by
  obtain ⟨message, counter, hexempt, hmem, hout⟩ := h
  refine ⟨_, hmem, ?_⟩
  have hentry : fullTable f parameter seed labels (hashDomainFields (.encoding topLayer rootTree leaf)) =
      some ⟨ReferenceChoice.exemptInput f parameter topLayer rootTree leaf
          (SignatureWitness.canonicalForest f parameter seed leaf),
        ReferenceChoice.target f parameter topLayer rootTree leaf
          (SignatureWitness.canonicalForest f parameter seed leaf)⟩ := by
    simp only [fullTable, encoding_positionAt, encodingEntry, encodingAt_encoding, Option.map_some]
  have hexempt' : ¬ReferenceChoice.exemptInput f parameter topLayer rootTree leaf
      (SignatureWitness.canonicalForest f parameter seed leaf) =
        some (tweakableHashInput parameter (.encoding topLayer rootTree leaf)
          (bytesLE 16 message ++ bytesLE 4 counter)) := hexempt
  unfold Wots.encodingInput
  rw [targets_at_entry _ _ _ _ _ hentry]
  simp only []
  rw [ite_eq_right hexempt']
  exact Finset.mem_singleton.mpr hout

end Sphincs.Security.HiddenBridge
