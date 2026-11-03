import FORS.GraphView.Signer
import FORS.GraphView.Secrets
import FORS.GraphView.HashCalls
import FORS.LazyRun.Cost

section

/-! The source oracle of the graph-reveal signer on a fixed answer function and coordinate
table: private draws are uniform, and hash and reveal queries are answered by the fixed view. -/

open OracleComp OracleSpec

namespace FORS.Security.GraphView

variable [Params]
open Concrete Completeness Prefix HiddenGraph
attribute [local instance] Classical.propDecidable
attribute [local irreducible] finishSource Seeded.finishSign digestAttemptLimit
set_option backward.isDefEq.respectTransparency false

noncomputable def fixedSource (f : QueryImpl HashSpec Id) (table : HiddenGraph.Table) :
    QueryImpl HiddenGraph.SourceSpec PMF :=
  (fun input => PMF.uniformOfFintype (unifSpec.Range input) : QueryImpl unifSpec PMF) +
    (fixedView f table).liftTarget PMF

end FORS.Security.GraphView

end

section

/-! Exact original honest hash costs for the graph-reveal signer. The simulation retains
ordinary message/encoding queries and represents the remaining internal work by explicit
natural-number ticks, including work performed before a failed WOTS search. -/

open OracleComp OracleSpec

namespace FORS.Security.GraphView

variable [Params]
open Concrete Completeness Prefix PrunedGraph
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] firstEncoding ReferenceChoice.search encodingAttemptLimit
  Seeded.forsKey Seeded.forsOpen Seeded.treePath Seeded.otsSignFrom Seeded.signLayer
  chainWalk sequenceFin encode Seeded.treeRoot Seeded.forsNode

/-- The cost of the FORS key: the two top nodes of every tree. -/
def forsKeyCost : Nat := forsTrees * (2 * (5 * 2 ^ (forsHeight - 2) - 1))

/-- The cost of opening one tree: the derivation of the opened pair and the sibling leaf, then the
path nodes above level 0. -/
def treeOpenCost : Nat :=
  2 + ∑ level : Fin forsHeight, if level.val = 0 then 0 else 5 * 2 ^ (level.val - 1) - 1

theorem hashCalls_forsKey_exact (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (index : Index) (seed : MasterSeed) :
    hashCalls f (Seeded.forsKey parameter index seed : OracleComp HashSpec ForsKey) = forsKeyCost :=
  hashCalls_forsKey f parameter index seed

theorem hashCalls_treeOpen_exact (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (index : Index) (κ : FTree) (leaf : FLeaf) (seed : MasterSeed) :
    hashCalls f (Seeded.treeOpen parameter index κ leaf seed : OracleComp HashSpec TreeOpening) =
      treeOpenCost := by
  rw [Seeded.treeOpen, hashCalls_bind, hashCalls_deriveOutput, hashCalls_bind, forsLeafHash,
    hashCalls_tweakableHash, hashCalls_bind, hashCalls_sequenceFin, hashCalls_pure, Nat.add_zero,
    ← Nat.add_assoc, treeOpenCost]
  congr 1
  refine Finset.sum_congr rfl fun level _ => ?_
  by_cases h0 : level.val = 0
  · rw [if_pos h0, if_pos h0, hashCalls_pure]
  · rw [if_neg h0, if_neg h0]
    obtain ⟨level', hl⟩ : ∃ level', level.val = level' + 1 := ⟨level.val - 1, by omega⟩
    rw [hl, hashCalls_forsNode f parameter index κ seed _ _ (by have := level.isLt; omega),
      Nat.add_sub_cancel]

/-- Opening FORS costs `k` tree openings. -/
theorem hashCalls_forsOpen_exact (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (index : Index) (leaves : FTree → FLeaf) (seed : MasterSeed) :
    hashCalls f (Seeded.forsOpen parameter index leaves seed :
      OracleComp HashSpec (FTree → TreeOpening)) = forsTrees * treeOpenCost := by
  simp only [Seeded.forsOpen, hashCalls_sequenceFin, hashCalls_treeOpen_exact, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, smul_eq_mul]

/-- The published values of a WOTS+C signature cost `32 + 128 = 160` calls: the 32 seed derivations
of the chain starts and the 128 chain steps of a codeword. -/
theorem hashCalls_published_values (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex) (seed : MasterSeed) (word : Encoding)
    (hword : TargetSum.Valid word) :
    hashCalls f (do
      let secrets ← (Seeded.otsSecrets parameter lay tree leaf seed : OracleComp HashSpec (ChainIndex → Digest))
      sequenceFin fun chain => chainWalk parameter lay tree leaf chain 0 (word chain).val (secrets chain)) = 160 := by
  simp only [hashCalls_sequenceFin, hashCalls_bind, hashCalls_otsSecrets]
  have hwalk (chain : ChainIndex) (value : Digest) :
      hashCalls f (chainWalk parameter lay tree leaf chain 0 (word chain).val value :
        OracleComp HashSpec Digest) = (word chain).val :=
    hashCalls_chainWalk f parameter lay tree leaf chain 0 (word chain).val value
      (by have := (word chain).isLt; omega)
  simp only [hwalk]
  change 32 + TargetSum.sum word = 160
  rw [show TargetSum.sum word = targetSum from hword]
  rfl

/-- A layer signs exactly when its counter search succeeds. -/
theorem eval_signLayer_isSome (f : QueryImpl HashSpec Id) (sk : Seeded.SecretKey) (index : Index)
    (lay : Layer) :
    (evalWithAnswerFn f (Seeded.signLayer sk index lay :
      OracleComp HashSpec (Option (LayerSignature lay)))).isSome =
    (firstEncoding f sk.parameter lay (treeIndexAt index lay) (leafIndexAt index lay)
      (Completeness.layerMessageValue f sk index lay) encodingAttemptLimit 0).isSome := by
  simp only [Seeded.signLayer, evalWithAnswerFn_bind, Seeded.otsSign, otsSignFrom_eq_firstEncoding,
    Completeness.layerMessageValue]
  cases firstEncoding f sk.parameter lay (treeIndexAt index lay) (leafIndexAt index lay)
      (evalWithAnswerFn f (Seeded.layerMessage sk index lay : OracleComp HashSpec HashInput))
      encodingAttemptLimit 0 <;>
    simp only [Option.map_none, Option.map_some, evalWithAnswerFn_pure, evalWithAnswerFn_bind,
      Option.isSome_none, Option.isSome_some]

theorem hashCalls_otsSignFrom_search (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex) (seed : MasterSeed) (message : HashInput)
    (attempts start : Nat) :
    hashCalls f (Seeded.otsSignFrom parameter lay tree leaf seed message attempts start :
      OracleComp HashSpec (Option (Counter × (ChainIndex → Digest)))) =
      hashCalls f (ReferenceChoice.search parameter lay tree leaf message attempts start) +
        if (firstEncoding f parameter lay tree leaf message attempts start).isSome then 160 else 0 := by
  induction attempts generalizing start with
  | zero => simp only [Seeded.otsSignFrom, ReferenceChoice.search, firstEncoding, hashCalls_pure,
      Option.isSome_none, Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
  | succ attempts ih =>
      cases he : evalWithAnswerFn f (encode parameter lay tree leaf message
          (BitVec.ofNat counterBits start) : OracleComp HashSpec (Option Encoding)) with
      | none =>
          simp only [Seeded.otsSignFrom, ReferenceChoice.search, firstEncoding,
            hashCalls_bind, hashCalls_encode, he, ih]
          omega
      | some word =>
          have hvalid := EncodingCode.decode_valid (Wots.decode_of_encode f parameter lay tree leaf
            message (BitVec.ofNat counterBits start) word he)
          have hpub := hashCalls_published_values f parameter lay tree leaf seed word hvalid
          rw [hashCalls_bind] at hpub
          simp only [Seeded.otsSignFrom, ReferenceChoice.search, firstEncoding,
            hashCalls_bind, hashCalls_encode, he, hashCalls_pure, hpub,
            Option.isSome_some, ↓reduceIte, Nat.add_zero]


/-- The cost of the authentication path of a layer: kept nodes below `keptHeight`, one derivation
per surrogate above. -/
def treePathCost (lay : Layer) : Nat :=
  ∑ level : Fin (layerHeight lay), if level.val < keptHeight lay then 226 * 2 ^ level.val - 1 else 1

theorem hashCalls_treePath_exact (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex) (seed : MasterSeed) :
    hashCalls f (Seeded.treePath parameter lay tree seed leaf :
      OracleComp HashSpec (Fin (layerHeight lay) → Digest)) = treePathCost lay := by
  simp only [Seeded.treePath, hashCalls_sequenceFin, treePathCost]
  apply Finset.sum_congr rfl
  intro level _
  split
  · exact hashCalls_treeNode f parameter lay tree seed _ _
  · have hlevel : level.val < maxLayerHeight := level.isLt.trans_le (layerHeight_le lay)
    simp only [Seeded.surrogate, dif_pos hlevel, hashCalls_deriveKey]

/-- The cost of a key's message: the root of a whole tree of height 6 below it, or the FORS key
of its instance at the bottom layer. -/
def keyMessageCost (lay : Layer) : Nat :=
  if lay.val + 1 < numLayers then 226 * 2 ^ lowerHeight - 1 else forsKeyCost

set_option maxRecDepth 100000 in
theorem hashCalls_keyMessage (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (seed : MasterSeed) (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex) :
    hashCalls f (Seeded.keyMessage parameter seed lay tree leaf : OracleComp HashSpec HashInput) =
      keyMessageCost lay := by
  unfold Seeded.keyMessage keyMessageCost
  by_cases hbelow : lay.val + 1 < numLayers
  · have hne : (⟨lay.val + 1, hbelow⟩ : Layer).val ≠ 0 := Nat.succ_ne_zero _
    rw [dif_pos hbelow, if_pos hbelow, hashCalls_bind, hashCalls_treeRoot,
      keptHeight_of_ne_top _ hne, layerHeight_of_ne_top _ hne, Nat.sub_self]
    simp only [hashCalls_pure, Nat.mul_zero, Nat.add_zero]
  · rw [dif_neg hbelow, if_neg hbelow, hashCalls_bind, hashCalls_forsKey_exact, hashCalls_pure, Nat.add_zero]

/-- The cost of one layer: its key's message, the counter search, and on success the chain values
and the path. -/
theorem hashCalls_signLayer_exact (f : QueryImpl HashSpec Id) (sk : Seeded.SecretKey)
    (index : Index) (lay : Layer) :
    hashCalls f (Seeded.signLayer sk index lay : OracleComp HashSpec (Option (LayerSignature lay))) =
      keyMessageCost lay + hashCalls f (ReferenceChoice.search sk.parameter lay (treeIndexAt index lay)
        (leafIndexAt index lay) (Completeness.layerMessageValue f sk index lay) encodingAttemptLimit 0) +
      if (firstEncoding f sk.parameter lay (treeIndexAt index lay) (leafIndexAt index lay)
        (Completeness.layerMessageValue f sk index lay) encodingAttemptLimit 0).isSome then
          160 + treePathCost lay else 0 := by
  unfold Completeness.layerMessageValue
  rw [Seeded.signLayer, hashCalls_bind, Seeded.layerMessage, hashCalls_keyMessage]
  simp only [Seeded.otsSign, hashCalls_bind, hashCalls_otsSignFrom_search,
    otsSignFrom_eq_firstEncoding]
  generalize evalWithAnswerFn f (Seeded.keyMessage sk.parameter sk.seed lay (treeIndexAt index lay)
    (leafIndexAt index lay) : OracleComp HashSpec HashInput) = message
  cases hs : firstEncoding f sk.parameter lay (treeIndexAt index lay) (leafIndexAt index lay)
      message encodingAttemptLimit 0 <;>
    simp only [Option.map_none, Option.map_some, Option.isSome_none, Option.isSome_some,
      Bool.false_eq_true, ↓reduceIte, hashCalls_pure, hashCalls_bind, hashCalls_treePath_exact,
      Nat.add_zero]
  omega

/-- The cost of the layer `lay` of a signature, from the public data. -/
noncomputable def layerHashCost (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (data : PublicData) (index : Index) (lay : Layer) : Nat :=
  keyMessageCost lay + hashCalls f (layerSearch parameter data index lay) +
    if (firstEncoding f parameter lay (treeIndexAt index lay) (leafIndexAt index lay)
      (data.keyMessage lay (treeIndexAt index lay) (leafIndexAt index lay)) encodingAttemptLimit 0).isSome
    then 160 + treePathCost lay else 0

/-- Whether the counter search of the layer `lay` of a signature succeeds. -/
noncomputable def layerFound (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (data : PublicData) (index : Index) (lay : Layer) : Bool :=
  (firstEncoding f parameter lay (treeIndexAt index lay) (leafIndexAt index lay)
    (data.keyMessage lay (treeIndexAt index lay) (leafIndexAt index lay)) encodingAttemptLimit 0).isSome

noncomputable def finishHashCost (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (data : PublicData) (message : Message) (randomness : Randomness) : Nat :=
  let index := digestIndex (evalWithAnswerFn f
    (messageDigest parameter data.root message randomness : OracleComp HashSpec MessageDigest))
  digestCalls + forsTrees * treeOpenCost +
    seqCost (layerFound f parameter data index) (layerHashCost f parameter data index)

/-- The digest calls and the FORS opening (secrets and all authentication nodes) come first; the
layers follow, each with its key's message, the counter search, and on success the chain values and
the path, until the first failed search. -/
theorem hashCalls_finishSign_exact (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (seed : MasterSeed) (data : PublicData) (hdata : DataCorrect f parameter seed data)
    (message : Message) (randomness : Randomness)
    (hland : Landed parameter (digestIndex (evalWithAnswerFn f
      (messageDigest parameter data.root message randomness : OracleComp HashSpec MessageDigest)))) :
    hashCalls f (Seeded.finishSign ⟨seed, parameter, data.root⟩ message randomness) =
      finishHashCost f parameter data message randomness := by
  simp only [Seeded.finishSign, hashCalls_bind, hashCalls_messageDigest, hashCalls_forsOpen_exact,
    finishHashCost]
  generalize digestIndex (evalWithAnswerFn f (messageDigest parameter data.root message randomness :
    OracleComp HashSpec MessageDigest)) = index at hland ⊢
  have hmsg : ∀ lay : Layer, Completeness.layerMessageValue f ⟨seed, parameter, data.root⟩ index lay =
      data.keyMessage lay (treeIndexAt index lay) (leafIndexAt index lay) := fun lay =>
    (hdata.keyMessage lay _ _ ⟨index, hland, rfl, rfl⟩).symm
  have hlayers : hashCalls f (sequenceLayers fun lay => Seeded.signLayer ⟨seed, parameter, data.root⟩ index lay) =
      seqCost (layerFound f parameter data index) (layerHashCost f parameter data index) := by
    rw [hashCalls_sequenceLayers]
    congr 1
    · funext lay
      rw [eval_signLayer_isSome]
      simp only [layerFound, ← hmsg lay]
    · funext lay
      rw [hashCalls_signLayer_exact, hmsg lay]
      rfl
  rw [← hlayers]
  cases evalWithAnswerFn f (sequenceLayers fun lay => Seeded.signLayer ⟨seed, parameter, data.root⟩
      index lay) <;> simp only [hashCalls_pure] <;> omega

end FORS.Security.GraphView

end
