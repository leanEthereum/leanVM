import Sphincs.SecurityEncodingPreparation
import Sphincs.SecurityHiddenGraphRows
import Sphincs.SecurityGraphCorrectness

/-! Signature assembly from public structural labels and explicit coordinate disclosures.
This file establishes the exact output view; preservation of the original internal hash cost
is a separate obligation when composing the complete monitored game.

The forest opening reveals, for every tree, subtree and chain of the selected WOTS keys, the chain
values at and above the opened position `4 - d_i` (everything the signature lets anyone compute);
the subtree and tree paths are public structural labels. -/

open OracleComp OracleSpec

namespace Sphincs.Security.GraphView
open Concrete Completeness Graph GraphCorrectness HiddenGraph Prefix

attribute [local irreducible] firstEncoding encodingAttemptLimit Seeded.forestKey Seeded.forestOpen
  Seeded.treePath Seeded.signLayer chainWalk forestWalk sequenceFin encode
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

structure PublicData where
  root : Digest
  forestKey : Index → Digest
  treePath : LeafIndex → Fin (layerHeight topLayer) → Digest
  subPath : Index → Coord → SuperIdx → SubIdx → ChildIdx → Fin subHeight → Digest
  topPath : Index → Coord → SuperIdx → Fin topHeight → Digest

def publicData (labels : CanonicalGraphLabels) : PublicData where
  root := truncateHash (labels (treePosition topLayer rootTree totalHeight le_rfl ⟨0, by decide⟩))
  forestKey := fun index => truncateHash (labels (.roots index))
  treePath := fun leaf level => truncateHash (labels
    (treePosition topLayer rootTree level.val (Nat.le_of_lt level.isLt)
      ⟨Nat.xor (leaf.val / 2 ^ level.val) 1,
        Nat.xor_lt_two_pow ((Nat.div_le_self _ _).trans_lt leaf.isLt) one_lt_leaf_capacity⟩))
  subPath := fun index c s j a level => truncateHash (labels
    (subPosition index c s j level.val (Nat.le_of_lt level.isLt)
      ⟨Nat.xor (a.val / 2 ^ level.val) 1,
        Nat.xor_lt_two_pow ((Nat.div_le_self _ _).trans_lt a.isLt) (by decide)⟩))
  topPath := fun index c s level => truncateHash (labels
    (topPosition index c level.val (Nat.le_of_lt level.isLt)
      ⟨Nat.xor (s.val / 2 ^ level.val) 1,
        Nat.xor_lt_two_pow ((Nat.div_le_self _ _).trans_lt s.isLt) (by decide)⟩))

variable [Params]

structure DataCorrect (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (seed : MasterSeed) (data : PublicData) : Prop where
  root : data.root = evalWithAnswerFn f
    (Seeded.treeRoot parameter topLayer rootTree seed : OracleComp HashSpec Digest)
  forestKey : ∀ index, data.forestKey index = evalWithAnswerFn f
    (Seeded.forestKey parameter index seed : OracleComp HashSpec Digest)
  treePath : ∀ leaf, Landed parameter leaf → data.treePath leaf = evalWithAnswerFn f
    (Seeded.treePath parameter topLayer rootTree seed leaf :
      OracleComp HashSpec (Fin (layerHeight topLayer) → Digest))
  subPath : ∀ index c s j a, data.subPath index c s j a = Forest.canonicalSubPath f parameter index seed c s j a
  topPath : ∀ index c s, data.topPath index c s = Forest.canonicalTopPath f parameter index seed c s

theorem publicData_correct (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (seed : MasterSeed) (labels : CanonicalGraphLabels)
    (hconsistent : Consistent f parameter seed labels)
    (hboundary : BoundaryCorrect f parameter seed labels) :
    DataCorrect f parameter seed (publicData labels) := by
  constructor
  · exact tree_root_value f parameter seed labels hconsistent hboundary topLayer rootTree
  · exact forest_key_value f parameter seed labels hconsistent
  · intro leaf hland
    funext level
    simpa only [publicData, canonicalTreePath, dif_pos level.isLt] using
      tree_path_sibling f parameter seed labels hconsistent hboundary topLayer rootTree
        leaf hland level.val level.isLt
  · intro index c s j a
    funext level
    have h := sub_path_sibling f parameter seed labels hconsistent index c s j a level.val level.isLt
    simpa only [publicData, Forest.subPathExt, dif_pos level.isLt] using h
  · intro index c s
    funext level
    have h := top_path_sibling f parameter seed labels hconsistent index c s level.val level.isLt
    simpa only [publicData, Forest.topPathExt, dif_pos level.isLt] using h

def CoordinatesCorrect (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (seed : MasterSeed) (table : HiddenGraph.Table) : Prop :=
  (∀ leaf, Landed parameter leaf → ∀ chain position,
    table (.chain topLayer rootTree leaf chain position) =
      Chain.honestChain f parameter topLayer rootTree leaf chain
        (Completeness.otsSecret f parameter topLayer rootTree leaf seed chain) position.val) ∧
  (∀ index c s j a i (position : FPos), table (.fchain index c s j a i position) =
    Completeness.chainValueOf f parameter index c s j a i seed position.val)

theorem coordinates_correct (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (seed : MasterSeed) (labels : CanonicalGraphLabels)
    (hconsistent : Consistent f parameter seed labels) :
    CoordinatesCorrect f parameter seed
      (coordinates (otsSecrets f parameter seed) (ftsSecrets f parameter seed) labels) := by
  constructor
  · intro leaf hland chain position
    by_cases hz : position.val = 0
    · simp only [coordinates, hz, ↓reduceDIte, Chain.honestChain, chainWalk]
      rfl
    · rw [coordinates, dif_neg hz]
      have hstep : position.val - 1 < chainLength - 1 := by have := position.isLt; omega
      have h := chain_value f parameter seed labels hconsistent topLayer rootTree leaf hland
        chain ⟨position.val - 1, hstep⟩
      simpa only [Nat.sub_add_cancel (by omega : 1 ≤ position.val), otsSecrets] using h
  · intro index c s j a i position
    by_cases hz : position.val = 0
    · simp only [coordinates, hz, ↓reduceDIte, Completeness.chainValueOf, Completeness.fwalk, forestWalk]
      rfl
    · rw [coordinates, dif_neg hz]
      have hstep : position.val - 1 < chainTop := by have := position.isLt; omega
      have h := fchain_value f parameter seed labels hconsistent index c s j a i ⟨position.val - 1, hstep⟩
      rw [Nat.sub_add_cancel (by omega : 1 ≤ position.val)] at h
      exact h

abbrev HashViewSpec := HashSpec + (Coordinate →ₒ Digest)

def reveal (coordinate : Coordinate) : OracleComp HashViewSpec Digest :=
  liftM ((Coordinate →ₒ Digest).query coordinate)

def fixedView (f : QueryImpl HashSpec Id) (table : HiddenGraph.Table) : QueryImpl HashViewSpec Id :=
  f + (show QueryImpl (Coordinate →ₒ Digest) Id from table)

/-- The opened position of chain `i` of sub-tree `j`. -/
def openedPos (mark : CoordMark) (j : SubIdx) (i : FChain) : FPos :=
  ⟨chainTop - (lut (mark.word j) i).val, by simp only [chainTop]; omega⟩

/-- Reveal the chain values of one opened chain at and above its opened position. -/
def revealChain (index : Index) (c : Coord) (mark : CoordMark) (j : SubIdx) (i : FChain) :
    OracleComp HashViewSpec (FPos → Digest) :=
  sequenceFin fun k : FPos =>
    if (openedPos mark j i).val ≤ k.val then
      reveal (.fchain index c mark.super j (mark.child j) i k)
    else pure 0

/-- One tree's opening from the revealed chain values and the public paths. -/
def coordSource (data : PublicData) (index : Index) (c : Coord) (mark : CoordMark) :
    OracleComp HashViewSpec CoordOpening := do
  let sub ← sequenceFin fun j => do
    let cols ← sequenceFin fun i => revealChain index c mark j i
    return (⟨fun i => cols i (openedPos mark j i),
      data.subPath index c mark.super j (mark.child j)⟩ : SubOpening)
  return ⟨sub, data.topPath index c mark.super⟩

/-- No coordinate is revealed when WOTS encoding fails. On success only the 64 frontiers and the
opened forest chains are read; all path values are public structural labels. -/
def finishSource (parameter : PublicParameter) (data : PublicData)
    (message : Message) (randomness : Randomness) : OracleComp HashViewSpec (Option Signature) := do
  let digest ← liftM (messageDigest parameter data.root message randomness :
    OracleComp HashSpec MessageDigest)
  let index := digestIndex digest
  let some (counter, word) ← liftM (ReferenceChoice.search parameter topLayer rootTree index
    (data.forestKey index) encodingAttemptLimit 0) | return none
  let values ← sequenceFin fun chain => reveal (.chain topLayer rootTree index chain (word chain))
  let opening ← sequenceFin fun c => coordSource data index c (digestMarks digest c)
  let top : LayerSignature topLayer := ⟨counter, values, data.treePath index⟩
  return some ⟨randomness, opening, Fin.cases top (fun i => Fin.elim0 i)⟩

/-- The forest opening read from a coordinate table. -/
def assembledForest (data : PublicData) (table : HiddenGraph.Table) (index : Index)
    (marks : Coord → CoordMark) : Coord → CoordOpening :=
  fun c => ⟨fun j => ⟨fun i => table (.fchain index c (marks c).super j ((marks c).child j) i
      (openedPos (marks c) j i)), data.subPath index c (marks c).super j ((marks c).child j)⟩,
    data.topPath index c (marks c).super⟩

noncomputable def assembled (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (data : PublicData) (table : HiddenGraph.Table) (message : Message) (randomness : Randomness) :
    Option Signature :=
  let digest := evalWithAnswerFn f (messageDigest parameter data.root message randomness :
    OracleComp HashSpec MessageDigest)
  let index := digestIndex digest
  (firstEncoding f parameter topLayer rootTree index (data.forestKey index) encodingAttemptLimit 0).map
    fun pair => ⟨randomness, assembledForest data table index (digestMarks digest),
      Fin.cases (⟨pair.1, (fun chain => table (.chain topLayer rootTree index chain (pair.2 chain))),
        data.treePath index⟩ : LayerSignature topLayer) (fun i => Fin.elim0 i)⟩

theorem eval_forestOpen_assembled (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (seed : MasterSeed) (data : PublicData) (table : HiddenGraph.Table)
    (hdata : DataCorrect f parameter seed data)
    (htable : CoordinatesCorrect f parameter seed table) (index : Index) (marks : Coord → CoordMark) :
    evalWithAnswerFn f (Seeded.forestOpen parameter index marks seed :
      OracleComp HashSpec (Coord → CoordOpening)) = assembledForest data table index marks := by
  funext c
  simp only [Seeded.forestOpen, eval_sequenceFin, eval_coordOpen, assembledForest, htable.2, hdata.subPath,
    hdata.topPath, openedPos]
  rfl

theorem eval_finishSign_assembled (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (seed : MasterSeed) (data : PublicData) (table : HiddenGraph.Table)
    (hdata : DataCorrect f parameter seed data)
    (htable : CoordinatesCorrect f parameter seed table)
    (message : Message) (randomness : Randomness)
    (hland : Landed parameter (digestIndex (evalWithAnswerFn f
      (messageDigest parameter data.root message randomness : OracleComp HashSpec MessageDigest)))) :
    evalWithAnswerFn f (Randomized.finishSign ⟨seed, parameter, data.root⟩ message randomness) =
      assembled f parameter data table message randomness := by
  have hchains (word : Encoding) :
      (fun chain => table (.chain topLayer rootTree
        (digestIndex (evalWithAnswerFn f (messageDigest parameter data.root message randomness :
          OracleComp HashSpec MessageDigest))) chain (word chain))) =
      (fun chain => evalWithAnswerFn f (chainWalk parameter topLayer rootTree
        (digestIndex (evalWithAnswerFn f (messageDigest parameter data.root message randomness :
          OracleComp HashSpec MessageDigest))) chain 0 (word chain).val
          (Completeness.otsSecret f parameter topLayer rootTree
            (digestIndex (evalWithAnswerFn f (messageDigest parameter data.root message randomness :
              OracleComp HashSpec MessageDigest))) seed chain) : OracleComp HashSpec Digest)) := by
    funext chain
    exact htable.1 _ hland chain (word chain)
  simp only [Randomized.finishSign, assembled, evalWithAnswerFn_bind, eval_sequenceFin,
    sequenceLayers, Seeded.signLayer, Seeded.layerMessage, treeIndexAt_eq, leafIndexAt_eq,
    Seeded.otsSign, otsSignFrom_eq_firstEncoding, hdata.forestKey,
    hdata.treePath _ hland, hchains, eval_forestOpen_assembled f parameter seed data table hdata htable]
  cases hs : firstEncoding f parameter topLayer rootTree
      (digestIndex (evalWithAnswerFn f (messageDigest parameter data.root message randomness :
        OracleComp HashSpec MessageDigest)))
      (evalWithAnswerFn f (Seeded.forestKey parameter
        (digestIndex (evalWithAnswerFn f (messageDigest parameter data.root message randomness :
          OracleComp HashSpec MessageDigest))) seed : OracleComp HashSpec Digest))
      encodingAttemptLimit 0 <;>
    simp only [Option.map_none, Option.map_some, evalWithAnswerFn_pure, evalWithAnswerFn_bind,
      derivedSecrets, Completeness.otsSecret]

end Sphincs.Security.GraphView
