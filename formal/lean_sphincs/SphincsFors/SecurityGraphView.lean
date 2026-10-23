import SphincsFors.SecurityEncodingPreparation
import SphincsFors.SecurityHiddenGraphRows
import SphincsFors.SecurityGraphCorrectness

/-! Signature assembly from public structural labels and explicit coordinate disclosures.
This file establishes the exact output view; preservation of the original internal hash cost
is a separate obligation when composing the complete monitored game. -/

open OracleComp OracleSpec

namespace SphincsFors.Security.GraphView
open Concrete Completeness Graph GraphCorrectness HiddenGraph Prefix

attribute [local irreducible] firstEncoding encodingAttemptLimit Seeded.ftsKey Seeded.ftsOpen
  Seeded.treePath Seeded.signLayer chainWalk sequenceFin encode
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

structure PublicData where
  root : Digest
  forsKey : Index → Digest
  treePath : LeafIndex → Fin (layerHeight topLayer) → Digest
  forsPath : Index → (IndexGroup → FtsLeaf) → FtsTree → Fin ftsTreeHeight → Digest

def publicData (labels : CanonicalGraphLabels) : PublicData where
  root := truncateHash (labels (treePosition topLayer rootTree totalHeight le_rfl ⟨0, by decide⟩))
  forsKey := fun index => truncateHash (labels (.ftsRoots index))
  treePath := fun leaf level => truncateHash (labels
    (treePosition topLayer rootTree level.val (Nat.le_of_lt level.isLt)
      ⟨Nat.xor (leaf.val / 2 ^ level.val) 1,
        Nat.xor_lt_two_pow ((Nat.div_le_self _ _).trans_lt leaf.isLt) one_lt_leaf_capacity⟩))
  forsPath := fun index leaves tree level => truncateHash (labels
    (forsPosition index tree level.val (Nat.le_of_lt level.isLt)
      ⟨Nat.xor ((leaves tree).val / 2 ^ level.val) 1,
        Nat.xor_lt_two_pow ((Nat.div_le_self _ _).trans_lt (leaves tree).isLt) (by decide)⟩))

variable [Params]

structure DataCorrect (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (seed : MasterSeed) (data : PublicData) : Prop where
  root : data.root = evalWithAnswerFn f
    (Seeded.treeRoot parameter topLayer rootTree seed : OracleComp HashSpec Digest)
  forsKey : ∀ index, data.forsKey index = evalWithAnswerFn f
    (Seeded.ftsKey parameter index seed : OracleComp HashSpec Digest)
  treePath : ∀ leaf, Landed parameter leaf → data.treePath leaf = evalWithAnswerFn f
    (Seeded.treePath parameter topLayer rootTree seed leaf :
      OracleComp HashSpec (Fin (layerHeight topLayer) → Digest))
  forsPath : ∀ index leaves, data.forsPath index leaves = evalWithAnswerFn f
    (Seeded.ftsOpen parameter index leaves seed :
      OracleComp HashSpec (FtsTree → Fin ftsTreeHeight → Digest))

theorem publicData_correct (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (seed : MasterSeed) (labels : CanonicalGraphLabels)
    (hconsistent : Consistent f parameter seed labels)
    (hboundary : BoundaryCorrect f parameter seed labels) :
    DataCorrect f parameter seed (publicData labels) := by
  constructor
  · exact tree_root_value f parameter seed labels hconsistent hboundary topLayer rootTree
  · exact fors_key_value f parameter seed labels hconsistent
  · intro leaf hland
    funext level
    simpa only [publicData, canonicalTreePath, dite_eq_left level.isLt] using
      tree_path_sibling f parameter seed labels hconsistent hboundary topLayer rootTree
        leaf hland level.val level.isLt
  · intro index leaves
    funext tree level
    have h := fors_path_sibling f parameter seed labels hconsistent index tree (leaves tree)
      level.val level.isLt
    simpa only [publicData, eval_ftsOpen, Fors.extendPath, dite_eq_left level.isLt,
      Fors.canonicalPath, ftsIndexOf] using h

def CoordinatesCorrect (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (seed : MasterSeed) (table : HiddenGraph.Table) : Prop :=
  (∀ leaf, Landed parameter leaf → ∀ chain position,
    table (.chain topLayer rootTree leaf chain position) =
      Chain.honestChain f parameter topLayer rootTree leaf chain
        (Completeness.otsSecret f parameter topLayer rootTree leaf seed chain) position.val) ∧
  (∀ index tree leaf, table (.ftsSecret index tree leaf) =
    Completeness.ftsSecret f parameter index tree leaf seed)

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
    · rw [coordinates, dite_eq_right hz]
      have hstep : position.val - 1 < chainLength - 1 := by have := position.isLt; omega
      have h := chain_value f parameter seed labels hconsistent topLayer rootTree leaf hland
        chain ⟨position.val - 1, hstep⟩
      simpa only [Nat.sub_add_cancel (by omega : 1 ≤ position.val), otsSecrets] using h
  · intros; rfl

abbrev HashViewSpec := HashSpec + (Coordinate →ₒ Digest)

def reveal (coordinate : Coordinate) : OracleComp HashViewSpec Digest :=
  liftM ((Coordinate →ₒ Digest).query coordinate)

def fixedView (f : QueryImpl HashSpec Id) (table : HiddenGraph.Table) : QueryImpl HashViewSpec Id :=
  f + (show QueryImpl (Coordinate →ₒ Digest) Id from table)

/-- No coordinate is revealed when WOTS encoding fails. On success only the 64 frontiers
and 24 selected FORS secrets are read; all path values are public structural labels. -/
def finishSource (parameter : PublicParameter) (data : PublicData)
    (message : Message) (randomness : Randomness) : OracleComp HashViewSpec (Option Signature) := do
  let digest ← liftM (messageDigest parameter data.root message randomness :
    OracleComp HashSpec MessageDigest)
  let index := digestIndex digest
  let some (counter, word) ← liftM (ReferenceChoice.search parameter topLayer rootTree index
    (data.forsKey index) encodingAttemptLimit 0) | return none
  let values ← sequenceFin fun chain => reveal (.chain topLayer rootTree index chain (word chain))
  let secrets ← sequenceFin fun tree => reveal (.ftsSecret index tree (digestLeaves digest tree))
  let top : LayerSignature topLayer := ⟨counter, values, data.treePath index⟩
  return some ⟨randomness, secrets, data.forsPath index (digestLeaves digest),
    Fin.cases top (fun i => Fin.elim0 i)⟩

noncomputable def assembled (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (data : PublicData) (table : HiddenGraph.Table) (message : Message) (randomness : Randomness) :
    Option Signature :=
  let digest := evalWithAnswerFn f (messageDigest parameter data.root message randomness :
    OracleComp HashSpec MessageDigest)
  let index := digestIndex digest
  (firstEncoding f parameter topLayer rootTree index (data.forsKey index) encodingAttemptLimit 0).map
    fun pair => ⟨randomness,
      (fun tree => table (.ftsSecret index tree (digestLeaves digest tree))),
      data.forsPath index (digestLeaves digest),
      Fin.cases (⟨pair.1, (fun chain => table (.chain topLayer rootTree index chain (pair.2 chain))),
        data.treePath index⟩ : LayerSignature topLayer) (fun i => Fin.elim0 i)⟩

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
    Seeded.otsSign, otsSignFrom_eq_firstEncoding, hdata.forsKey, hdata.forsPath,
    hdata.treePath _ hland, htable.2, hchains]
  cases hs : firstEncoding f parameter topLayer rootTree
      (digestIndex (evalWithAnswerFn f (messageDigest parameter data.root message randomness :
        OracleComp HashSpec MessageDigest)))
      (evalWithAnswerFn f (Seeded.ftsKey parameter
        (digestIndex (evalWithAnswerFn f (messageDigest parameter data.root message randomness :
          OracleComp HashSpec MessageDigest))) seed : OracleComp HashSpec Digest))
      encodingAttemptLimit 0 <;>
    simp only [Option.map_none, Option.map_some, evalWithAnswerFn_pure, evalWithAnswerFn_bind,
      derivedSecrets, Completeness.otsSecret, Completeness.ftsSecret, ftsIndexOf]

end SphincsFors.Security.GraphView
