module

public import XmssSecurity.Proof.CappedGlobalKeygen
public import XmssSecurity.Proof.CappedChain.CausalSigningKeygenCoupling
public import XmssSecurity.Proof.TreeCacheVocabulary
public import XmssSecurity.Proof.StatementLemmas

@[expose] public section

/-!
# Key generation over two chain tables

Two key generations whose chains were presampled into different tables run with equal outputs, and
their final caches replay the same trees of both layers.
-/

open OracleComp OracleSpec
open OracleComp.ProgramLogic.Relational

namespace XmssSecurity.CappedChain

open Concrete.CacheReplay

attribute [local irreducible] Concrete.topTreeNode

theorem GlobalTreeCacheCorrespondence.replayLeaves
    (parameter : PublicParameter)
    (leftStart rightStart : ChainKey → ChainIndex → Digest)
    (leftCache rightCache : QueryCache HashSpec)
    (leftEndpoints rightEndpoints : ChainKey → ChainIndex → Digest)
    (htree : GlobalTreeCacheCorrespondence parameter leftEndpoints
      rightEndpoints leftCache rightCache)
    (hleftReplay : ReplayEndpointsMatch parameter leftStart leftEndpoints leftCache)
    (hrightReplay : ReplayEndpointsMatch parameter rightStart rightEndpoints rightCache) :
    LeafReplayOutputsCorrespond parameter leftStart rightStart leftCache rightCache := by
  intro key
  rw [← hleftReplay key, ← hrightReplay key]
  exact htree.leaves key

section Replay

variable {parameter : PublicParameter} {leftStart rightStart : ChainKey → ChainIndex → Digest}
  {leftWarm rightWarm leftCache rightCache : QueryCache HashSpec}

theorem KeygenRunRelation.leftReplayEndpoints
    (hleftWarm : ChainsWarm parameter leftStart leftWarm)
    (hrel : KeygenRunRelation parameter leftStart rightStart leftWarm rightWarm
      leftCache rightCache) :
    ReplayEndpointsMatch parameter leftStart (keyOneTimePublicKey leftWarm parameter leftStart)
      leftCache :=
  fun key => (hleftWarm.keyOneTimePublicKey_eq hrel.1 key).symm

theorem KeygenRunRelation.rightReplayEndpoints
    (hrightWarm : ChainsWarm parameter rightStart rightWarm)
    (hrel : KeygenRunRelation parameter leftStart rightStart leftWarm rightWarm
      leftCache rightCache) :
    ReplayEndpointsMatch parameter rightStart (keyOneTimePublicKey rightWarm parameter rightStart)
      rightCache :=
  fun key => (hrightWarm.keyOneTimePublicKey_eq hrel.2.1 key).symm

theorem KeygenRunRelation.keyLeafHash_eq
    (hleftWarm : ChainsWarm parameter leftStart leftWarm)
    (hrightWarm : ChainsWarm parameter rightStart rightWarm)
    (hrel : KeygenRunRelation parameter leftStart rightStart leftWarm rightWarm
      leftCache rightCache) (key : ChainKey) :
    Concrete.CacheView.digestAt leftCache (Concrete.CacheView.keyLeafInput parameter key
        (keyOneTimePublicKey leftCache parameter leftStart key)) =
      Concrete.CacheView.digestAt rightCache (Concrete.CacheView.keyLeafInput parameter key
        (keyOneTimePublicKey rightCache parameter rightStart key)) := by
  have hlookup := GlobalTreeCacheCorrespondence.replayLeaves parameter leftStart rightStart
    leftCache rightCache _ _ hrel.2.2 (KeygenRunRelation.leftReplayEndpoints hleftWarm hrel)
    (KeygenRunRelation.rightReplayEndpoints hrightWarm hrel) key
  unfold hashCacheLookup at hlookup
  unfold Concrete.CacheView.digestAt
  split <;> split <;> simp_all

theorem KeygenRunRelation.treeNode_eq
    (hleftWarm : ChainsWarm parameter leftStart leftWarm)
    (hrightWarm : ChainsWarm parameter rightStart rightWarm)
    (hrel : KeygenRunRelation parameter leftStart rightStart leftWarm rightWarm
      leftCache rightCache) :
    ∀ (levels : Nat) (node : MerkleNode),
      treeNode leftCache parameter (fun leafIndex => leftStart (.inl leafIndex)) levels node =
        treeNode rightCache parameter (fun leafIndex => rightStart (.inl leafIndex)) levels node := by
  intro levels
  induction levels with
  | zero =>
      intro node
      rw [treeNode_zero_eq, treeNode_zero_eq]
      exact KeygenRunRelation.keyLeafHash_eq hleftWarm hrightWarm hrel (.inl node)
  | succ levels ih =>
      intro node
      rw [treeNode_succ_eq, treeNode_succ_eq, ih, ih]
      split
      · unfold Concrete.CacheView.merkleHash Concrete.CacheView.digestAt
        rw [hrel.2.2.merkle _ (merkleHashInput_merkleInput _ _ _ _ _)]
      · rfl

theorem KeygenRunRelation.topTreeNode_eq
    (hleftWarm : ChainsWarm parameter leftStart leftWarm)
    (hrightWarm : ChainsWarm parameter rightStart rightWarm)
    (hrel : KeygenRunRelation parameter leftStart rightStart leftWarm rightWarm
      leftCache rightCache) :
    ∀ (levels : Nat) (node : TopNode),
      topTreeNode leftCache parameter (fun key => leftStart (.inr key)) levels node =
        topTreeNode rightCache parameter (fun key => rightStart (.inr key)) levels node := by
  intro levels
  induction levels with
  | zero =>
      intro node
      rw [topTreeNode_zero_eq, topTreeNode_zero_eq]
      exact KeygenRunRelation.keyLeafHash_eq hleftWarm hrightWarm hrel (.inr node)
  | succ levels ih =>
      intro node
      rw [topTreeNode_succ_eq, topTreeNode_succ_eq, ih, ih]
      split
      · unfold Concrete.CacheView.topMerkleHash Concrete.CacheView.digestAt
        rw [hrel.2.2.merkle _ (merkleHashInput_topMerkleInput _ _ _ _ _)]
      · rfl

theorem KeygenRunRelation.authenticationPath_eq
    (hleftWarm : ChainsWarm parameter leftStart leftWarm)
    (hrightWarm : ChainsWarm parameter rightStart rightWarm)
    (hrel : KeygenRunRelation parameter leftStart rightStart leftWarm rightWarm
      leftCache rightCache)
    (leftSigned rightSigned : TopIndex → Option (Randomness × Encoding)) (leafIndex : LeafIndex) :
    authenticationPath leftCache (startSecretKey parameter leftStart leftSigned) leafIndex =
      authenticationPath rightCache (startSecretKey parameter rightStart rightSigned) leafIndex := by
  funext level
  exact KeygenRunRelation.treeNode_eq hleftWarm hrightWarm hrel level.val _

theorem KeygenRunRelation.honestTopPath_eq
    (hleftWarm : ChainsWarm parameter leftStart leftWarm)
    (hrightWarm : ChainsWarm parameter rightStart rightWarm)
    (hrel : KeygenRunRelation parameter leftStart rightStart leftWarm rightWarm
      leftCache rightCache)
    (leftSigned rightSigned : TopIndex → Option (Randomness × Encoding)) (key : TopIndex)
    (level : Nat) :
    Concrete.honestTopPath leftCache (startSecretKey parameter leftStart leftSigned) key level =
      Concrete.honestTopPath rightCache (startSecretKey parameter rightStart rightSigned) key
        level := by
  unfold Concrete.honestTopPath
  split
  · exact KeygenRunRelation.topTreeNode_eq hleftWarm hrightWarm hrel level _
  · rfl

end Replay

/-- Key generation from two presampled trajectory materials couples with equal outputs. -/
theorem relTriple_programmedMaterial_honestKeygenFrom_run
    (parameter : PublicParameter) (left right : GlobalChainTrajectoryMaterial)
    (hleft : left ∈ support (programmedGlobalChainTrajectoryMaterial parameter))
    (hright : right ∈ support (programmedGlobalChainTrajectoryMaterial parameter))
    (topBase : TopIndex → Randomness) :
    RelTriple
      ((simulateQ randomOracle (Concrete.honestKeygenFrom parameter left.1 topBase)).run
        left.2.2)
      ((simulateQ randomOracle (Concrete.honestKeygenFrom parameter right.1 topBase)).run
        right.2.2)
      (KeygenRunResult parameter left.1 right.1 left.2.2 right.2.2) :=
  relTriple_honestKeygenFrom_run
    (programmedGlobalChainTrajectoryMaterial_chainsWarm parameter left hleft)
    (programmedGlobalChainTrajectoryMaterial_chainsWarm parameter right hright) topBase
    left.2.2 right.2.2
    (programmedGlobalChainTrajectoryMaterial_initialRelation parameter left right hleft hright)

end XmssSecurity.CappedChain
