module

public import XmssSecurity.Proof.TreeCacheVocabulary
public import XmssSecurity.Proof.CacheAgreement

@[expose] public section

/-!
# Coupling key generation over two chain tables

Once every chain of both layers is cached, key generation's remaining queries are leaves, Merkle
nodes and top digests. Two runs from caches holding different chain tables couple with equal outputs:
a leaf query is fresh on both sides or answered alike, and every other query has the same input.
-/

open OracleComp OracleSpec ENNReal
open OracleComp.ProgramLogic.Relational

namespace XmssSecurity

open Concrete.CacheReplay

attribute [local irreducible] Concrete.topTreeNode

/-- Every chain prefix of both layers ran below the cache. -/
def ChainsWarm (parameter : PublicParameter) (start : ChainKey → ChainIndex → Digest)
    (cache : QueryCache HashSpec) : Prop :=
  ∀ key chain steps, steps ≤ chainLength - 1 →
    RunsBelow (Concrete.keyChainWalk parameter key chain 0 steps (start key chain) :
      OracleComp HashSpec Digest) cache

theorem ChainsWarm.mono {parameter : PublicParameter} {start : ChainKey → ChainIndex → Digest}
    {cache larger : QueryCache HashSpec} (hwarm : ChainsWarm parameter start cache)
    (hle : cache ≤ larger) : ChainsWarm parameter start larger :=
  fun key chain steps hsteps => (hwarm key chain steps hsteps).mono hle

theorem ChainsWarm.keyChainWalk_run_eq {parameter : PublicParameter}
    {start : ChainKey → ChainIndex → Digest} {warm cache : QueryCache HashSpec}
    (hwarm : ChainsWarm parameter start warm) (hle : warm ≤ cache)
    (key : ChainKey) (chain : ChainIndex) (steps : Nat) (hsteps : steps ≤ chainLength - 1) :
    (simulateQ randomOracle
      (Concrete.keyChainWalk parameter key chain 0 steps (start key chain) :
        OracleComp HashSpec Digest)).run cache =
      pure (Wots.walk (Concrete.CacheView.keyChainStep warm parameter key chain) 0 steps
        (start key chain), cache) := by
  rw [(hwarm key chain steps hsteps).run_eq cache hle, eval_keyChainWalk]

theorem ChainsWarm.keyOneTimePublicKey_eq {parameter : PublicParameter}
    {start : ChainKey → ChainIndex → Digest} {warm cache : QueryCache HashSpec}
    (hwarm : ChainsWarm parameter start warm) (hle : warm ≤ cache) (key : ChainKey) :
    keyOneTimePublicKey cache parameter start key =
      keyOneTimePublicKey warm parameter start key := by
  funext chain
  have heval := (hwarm key chain (chainLength - 1) le_rfl).eval_eq cache hle
  rw [eval_keyChainWalk, eval_keyChainWalk] at heval
  exact heval.symm

theorem sequenceFin_run_eq_pure
    {α : Type} {n : Nat} (computation : Fin n → OracleComp HashSpec α)
    (cache : QueryCache HashSpec) (values : Fin n → α)
    (hrun : ∀ index,
      (simulateQ randomOracle (computation index)).run cache =
        pure (values index, cache)) :
    (simulateQ randomOracle (Concrete.sequenceFin computation)).run cache =
      pure (values, cache) := by
  induction n with
  | zero =>
      have hvalues : (Fin.elim0 : Fin 0 → α) = values := by
        funext index
        exact Fin.elim0 index
      simp [Concrete.sequenceFin, hvalues]
  | succ n ih =>
      rw [Concrete.sequenceFin, simulateQ_bind, StateT.run_bind, hrun 0]
      simp only [pure_bind]
      rw [simulateQ_bind, StateT.run_bind,
        ih (fun index => computation index.succ)
          (fun index => values index.succ) (fun index => hrun index.succ)]
      simp only [pure_bind, simulateQ_pure, StateT.run_pure]
      congr
      funext index
      exact Fin.cases rfl (fun _ => rfl) index

theorem ChainsWarm.oneTimePublicKey_run_eq {parameter : PublicParameter}
    {start : ChainKey → ChainIndex → Digest} {warm cache : QueryCache HashSpec}
    (hwarm : ChainsWarm parameter start warm) (hle : warm ≤ cache) (leafIndex : LeafIndex) :
    (simulateQ randomOracle
      (Concrete.oneTimePublicKey parameter (fun leafIndex => start (.inl leafIndex)) leafIndex :
        OracleComp HashSpec (ChainIndex → Digest))).run cache =
      pure (keyOneTimePublicKey warm parameter start (.inl leafIndex), cache) := by
  unfold Concrete.oneTimePublicKey
  apply sequenceFin_run_eq_pure
  intro chain
  rw [← Concrete.keyChainWalk_inl]
  exact hwarm.keyChainWalk_run_eq hle (.inl leafIndex) chain (chainLength - 1) le_rfl

theorem ChainsWarm.topOneTimePublicKey_run_eq {parameter : PublicParameter}
    {start : ChainKey → ChainIndex → Digest} {warm cache : QueryCache HashSpec}
    (hwarm : ChainsWarm parameter start warm) (hle : warm ≤ cache) (key : TopIndex) :
    (simulateQ randomOracle
      (Concrete.topOneTimePublicKey parameter (fun key => start (.inr key)) key :
        OracleComp HashSpec (ChainIndex → Digest))).run cache =
      pure (keyOneTimePublicKey warm parameter start (.inr key), cache) := by
  unfold Concrete.topOneTimePublicKey
  apply sequenceFin_run_eq_pure
  intro chain
  rw [← Concrete.keyChainWalk_inr]
  exact hwarm.keyChainWalk_run_eq hle (.inr key) chain (chainLength - 1) le_rfl

structure GlobalTreeCacheCorrespondence
    (parameter : PublicParameter)
    (leftEndpoints rightEndpoints : ChainKey → ChainIndex → Digest)
    (leftCache rightCache : QueryCache HashSpec) : Prop where
  merkle : HashCachesAgreeOn (MerkleHashInput parameter) leftCache rightCache
  leaves : LeafCacheOutputsCorrespond parameter leftEndpoints rightEndpoints
    leftCache rightCache

theorem GlobalTreeCacheCorrespondence.cacheQuery_retained
    {parameter : PublicParameter}
    {leftEndpoints rightEndpoints : ChainKey → ChainIndex → Digest}
    {leftCache rightCache : QueryCache HashSpec}
    (hrel : GlobalTreeCacheCorrespondence parameter leftEndpoints rightEndpoints
      leftCache rightCache)
    (input : HashInput) (hinput : MerkleHashInput parameter input) (output : HashOutput) :
    GlobalTreeCacheCorrespondence parameter leftEndpoints rightEndpoints
      (leftCache.cacheQuery input output) (rightCache.cacheQuery input output) := by
  constructor
  · exact hrel.merkle.cacheQuery (MerkleHashInput parameter) leftCache rightCache _ output
  · apply hrel.leaves.cacheQuery_distinct
    · intro key
      exact merkleHashInput_ne_keyLeafInput parameter key _ input hinput
    · intro key
      exact merkleHashInput_ne_keyLeafInput parameter key _ input hinput

theorem GlobalTreeCacheCorrespondence.cacheQuery_leafPair
    {parameter : PublicParameter}
    {leftEndpoints rightEndpoints : ChainKey → ChainIndex → Digest}
    {leftCache rightCache : QueryCache HashSpec}
    (hrel : GlobalTreeCacheCorrespondence parameter leftEndpoints rightEndpoints
      leftCache rightCache)
    (key : ChainKey) (output : HashOutput) :
    GlobalTreeCacheCorrespondence parameter leftEndpoints rightEndpoints
      (leftCache.cacheQuery
        (Concrete.CacheView.keyLeafInput parameter key (leftEndpoints key)) output)
      (rightCache.cacheQuery
        (Concrete.CacheView.keyLeafInput parameter key (rightEndpoints key)) output) := by
  constructor
  · apply HashCachesAgreeOn.cacheQuery_distinct
      (MerkleHashInput parameter) leftCache rightCache hrel.merkle
    · intro input hinput
      exact merkleHashInput_ne_keyLeafInput parameter key _ input hinput
    · intro input hinput
      exact merkleHashInput_ne_keyLeafInput parameter key _ input hinput
  · exact hrel.leaves.cacheQuery_pair parameter leftEndpoints rightEndpoints
      leftCache rightCache key output

/-- Two caches extending warm chain caches of two tables, with corresponding trees. -/
def KeygenRunRelation (parameter : PublicParameter)
    (leftStart rightStart : ChainKey → ChainIndex → Digest)
    (leftWarm rightWarm leftCache rightCache : QueryCache HashSpec) : Prop :=
  leftWarm ≤ leftCache ∧ rightWarm ≤ rightCache ∧
    GlobalTreeCacheCorrespondence parameter
      (keyOneTimePublicKey leftWarm parameter leftStart)
      (keyOneTimePublicKey rightWarm parameter rightStart) leftCache rightCache

section Coupling

variable {parameter : PublicParameter} {leftStart rightStart : ChainKey → ChainIndex → Digest}
  {leftWarm rightWarm : QueryCache HashSpec}

/-- Equal outputs and related final caches. -/
def KeygenRunResult (parameter : PublicParameter)
    (leftStart rightStart : ChainKey → ChainIndex → Digest)
    (leftWarm rightWarm : QueryCache HashSpec) {α : Type}
    (left right : α × QueryCache HashSpec) : Prop :=
  left.1 = right.1 ∧
    KeygenRunRelation parameter leftStart rightStart leftWarm rightWarm left.2 right.2

theorem relTriple_randomOracle_retained
    {leftCache rightCache : QueryCache HashSpec}
    (hrel : KeygenRunRelation parameter leftStart rightStart leftWarm rightWarm
      leftCache rightCache)
    (input : HashInput) (hinput : MerkleHashInput parameter input) :
    RelTriple ((randomOracle input).run leftCache) ((randomOracle input).run rightCache)
      (KeygenRunResult parameter leftStart rightStart leftWarm rightWarm) := by
  obtain ⟨hleftLe, hrightLe, hcorr⟩ := hrel
  cases hleft : leftCache input with
  | none =>
      have hright : rightCache input = none := by
        rw [← hcorr.merkle input hinput]
        exact hleft
      rw [randomOracle, QueryImpl.withCaching_run_none _ hleft,
        QueryImpl.withCaching_run_none _ hright,
        map_eq_bind_pure_comp, map_eq_bind_pure_comp]
      apply relTriple_bind (relTriple_refl ($ᵗ HashOutput))
      intro leftOutput rightOutput houtput
      subst rightOutput
      apply relTriple_pure_pure
      exact ⟨rfl, hleftLe.trans (QueryCache.le_cacheQuery _ hleft),
        hrightLe.trans (QueryCache.le_cacheQuery _ hright),
        hcorr.cacheQuery_retained input hinput leftOutput⟩
  | some output =>
      have hright : rightCache input = some output := by
        rw [← hcorr.merkle input hinput]
        exact hleft
      rw [randomOracle, QueryImpl.withCaching_run_some _ hleft,
        QueryImpl.withCaching_run_some _ hright]
      exact relTriple_pure_pure ⟨rfl, hleftLe, hrightLe, hcorr⟩

theorem relTriple_randomOracle_leafPair
    {leftCache rightCache : QueryCache HashSpec}
    (hrel : KeygenRunRelation parameter leftStart rightStart leftWarm rightWarm
      leftCache rightCache) (key : ChainKey) :
    RelTriple
      ((randomOracle (Concrete.CacheView.keyLeafInput parameter key
        (keyOneTimePublicKey leftWarm parameter leftStart key))).run leftCache)
      ((randomOracle (Concrete.CacheView.keyLeafInput parameter key
        (keyOneTimePublicKey rightWarm parameter rightStart key))).run rightCache)
      (KeygenRunResult parameter leftStart rightStart leftWarm rightWarm) := by
  obtain ⟨hleftLe, hrightLe, hcorr⟩ := hrel
  have hlookup := hcorr.leaves key
  unfold hashCacheLookup at hlookup
  cases hleft : leftCache (Concrete.CacheView.keyLeafInput parameter key
      (keyOneTimePublicKey leftWarm parameter leftStart key)) with
  | none =>
      have hright : rightCache (Concrete.CacheView.keyLeafInput parameter key
          (keyOneTimePublicKey rightWarm parameter rightStart key)) = none := by
        rw [← hlookup]
        exact hleft
      rw [randomOracle, QueryImpl.withCaching_run_none _ hleft,
        QueryImpl.withCaching_run_none _ hright,
        map_eq_bind_pure_comp, map_eq_bind_pure_comp]
      apply relTriple_bind (relTriple_refl ($ᵗ HashOutput))
      intro leftOutput rightOutput houtput
      subst rightOutput
      apply relTriple_pure_pure
      exact ⟨rfl, hleftLe.trans (QueryCache.le_cacheQuery _ hleft),
        hrightLe.trans (QueryCache.le_cacheQuery _ hright),
        hcorr.cacheQuery_leafPair key leftOutput⟩
  | some output =>
      have hright : rightCache (Concrete.CacheView.keyLeafInput parameter key
          (keyOneTimePublicKey rightWarm parameter rightStart key)) = some output := by
        rw [← hlookup]
        exact hleft
      rw [randomOracle, QueryImpl.withCaching_run_some _ hleft,
        QueryImpl.withCaching_run_some _ hright]
      exact relTriple_pure_pure ⟨rfl, hleftLe, hrightLe, hcorr⟩

theorem Concrete.simulateQ_tweakableHash_run (parameter : PublicParameter) (domain : HashDomain)
    (payload : HashInput) (cache : QueryCache HashSpec) :
    (simulateQ randomOracle
      (Concrete.tweakableHash parameter domain payload : OracleComp HashSpec Digest)).run cache =
      (fun result : HashOutput × QueryCache HashSpec => (truncateHash result.1, result.2)) <$>
        (randomOracle (tweakableHashInput parameter domain payload)).run cache := by
  simp only [Concrete.tweakableHash, Concrete.oracleHash,
    HasQuery.instOfMonadLift_query, bind_pure_comp, simulateQ_map, StateT.run_map, simulateQ_spec_query]

theorem relTriple_tweakableHash_retained
    {leftCache rightCache : QueryCache HashSpec}
    (hrel : KeygenRunRelation parameter leftStart rightStart leftWarm rightWarm
      leftCache rightCache)
    (domain : HashDomain) (hdomain : domain.Retained) (payload : HashInput) :
    RelTriple
      ((simulateQ randomOracle (Concrete.tweakableHash parameter domain payload :
        OracleComp HashSpec Digest)).run leftCache)
      ((simulateQ randomOracle (Concrete.tweakableHash parameter domain payload :
        OracleComp HashSpec Digest)).run rightCache)
      (KeygenRunResult parameter leftStart rightStart leftWarm rightWarm) := by
  rw [Concrete.simulateQ_tweakableHash_run, Concrete.simulateQ_tweakableHash_run]
  change RelTriple
    ((fun result : HashOutput × QueryCache HashSpec => (truncateHash result.1, result.2)) <$>
      (randomOracle (tweakableHashInput parameter domain payload)).run leftCache)
    ((fun result : HashOutput × QueryCache HashSpec => (truncateHash result.1, result.2)) <$>
      (randomOracle (tweakableHashInput parameter domain payload)).run rightCache) _
  apply relTriple_map
  apply relTriple_post_mono (relTriple_randomOracle_retained hrel _
    ⟨domain, hdomain, (atHashAddress_tweakableHashInput_iff parameter _ _ _).2 rfl⟩)
  intro left right hresult
  exact ⟨congrArg truncateHash hresult.1, hresult.2⟩

theorem relTriple_keyLeafHash
    {leftCache rightCache : QueryCache HashSpec}
    (hrel : KeygenRunRelation parameter leftStart rightStart leftWarm rightWarm
      leftCache rightCache) (key : ChainKey) :
    RelTriple
      ((simulateQ randomOracle (Concrete.tweakableHash parameter key.leafDomain
        (Concrete.leafPayload (keyOneTimePublicKey leftWarm parameter leftStart key)) :
          OracleComp HashSpec Digest)).run leftCache)
      ((simulateQ randomOracle (Concrete.tweakableHash parameter key.leafDomain
        (Concrete.leafPayload (keyOneTimePublicKey rightWarm parameter rightStart key)) :
          OracleComp HashSpec Digest)).run rightCache)
      (KeygenRunResult parameter leftStart rightStart leftWarm rightWarm) := by
  rw [Concrete.simulateQ_tweakableHash_run, Concrete.simulateQ_tweakableHash_run]
  change RelTriple
    ((fun result : HashOutput × QueryCache HashSpec => (truncateHash result.1, result.2)) <$>
      (randomOracle (Concrete.CacheView.keyLeafInput parameter key
        (keyOneTimePublicKey leftWarm parameter leftStart key))).run leftCache)
    ((fun result : HashOutput × QueryCache HashSpec => (truncateHash result.1, result.2)) <$>
      (randomOracle (Concrete.CacheView.keyLeafInput parameter key
        (keyOneTimePublicKey rightWarm parameter rightStart key))).run rightCache) _
  apply relTriple_map
  apply relTriple_post_mono (relTriple_randomOracle_leafPair hrel key)
  intro left right hresult
  exact ⟨congrArg truncateHash hresult.1, hresult.2⟩

variable (hleftWarm : ChainsWarm parameter leftStart leftWarm)
  (hrightWarm : ChainsWarm parameter rightStart rightWarm)
include hleftWarm hrightWarm

theorem relTriple_treeNode_run :
    ∀ (levels : Nat) (node : MerkleNode) (leftCache rightCache : QueryCache HashSpec),
      KeygenRunRelation parameter leftStart rightStart leftWarm rightWarm leftCache rightCache →
      RelTriple
        ((simulateQ randomOracle
          (Concrete.treeNode parameter (fun leafIndex => leftStart (.inl leafIndex)) levels node :
            OracleComp HashSpec Digest)).run leftCache)
        ((simulateQ randomOracle
          (Concrete.treeNode parameter (fun leafIndex => rightStart (.inl leafIndex)) levels node :
            OracleComp HashSpec Digest)).run rightCache)
        (KeygenRunResult parameter leftStart rightStart leftWarm rightWarm) := by
  intro levels
  induction levels with
  | zero =>
      intro node leftCache rightCache hrel
      rw [Concrete.treeNode_zero_eq, Concrete.treeNode_zero_eq, Concrete.leafAt,
        Concrete.leafAt, simulateQ_bind, StateT.run_bind, simulateQ_bind, StateT.run_bind,
        hleftWarm.oneTimePublicKey_run_eq hrel.1 node,
        hrightWarm.oneTimePublicKey_run_eq hrel.2.1 node, pure_bind, pure_bind]
      exact relTriple_keyLeafHash hrel (.inl node)
  | succ levels ih =>
      intro node leftCache rightCache hrel
      rw [Concrete.treeNode_succ_eq, Concrete.treeNode_succ_eq, simulateQ_bind,
        StateT.run_bind, simulateQ_bind, StateT.run_bind]
      apply relTriple_bind (ih _ leftCache rightCache hrel)
      intro leftChild rightChild hchild
      obtain ⟨hchildEq, hchildRel⟩ := hchild
      rw [simulateQ_bind, StateT.run_bind, simulateQ_bind, StateT.run_bind, hchildEq]
      apply relTriple_bind (ih _ leftChild.2 rightChild.2 hchildRel)
      intro leftOther rightOther hother
      obtain ⟨hotherEq, hotherRel⟩ := hother
      rw [hotherEq]
      split
      · exact relTriple_tweakableHash_retained hotherRel (.merkle _ node) trivial _
      · exact relTriple_pure_pure ⟨rfl, hotherRel⟩

theorem relTriple_topTreeNode_run :
    ∀ (levels : Nat) (node : TopNode) (leftCache rightCache : QueryCache HashSpec),
      KeygenRunRelation parameter leftStart rightStart leftWarm rightWarm leftCache rightCache →
      RelTriple
        ((simulateQ randomOracle
          (Concrete.topTreeNode parameter (fun key => leftStart (.inr key)) levels node :
            OracleComp HashSpec Digest)).run leftCache)
        ((simulateQ randomOracle
          (Concrete.topTreeNode parameter (fun key => rightStart (.inr key)) levels node :
            OracleComp HashSpec Digest)).run rightCache)
        (KeygenRunResult parameter leftStart rightStart leftWarm rightWarm) := by
  intro levels
  induction levels with
  | zero =>
      intro node leftCache rightCache hrel
      rw [Concrete.topTreeNode, Concrete.topTreeNode, Concrete.topLeafAt,
        Concrete.topLeafAt, simulateQ_bind, StateT.run_bind, simulateQ_bind, StateT.run_bind,
        hleftWarm.topOneTimePublicKey_run_eq hrel.1 node,
        hrightWarm.topOneTimePublicKey_run_eq hrel.2.1 node, pure_bind, pure_bind]
      exact relTriple_keyLeafHash hrel (.inr node)
  | succ levels ih =>
      intro node leftCache rightCache hrel
      rw [Concrete.topTreeNode, Concrete.topTreeNode, simulateQ_bind,
        StateT.run_bind, simulateQ_bind, StateT.run_bind]
      apply relTriple_bind (ih _ leftCache rightCache hrel)
      intro leftChild rightChild hchild
      obtain ⟨hchildEq, hchildRel⟩ := hchild
      rw [simulateQ_bind, StateT.run_bind, simulateQ_bind, StateT.run_bind, hchildEq]
      apply relTriple_bind (ih _ leftChild.2 rightChild.2 hchildRel)
      intro leftOther rightOther hother
      obtain ⟨hotherEq, hotherRel⟩ := hother
      rw [hotherEq]
      split
      · exact relTriple_tweakableHash_retained hotherRel (.topMerkle _ node) trivial _
      · exact relTriple_pure_pure ⟨rfl, hotherRel⟩

omit hleftWarm hrightWarm in
theorem relTriple_topSignFrom_run (key : TopIndex) (root : Digest) (base : Randomness) :
    ∀ (attempts trial : Nat) (leftCache rightCache : QueryCache HashSpec),
      KeygenRunRelation parameter leftStart rightStart leftWarm rightWarm leftCache rightCache →
      RelTriple
        ((simulateQ randomOracle (Concrete.topSignFrom parameter key root base attempts trial :
          OracleComp HashSpec (Option (Randomness × Encoding)))).run leftCache)
        ((simulateQ randomOracle (Concrete.topSignFrom parameter key root base attempts trial :
          OracleComp HashSpec (Option (Randomness × Encoding)))).run rightCache)
        (KeygenRunResult parameter leftStart rightStart leftWarm rightWarm) := by
  intro attempts
  induction attempts with
  | zero =>
      intro trial leftCache rightCache hrel
      exact relTriple_pure_pure ⟨rfl, hrel⟩
  | succ attempts ih =>
      intro trial leftCache rightCache hrel
      rw [Concrete.topSignFrom, simulateQ_bind, StateT.run_bind]
      apply relTriple_bind (relTriple_tweakableHash_retained hrel (.topEncoding key) trivial _)
      rintro ⟨leftValue, leftDigestCache⟩ ⟨rightValue, rightDigestCache⟩ ⟨hdigestEq, hdigestRel⟩
      dsimp only at hdigestEq hdigestRel ⊢
      subst hdigestEq
      cases TargetSum.decodeDigest leftValue with
      | some encoding =>
          simp only [simulateQ_pure, StateT.run_pure]
          exact relTriple_pure_pure ⟨rfl, hdigestRel⟩
      | none => exact ih _ _ _ hdigestRel

omit hleftWarm hrightWarm in
theorem relTriple_sequenceFin_run {β : Type} :
    ∀ {n : Nat} (leftComputation rightComputation : Fin n → OracleComp HashSpec β),
      (∀ index leftCache rightCache,
        KeygenRunRelation parameter leftStart rightStart leftWarm rightWarm leftCache rightCache →
        RelTriple ((simulateQ randomOracle (leftComputation index)).run leftCache)
          ((simulateQ randomOracle (rightComputation index)).run rightCache)
          (KeygenRunResult parameter leftStart rightStart leftWarm rightWarm)) →
      ∀ leftCache rightCache,
        KeygenRunRelation parameter leftStart rightStart leftWarm rightWarm leftCache rightCache →
        RelTriple
          ((simulateQ randomOracle (Concrete.sequenceFin leftComputation)).run leftCache)
          ((simulateQ randomOracle (Concrete.sequenceFin rightComputation)).run rightCache)
          (KeygenRunResult parameter leftStart rightStart leftWarm rightWarm) := by
  intro n
  induction n with
  | zero =>
      intro leftComputation rightComputation _ leftCache rightCache hrel
      exact relTriple_pure_pure ⟨rfl, hrel⟩
  | succ n ih =>
      intro leftComputation rightComputation hcomponent leftCache rightCache hrel
      rw [Concrete.sequenceFin, Concrete.sequenceFin, simulateQ_bind, StateT.run_bind,
        simulateQ_bind, StateT.run_bind]
      apply relTriple_bind (hcomponent 0 leftCache rightCache hrel)
      intro leftHead rightHead hhead
      obtain ⟨hheadEq, hheadRel⟩ := hhead
      rw [simulateQ_bind, StateT.run_bind, simulateQ_bind, StateT.run_bind]
      apply relTriple_bind (ih (fun index => leftComputation index.succ)
        (fun index => rightComputation index.succ)
        (fun index => hcomponent index.succ) _ _ hheadRel)
      intro leftTail rightTail htail
      obtain ⟨htailEq, htailRel⟩ := htail
      rw [hheadEq, htailEq]
      exact relTriple_pure_pure ⟨rfl, htailRel⟩

/-- Key generation from two warm chain caches couples with equal outputs. -/
theorem relTriple_honestKeygenFrom_run (topBase : TopIndex → Randomness)
    (leftCache rightCache : QueryCache HashSpec)
    (hrel : KeygenRunRelation parameter leftStart rightStart leftWarm rightWarm
      leftCache rightCache) :
    RelTriple
      ((simulateQ randomOracle (Concrete.honestKeygenFrom parameter leftStart topBase)).run
        leftCache)
      ((simulateQ randomOracle (Concrete.honestKeygenFrom parameter rightStart topBase)).run
        rightCache)
      (KeygenRunResult parameter leftStart rightStart leftWarm rightWarm) := by
  unfold Concrete.honestKeygenFrom Concrete.honestKeygen
  rw [simulateQ_bind, StateT.run_bind, simulateQ_bind, StateT.run_bind]
  apply relTriple_bind (relTriple_sequenceFin_run _ _ (fun key cL cR hcomponent => by
    rw [simulateQ_bind, StateT.run_bind, simulateQ_bind, StateT.run_bind]
    apply relTriple_bind (relTriple_treeNode_run hleftWarm hrightWarm treeHeight
      (Concrete.bottomRootNode key) cL cR hcomponent)
    intro leftRoot rightRoot hroot
    obtain ⟨hrootEq, hrootRel⟩ := hroot
    rw [hrootEq]
    exact relTriple_topSignFrom_run key rightRoot.1 (topBase key) _ 0 _ _ hrootRel)
    leftCache rightCache hrel)
  intro leftSigned rightSigned hsigned
  obtain ⟨hsignedEq, hsignedRel⟩ := hsigned
  rw [simulateQ_bind, StateT.run_bind, simulateQ_bind, StateT.run_bind]
  apply relTriple_bind (relTriple_topTreeNode_run hleftWarm hrightWarm treeHeight
    Concrete.rootNode _ _ hsignedRel)
  intro leftRoot rightRoot hroot
  obtain ⟨hrootEq, hrootRel⟩ := hroot
  rw [hsignedEq, hrootEq]
  exact relTriple_pure_pure ⟨rfl, hrootRel⟩

end Coupling

end XmssSecurity
