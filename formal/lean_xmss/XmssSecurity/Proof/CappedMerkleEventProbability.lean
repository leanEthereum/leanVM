import XmssSecurity.Proof.ExpectedAdaptiveFreshTarget
import XmssSecurity.Proof.CappedLeafEventProbability
import XmssSecurity.Proof.MerkleVerificationQueryPresence
import XmssSecurity.Proof.TopKeygenCache

open OracleComp OracleSpec ENNReal

namespace XmssSecurity.CappedMerkle


theorem detailed_execution_verified_merkle_query_cached_as
    (adversary : Adversary)
    (execution : GameOutcome × QueryCache HashSpec)
    (hmem : execution ∈ support (detailedGameWithCache Concrete.scheme adversary))
    (encoding : Encoding) (hverified : execution.1.verified = true)
    (hdecode : TargetSum.decodeDigest
      (Concrete.CacheView.encodingHash execution.2 execution.1.secretKey.parameter
        execution.1.forgery.leafIndex
        (execution.1.forgery.message, execution.1.forgery.signature.randomness)) =
        some encoding)
    (level : MerkleLevel) :
    ∃ output, execution.2
      (Concrete.CacheView.nodeInput execution.1.secretKey.parameter
        execution.1.forgery.leafIndex level
        (Merkle.ascend
          (Concrete.CacheView.nodeHash execution.2 execution.1.secretKey.parameter
            execution.1.forgery.leafIndex)
          (Concrete.signaturePath execution.1.forgery.signature) 0 level.val
          (Concrete.CacheView.leafHash execution.2 execution.1.secretKey.parameter
            execution.1.forgery.leafIndex
            (recoveredEndpoints
              (fun chain => Concrete.CacheView.chainStep execution.2
                execution.1.secretKey.parameter execution.1.forgery.leafIndex chain)
              encoding execution.1.forgery.signature.chainValue)))
        (Concrete.signaturePath execution.1.forgery.signature level.val)) = some output := by
  have hparameter :=
    (capped_detailed_execution_key_components_consistent adversary execution hmem).1
  unfold detailedGameWithCache detailedGameCore at hmem
  rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hmem
  obtain ⟨⟨⟨publicKey, secretKey⟩, keyCache⟩, _hkeygen, hrest⟩ := hmem
  unfold detailedGameAfterKeygen at hrest
  simp only at hrest
  rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hrest
  obtain ⟨⟨⟨forgery, signingLog⟩, adversaryCache⟩, _hadversary, hverifyRest⟩ := hrest
  rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hverifyRest
  obtain ⟨⟨verified, finalCache⟩, hverify, hfinal⟩ := hverifyRest
  simp only [simulateQ_pure, StateT.run_pure, support_pure,
    Set.mem_singleton_iff] at hfinal
  cases hfinal
  simp only at hparameter hverified hdecode ⊢
  subst verified
  have hroute :
      simulateQ romImpl
          (Concrete.scheme.verify publicKey forgery.leafIndex forgery.message forgery.signature) =
        simulateQ (randomOracle : QueryImpl HashSpec (StateT (QueryCache HashSpec) ProbComp))
          (Concrete.verify publicKey forgery.leafIndex forgery.message forgery.signature :
            OracleComp HashSpec Bool) := by
    simp only [Concrete.scheme, romImpl]
    change simulateQ (unifFwdImpl HashSpec +
      (randomOracle : QueryImpl HashSpec (StateT (QueryCache HashSpec) ProbComp)))
      (liftM (Concrete.verify publicKey forgery.leafIndex forgery.message forgery.signature :
        OracleComp HashSpec Bool)) = _
    exact QueryImpl.simulateQ_add_liftM_right (unifFwdImpl HashSpec)
      (randomOracle : QueryImpl HashSpec (StateT (QueryCache HashSpec) ProbComp))
      (Concrete.verify publicKey forgery.leafIndex forgery.message forgery.signature :
        OracleComp HashSpec Bool)
  rw [hroute] at hverify
  have hdecodePublic : TargetSum.decodeDigest
      (Concrete.CacheView.encodingHash finalCache publicKey.parameter forgery.leafIndex
        (forgery.message, forgery.signature.randomness)) = some encoding := by
    rw [hparameter]
    exact hdecode
  rw [← hparameter]
  exact Concrete.CacheReplay.verify_true_merkle_query_cached_as_in_largerCache publicKey
    forgery.leafIndex forgery.message forgery.signature encoding level adversaryCache finalCache
    finalCache hverify hdecodePublic le_rfl

def orderedNodePair (leafIndex : LeafIndex) (level : Nat) (current sibling : Digest) : Digest × Digest :=
  if leafIndex.val.testBit level then (sibling, current) else (current, sibling)

@[simp]
theorem nodeInput_eq_merkleInput_ordered (parameter : PublicParameter) (leafIndex : LeafIndex)
    (level : MerkleLevel) (current sibling : Digest) :
    Concrete.CacheView.nodeInput parameter leafIndex level current sibling =
      Concrete.CacheView.merkleInput parameter level
        (Concrete.CacheView.nodeIndex leafIndex level.val)
        (orderedNodePair leafIndex level.val current sibling).1
        (orderedNodePair leafIndex level.val current sibling).2 := by
  by_cases hbit : leafIndex.val.testBit level.val = true
  · simp [Concrete.CacheView.nodeInput, Concrete.CacheView.merkleInput,
      Concrete.CacheView.authenticationNodePayload, orderedNodePair, hbit]
  · have hbitFalse := Bool.eq_false_of_not_eq_true hbit
    simp [Concrete.CacheView.nodeInput, Concrete.CacheView.merkleInput,
      Concrete.CacheView.authenticationNodePayload, orderedNodePair, hbitFalse]

theorem orderedNodePair_injective (leafIndex : LeafIndex) (level : Nat) :
    Function.Injective fun pair : Digest × Digest =>
      orderedNodePair leafIndex level pair.1 pair.2 := by
  intro left right heq
  by_cases hbit : leafIndex.val.testBit level = true
  · simp [orderedNodePair, hbit] at heq
    exact Prod.ext heq.2 heq.1
  · have hbitFalse := Bool.eq_false_of_not_eq_true hbit
    simpa [orderedNodePair, hbitFalse] using heq

theorem nodeIndex_valid_at_level (leafIndex : LeafIndex) (level : MerkleLevel) :
    (Concrete.CacheView.nodeIndex leafIndex level.val).val <
      2 ^ (2 * treeHeight - (level.val + 1)) := by
  have hsum : (2 * treeHeight - (level.val + 1)) + (level.val + 1) = 2 * treeHeight := by
    have := level.isLt
    omega
  apply (Nat.div_lt_iff_lt_mul (by positivity : 0 < 2 ^ (level.val + 1))).2
  calc
    leafIndex.val < 2 ^ (2 * treeHeight) := leafIndex.isLt
    _ = 2 ^ (2 * treeHeight - (level.val + 1)) * 2 ^ (level.val + 1) := by
      rw [← Nat.pow_add, hsum]

noncomputable def keygenMerkleTargetInput (secretKey : SecretKey)
    (cache : QueryCache HashSpec) (input : HashInput) : HashInput :=
  if h : ∃ address : MerkleLevel × MerkleNode, ∃ left right,
      input = Concrete.CacheView.merkleInput secretKey.parameter address.1 address.2
        left right then
    let address := h.choose
    Concrete.CacheView.merkleInput secretKey.parameter address.1 address.2
      (Concrete.CacheReplay.treeNode cache secretKey.parameter secretKey.chainStart
        address.1.val (Concrete.childNode address.2 false))
      (Concrete.CacheReplay.treeNode cache secretKey.parameter secretKey.chainStart
        address.1.val (Concrete.childNode address.2 true))
  else input

@[simp]
theorem keygenMerkleTargetInput_merkleInput (secretKey : SecretKey)
    (cache : QueryCache HashSpec) (level : MerkleLevel) (node : MerkleNode)
    (left right : Digest) :
    keygenMerkleTargetInput secretKey cache
      (Concrete.CacheView.merkleInput secretKey.parameter level node left right) =
      Concrete.CacheView.merkleInput secretKey.parameter level node
        (Concrete.CacheReplay.treeNode cache secretKey.parameter secretKey.chainStart
          level.val (Concrete.childNode node false))
        (Concrete.CacheReplay.treeNode cache secretKey.parameter secretKey.chainStart
          level.val (Concrete.childNode node true)) := by
  unfold keygenMerkleTargetInput
  split
  · rename_i h
    obtain ⟨chosenLeft, chosenRight, hinput⟩ := h.choose_spec
    have hdomain := domain_eq_of_tweakableHashInput_eq secretKey.parameter
      (hinput.trans rfl)
    simp only [HashDomain.merkle.injEq] at hdomain
    rcases hdomain with ⟨hlevel, hnode⟩
    dsimp only
    rw [← hlevel, ← hnode]
  · rename_i h
    exfalso
    exact h ⟨(level, node), left, right, rfl⟩

attribute [irreducible] keygenMerkleTargetInput

theorem ordered_honestNodePair_eq_children
    (cache : QueryCache HashSpec) (secretKey : SecretKey) (leafIndex : LeafIndex)
    (level : MerkleLevel) :
    orderedNodePair leafIndex level.val
        (Concrete.CacheReplay.treeNode cache secretKey.parameter secretKey.chainStart
          level.val (Concrete.CacheReplay.pathNode leafIndex level.val))
        (Concrete.CacheReplay.treeNode cache secretKey.parameter secretKey.chainStart
          level.val (Concrete.authenticationPathNode leafIndex level)) =
      (Concrete.CacheReplay.treeNode cache secretKey.parameter secretKey.chainStart
          level.val
          (Concrete.childNode (Concrete.CacheView.nodeIndex leafIndex level.val) false),
        Concrete.CacheReplay.treeNode cache secretKey.parameter secretKey.chainStart
          level.val
          (Concrete.childNode (Concrete.CacheView.nodeIndex leafIndex level.val) true)) := by
  rw [Concrete.CacheReplay.nodeIndex_eq_pathNode_succ]
  have hchildren := Concrete.CacheReplay.pathNode_children leafIndex level.val level.isLt
  by_cases hbit : leafIndex.val.testBit level.val = true
  · simp only [hbit, ↓reduceIte] at hchildren
    rcases hchildren with ⟨hleft, hright⟩
    simp [orderedNodePair, hbit, hleft, hright]
  · have hbitFalse := Bool.eq_false_of_not_eq_true hbit
    simp only [hbitFalse, Bool.false_eq_true, ↓reduceIte] at hchildren
    rcases hchildren with ⟨hleft, hright⟩
    simp [orderedNodePair, hbitFalse, hleft, hright]

theorem adaptiveFreshDigestCollisionWith_of_merkleCollision
    (secretKey : SecretKey) (initialCache finalCache : QueryCache HashSpec)
    (leafIndex : LeafIndex) (level : MerkleLevel)
    (forgedCurrent forgedSibling honestCurrent honestSibling : Digest)
    (forgedOutput honestOutput : HashOutput)
    (hforgedFinal : finalCache
      (Concrete.CacheView.nodeInput secretKey.parameter leafIndex level
        forgedCurrent forgedSibling) = some forgedOutput)
    (hforgedInitial : initialCache
      (Concrete.CacheView.nodeInput secretKey.parameter leafIndex level
        forgedCurrent forgedSibling) = none)
    (hhonestInitial : initialCache
      (Concrete.CacheView.nodeInput secretKey.parameter leafIndex level
        honestCurrent honestSibling) = some honestOutput)
    (hcollision : Concrete.CacheView.digestAt finalCache
        (Concrete.CacheView.nodeInput secretKey.parameter leafIndex level
          forgedCurrent forgedSibling) =
      Concrete.CacheView.digestAt finalCache
        (Concrete.CacheView.nodeInput secretKey.parameter leafIndex level
          honestCurrent honestSibling))
    (hhonest : orderedNodePair leafIndex level.val honestCurrent honestSibling =
      (Concrete.CacheReplay.treeNode initialCache secretKey.parameter secretKey.chainStart
          level.val
          (Concrete.childNode (Concrete.CacheView.nodeIndex leafIndex level.val) false),
        Concrete.CacheReplay.treeNode initialCache secretKey.parameter secretKey.chainStart
          level.val
          (Concrete.childNode (Concrete.CacheView.nodeIndex leafIndex level.val) true))) :
    Rom.AdaptiveFreshDigestCollisionWith initialCache finalCache
      (keygenMerkleTargetInput secretKey initialCache) := by
  let forgedInput := Concrete.CacheView.nodeInput secretKey.parameter leafIndex level
    forgedCurrent forgedSibling
  have hhonestLeft := congrArg Prod.fst hhonest
  have hhonestRight := congrArg Prod.snd hhonest
  simp only at hhonestLeft hhonestRight
  have hhonestInitial' := hhonestInitial
  rw [nodeInput_eq_merkleInput_ordered] at hhonestInitial'
  have hcollision' := hcollision
  rw [nodeInput_eq_merkleInput_ordered, nodeInput_eq_merkleInput_ordered] at hcollision'
  refine ⟨forgedInput, forgedOutput, honestOutput, hforgedFinal, hforgedInitial, ?_, ?_⟩
  · rw [show forgedInput = Concrete.CacheView.nodeInput secretKey.parameter leafIndex level
      forgedCurrent forgedSibling by rfl]
    rw [nodeInput_eq_merkleInput_ordered, keygenMerkleTargetInput_merkleInput,
      ← hhonestLeft, ← hhonestRight]
    exact hhonestInitial'
  · rw [show forgedInput = Concrete.CacheView.nodeInput secretKey.parameter leafIndex level
      forgedCurrent forgedSibling by rfl]
    rw [nodeInput_eq_merkleInput_ordered, keygenMerkleTargetInput_merkleInput,
      ← hhonestLeft, ← hhonestRight]
    exact hcollision'

theorem merkleCollision_afterKeygen_orientation
    (adversary : Adversary)
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
    (hkeygen : keyResult ∈ support
      ((simulateQ romImpl Concrete.scheme.keygen).run ∅))
    (execution : GameOutcome × QueryCache HashSpec)
    (hafter : execution ∈ support
      ((simulateQ romImpl
        (detailedGameAfterKeygen Concrete.scheme adversary keyResult.1.1 keyResult.1.2)).run
          keyResult.2))
    (secretKey : SecretKey) (hsecret : secretKey = keyResult.1.2)
    (leafIndex : LeafIndex) (level : MerkleLevel)
    (forgedCurrent forgedSibling honestCurrent honestSibling : Digest)
    (forgedOutput : HashOutput)
    (hforgedCached : execution.2
      (Concrete.CacheView.nodeInput secretKey.parameter leafIndex level
        forgedCurrent forgedSibling) = some forgedOutput)
    (hne : (forgedCurrent, forgedSibling) ≠ (honestCurrent, honestSibling))
    (heq : Concrete.CacheView.nodeHash execution.2 secretKey.parameter leafIndex level.val
        forgedCurrent forgedSibling =
      Concrete.CacheView.nodeHash execution.2 secretKey.parameter leafIndex level.val
        honestCurrent honestSibling)
    (hhonest : orderedNodePair leafIndex level.val honestCurrent honestSibling =
      (Concrete.CacheReplay.treeNode execution.2 secretKey.parameter secretKey.chainStart
          level.val
          (Concrete.childNode (Concrete.CacheView.nodeIndex leafIndex level.val) false),
        Concrete.CacheReplay.treeNode execution.2 secretKey.parameter secretKey.chainStart
          level.val
          (Concrete.childNode (Concrete.CacheView.nodeIndex leafIndex level.val) true))) :
    Rom.AdaptiveFreshDigestCollisionWith keyResult.2 execution.2
      (keygenMerkleTargetInput keyResult.1.2 keyResult.2) := by
  subst secretKey
  have hafterCacheLe := xmssRom_cache_le
    (detailedGameAfterKeygen Concrete.scheme adversary keyResult.1.1 keyResult.1.2)
    keyResult.2 execution hafter
  have hkeygen' : keyResult ∈ support
      ((simulateQ romImpl Concrete.precomputedKeygen).run ∅) := by
    simpa only [Concrete.scheme] using hkeygen
  let node := Concrete.CacheView.nodeIndex leafIndex level.val
  have horderedNe : orderedNodePair leafIndex level.val forgedCurrent forgedSibling ≠
      orderedNodePair leafIndex level.val honestCurrent honestSibling := by
    intro hordered
    exact hne (orderedNodePair_injective leafIndex level.val hordered)
  have hforgedInitial :=
    Concrete.precomputedKeygen_cache_forestMerkleInput_eq_none_of_ne_in_largerCache keyResult
      hkeygen' execution.2 hafterCacheLe level node (nodeIndex_valid_at_level leafIndex level)
      (orderedNodePair leafIndex level.val forgedCurrent forgedSibling).1
      (orderedNodePair leafIndex level.val forgedCurrent forgedSibling).2 (by
        rw [← hhonest]
        exact horderedNe)
  rw [← nodeInput_eq_merkleInput_ordered] at hforgedInitial
  obtain ⟨honestOutput, hhonestCached⟩ :=
    Concrete.precomputedKeygen_cache_has_forestMerkleInput_in_largerCache keyResult hkeygen'
      execution.2 hafterCacheLe level node (nodeIndex_valid_at_level leafIndex level)
  dsimp only [node] at hhonestCached
  have hhonestLeft := congrArg Prod.fst hhonest
  have hhonestRight := congrArg Prod.snd hhonest
  simp only at hhonestLeft hhonestRight
  rw [← hhonestLeft, ← hhonestRight, ← nodeInput_eq_merkleInput_ordered] at hhonestCached
  have hcollision := heq
  rw [Concrete.CacheView.nodeHash_eq _ _ _ _ _ _ level.isLt,
    Concrete.CacheView.nodeHash_eq _ _ _ _ _ _ level.isLt] at hcollision
  have hstable := Concrete.precomputedKeygen_forestMerkleChildren_eq_of_cache_le keyResult hkeygen'
    execution.2 hafterCacheLe level node (nodeIndex_valid_at_level leafIndex level)
  have hhonestInitial : orderedNodePair leafIndex level.val honestCurrent honestSibling =
      (Concrete.CacheReplay.treeNode keyResult.2 keyResult.1.2.parameter
          keyResult.1.2.chainStart level.val
          (Concrete.childNode (Concrete.CacheView.nodeIndex leafIndex level.val) false),
        Concrete.CacheReplay.treeNode keyResult.2 keyResult.1.2.parameter
          keyResult.1.2.chainStart level.val
          (Concrete.childNode (Concrete.CacheView.nodeIndex leafIndex level.val) true)) := by
    dsimp only [node] at hstable
    exact hhonest.trans hstable.symm
  exact adaptiveFreshDigestCollisionWith_of_merkleCollision keyResult.1.2 keyResult.2
    execution.2 leafIndex level forgedCurrent forgedSibling honestCurrent honestSibling
    forgedOutput honestOutput hforgedCached hforgedInitial hhonestCached hcollision
    hhonestInitial

theorem merkle_path_collision_afterKeygen_orientation
    (adversary : Adversary)
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
    (hkeygen : keyResult ∈ support
      ((simulateQ romImpl Concrete.scheme.keygen).run ∅))
    (execution : GameOutcome × QueryCache HashSpec)
    (hafter : execution ∈ support
      ((simulateQ romImpl
        (detailedGameAfterKeygen Concrete.scheme adversary keyResult.1.1 keyResult.1.2)).run
          keyResult.2))
    (hverified : execution.1.verified = true)
    (leafIndex : LeafIndex) (hleafIndex : leafIndex = execution.1.forgery.leafIndex)
    (forgedEncoding : Encoding)
    (hforgedDecode : TargetSum.decodeDigest
      (Concrete.CacheView.encodingHash execution.2 execution.1.secretKey.parameter
        execution.1.forgery.leafIndex
        (execution.1.forgery.message, execution.1.forgery.signature.randomness)) =
        some forgedEncoding)
    (honestPath : Nat → Digest) (honestLeaf : Digest) (level : MerkleLevel)
    (hevent : Merkle.IsXmssPathCollisionAt
      (Concrete.CacheView.nodeHash execution.2 execution.1.secretKey.parameter leafIndex)
      (Concrete.signaturePath execution.1.forgery.signature) honestPath
      (Concrete.CacheView.leafHash execution.2 execution.1.secretKey.parameter leafIndex
        (recoveredEndpoints
          (fun chain => Concrete.CacheView.chainStep execution.2
            execution.1.secretKey.parameter leafIndex chain)
          forgedEncoding execution.1.forgery.signature.chainValue))
      honestLeaf level)
    (hhonestCurrent : Merkle.ascend
        (Concrete.CacheView.nodeHash execution.2 execution.1.secretKey.parameter leafIndex)
        honestPath 0 level.val honestLeaf =
      Concrete.CacheReplay.treeNode execution.2 execution.1.secretKey.parameter
        execution.1.secretKey.chainStart level.val
        (Concrete.CacheReplay.pathNode leafIndex level.val))
    (hhonestSibling : honestPath level.val =
      Concrete.CacheReplay.treeNode execution.2 execution.1.secretKey.parameter
        execution.1.secretKey.chainStart level.val
        (Concrete.authenticationPathNode leafIndex level)) :
    Rom.AdaptiveFreshDigestCollisionWith keyResult.2 execution.2
      (keygenMerkleTargetInput keyResult.1.2 keyResult.2) := by
  subst leafIndex
  let forgedCurrent := Merkle.ascend
    (Concrete.CacheView.nodeHash execution.2 execution.1.secretKey.parameter
      execution.1.forgery.leafIndex)
    (Concrete.signaturePath execution.1.forgery.signature) 0 level.val
    (Concrete.CacheView.leafHash execution.2 execution.1.secretKey.parameter
      execution.1.forgery.leafIndex
      (recoveredEndpoints
        (fun chain => Concrete.CacheView.chainStep execution.2
          execution.1.secretKey.parameter execution.1.forgery.leafIndex chain)
        forgedEncoding execution.1.forgery.signature.chainValue))
  let forgedSibling :=
    Concrete.signaturePath execution.1.forgery.signature level.val
  let honestCurrent := Merkle.ascend
    (Concrete.CacheView.nodeHash execution.2 execution.1.secretKey.parameter
      execution.1.forgery.leafIndex) honestPath 0 level.val honestLeaf
  let honestSibling := honestPath level.val
  change (forgedCurrent, forgedSibling) ≠ (honestCurrent, honestSibling) ∧
    Concrete.CacheView.nodeHash execution.2 execution.1.secretKey.parameter
        execution.1.forgery.leafIndex level.val forgedCurrent forgedSibling =
      Concrete.CacheView.nodeHash execution.2 execution.1.secretKey.parameter
        execution.1.forgery.leafIndex level.val honestCurrent honestSibling at hevent
  obtain ⟨hne, heq⟩ := hevent
  have hhonest : orderedNodePair execution.1.forgery.leafIndex level.val
      honestCurrent honestSibling =
      (Concrete.CacheReplay.treeNode execution.2
          execution.1.secretKey.parameter execution.1.secretKey.chainStart level.val
          (Concrete.childNode
            (Concrete.CacheView.nodeIndex execution.1.forgery.leafIndex level.val) false),
        Concrete.CacheReplay.treeNode execution.2
          execution.1.secretKey.parameter execution.1.secretKey.chainStart level.val
          (Concrete.childNode
            (Concrete.CacheView.nodeIndex execution.1.forgery.leafIndex level.val) true)) := by
    rw [show honestCurrent = Concrete.CacheReplay.treeNode execution.2
        execution.1.secretKey.parameter execution.1.secretKey.chainStart level.val
        (Concrete.CacheReplay.pathNode execution.1.forgery.leafIndex level.val) by
          exact hhonestCurrent,
      show honestSibling = Concrete.CacheReplay.treeNode execution.2
        execution.1.secretKey.parameter execution.1.secretKey.chainStart level.val
        (Concrete.authenticationPathNode execution.1.forgery.leafIndex level) by
          exact hhonestSibling]
    exact ordered_honestNodePair_eq_children execution.2 execution.1.secretKey
      execution.1.forgery.leafIndex level
  have hgame := CappedLeaf.afterKeygen_execution_mem_detailedGame adversary
    keyResult hkeygen execution hafter
  obtain ⟨forgedOutput, hforgedCached⟩ :=
    detailed_execution_verified_merkle_query_cached_as adversary execution hgame
      forgedEncoding hverified hforgedDecode level
  change execution.2
      (Concrete.CacheView.nodeInput execution.1.secretKey.parameter
        execution.1.forgery.leafIndex level forgedCurrent forgedSibling) =
      some forgedOutput at hforgedCached
  have hkeys := CappedLeaf.detailedGameAfterKeygen_keys_eq adversary keyResult.1.1
    keyResult.1.2 keyResult.2 execution hafter
  exact merkleCollision_afterKeygen_orientation adversary keyResult hkeygen execution
    hafter execution.1.secretKey hkeys.2 execution.1.forgery.leafIndex level
    forgedCurrent forgedSibling honestCurrent honestSibling forgedOutput
    hforgedCached hne heq hhonest

theorem same_merkle_witness_afterKeygen_orientation
    (adversary : Adversary)
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
    (hkeygen : keyResult ∈ support
      ((simulateQ romImpl Concrete.scheme.keygen).run ∅))
    (execution : GameOutcome × QueryCache HashSpec)
    (hafter : execution ∈ support
      ((simulateQ romImpl
        (detailedGameAfterKeygen Concrete.scheme adversary keyResult.1.1 keyResult.1.2)).run
          keyResult.2))
    (hverified : execution.1.verified = true)
    (request : SignRequest) (signature : Signature)
    (signedEncoding forgedEncoding : Encoding)
    (hsignedDecode : TargetSum.decodeDigest
      (Concrete.CacheView.encodingHash execution.2 execution.1.secretKey.parameter
        request.leafIndex (request.message, signature.randomness)) = some signedEncoding)
    (hforgedDecode : TargetSum.decodeDigest
      (Concrete.CacheView.encodingHash execution.2 execution.1.secretKey.parameter
        request.leafIndex
        (execution.1.forgery.message, execution.1.forgery.signature.randomness)) =
        some forgedEncoding)
    (hreturned : SigningTranscript.Returned execution.1.signingLog request signature)
    (hleafIndex : request.leafIndex = execution.1.forgery.leafIndex)
    (level : MerkleLevel)
    (hevent : Concrete.SameLeafIndexBadEventOccurs execution.2
      execution.1.secretKey.parameter request.leafIndex request.message
      execution.1.forgery.message signedEncoding forgedEncoding signature
      execution.1.forgery.signature
      (TargetSum.decodeDigest_eq_some_iff.mp hsignedDecode).2 (.merkle level)) :
    Rom.AdaptiveFreshDigestCollisionWith keyResult.2 execution.2
      (keygenMerkleTargetInput keyResult.1.2 keyResult.2) := by
  have hgame := CappedLeaf.afterKeygen_execution_mem_detailedGame adversary keyResult hkeygen execution hafter
  have hsignature := CappedLeaf.detailed_execution_returned_signature_eq adversary execution hgame
    request signature signedEncoding hsignedDecode hreturned
  have hdecodeLeafIndex := congrArg (fun leafIndex => TargetSum.decodeDigest
    (Concrete.CacheView.encodingHash execution.2 execution.1.secretKey.parameter leafIndex
      (execution.1.forgery.message, execution.1.forgery.signature.randomness))) hleafIndex
  have hforgedDecode' : TargetSum.decodeDigest
      (Concrete.CacheView.encodingHash execution.2 execution.1.secretKey.parameter
        execution.1.forgery.leafIndex
        (execution.1.forgery.message, execution.1.forgery.signature.randomness)) =
        some forgedEncoding := hdecodeLeafIndex.symm.trans hforgedDecode
  change Merkle.IsXmssPathCollisionAt
    (Concrete.CacheView.nodeHash execution.2 execution.1.secretKey.parameter request.leafIndex)
    (Concrete.signaturePath execution.1.forgery.signature)
    (Concrete.signaturePath signature)
    (Concrete.CacheView.leafHash execution.2 execution.1.secretKey.parameter request.leafIndex
      (recoveredEndpoints
        (fun chain => Concrete.CacheView.chainStep execution.2
          execution.1.secretKey.parameter request.leafIndex chain)
        forgedEncoding execution.1.forgery.signature.chainValue))
    (Concrete.CacheView.leafHash execution.2 execution.1.secretKey.parameter request.leafIndex
      (recoveredEndpoints
        (fun chain => Concrete.CacheView.chainStep execution.2
          execution.1.secretKey.parameter request.leafIndex chain)
        signedEncoding signature.chainValue)) level at hevent
  refine merkle_path_collision_afterKeygen_orientation adversary keyResult hkeygen
    execution hafter hverified request.leafIndex hleafIndex forgedEncoding hforgedDecode'
      (Concrete.signaturePath signature)
      (Concrete.CacheView.leafHash execution.2 execution.1.secretKey.parameter
        request.leafIndex
        (recoveredEndpoints
          (fun chain => Concrete.CacheView.chainStep execution.2
            execution.1.secretKey.parameter request.leafIndex chain)
          signedEncoding signature.chainValue)) level hevent ?_ ?_
  ·
    rw [hsignature,
      Concrete.CacheReplay.leafHash_recovered_signWithEncoding]
    exact Concrete.CacheReplay.authenticationPath_ascends_to_treeNode execution.2
      execution.1.secretKey request.leafIndex signature.randomness signedEncoding level.val
      level.isLt.le
  · rw [hsignature]
    simp [Concrete.signaturePath, Concrete.CacheReplay.signWithEncoding,
      Concrete.CacheReplay.authenticationPath, level.isLt]

theorem fresh_merkle_witness_afterKeygen_orientation
    (adversary : Adversary)
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
    (hkeygen : keyResult ∈ support
      ((simulateQ romImpl Concrete.scheme.keygen).run ∅))
    (execution : GameOutcome × QueryCache HashSpec)
    (hafter : execution ∈ support
      ((simulateQ romImpl
        (detailedGameAfterKeygen Concrete.scheme adversary keyResult.1.1 keyResult.1.2)).run
          keyResult.2))
    (hverified : execution.1.verified = true)
    (forgedEncoding : Encoding)
    (hforgedDecode : TargetSum.decodeDigest
      (Concrete.CacheView.encodingHash execution.2 execution.1.secretKey.parameter
        execution.1.forgery.leafIndex
        (execution.1.forgery.message, execution.1.forgery.signature.randomness)) =
        some forgedEncoding)
    (level : MerkleLevel)
    (hevent : Concrete.FreshLeafIndexBadEventOccurs execution.2
      execution.1.secretKey.parameter execution.1.forgery.leafIndex forgedEncoding
      execution.1.forgery.signature
      (execution.1.secretKey.chainStart execution.1.forgery.leafIndex)
      (Concrete.signaturePath
        (Concrete.CacheReplay.signWithEncoding execution.2 execution.1.secretKey
          execution.1.forgery.leafIndex execution.1.forgery.signature.randomness forgedEncoding))
      (TargetSum.decodeDigest_eq_some_iff.mp hforgedDecode).2 (.merkle level)) :
    Rom.AdaptiveFreshDigestCollisionWith keyResult.2 execution.2
      (keygenMerkleTargetInput keyResult.1.2 keyResult.2) := by
  let honestSignature := Concrete.CacheReplay.signWithEncoding execution.2
    execution.1.secretKey execution.1.forgery.leafIndex
    execution.1.forgery.signature.randomness forgedEncoding
  change Merkle.IsXmssPathCollisionAt
    (Concrete.CacheView.nodeHash execution.2 execution.1.secretKey.parameter
      execution.1.forgery.leafIndex)
    (Concrete.signaturePath execution.1.forgery.signature)
    (Concrete.signaturePath honestSignature)
    (Concrete.CacheView.leafHash execution.2 execution.1.secretKey.parameter
      execution.1.forgery.leafIndex
      (recoveredEndpoints
        (fun chain => Concrete.CacheView.chainStep execution.2
          execution.1.secretKey.parameter execution.1.forgery.leafIndex chain)
        forgedEncoding execution.1.forgery.signature.chainValue))
    (Concrete.CacheView.leafHash execution.2 execution.1.secretKey.parameter
      execution.1.forgery.leafIndex
      (fun chain => Wots.publicChain
        (Concrete.CacheView.chainStep execution.2 execution.1.secretKey.parameter
          execution.1.forgery.leafIndex chain)
        (execution.1.secretKey.chainStart execution.1.forgery.leafIndex chain))) level at hevent
  refine merkle_path_collision_afterKeygen_orientation adversary keyResult hkeygen
    execution hafter hverified execution.1.forgery.leafIndex rfl forgedEncoding
      hforgedDecode (Concrete.signaturePath honestSignature)
      (Concrete.CacheView.leafHash execution.2 execution.1.secretKey.parameter
        execution.1.forgery.leafIndex
        (fun chain => Wots.publicChain
          (Concrete.CacheView.chainStep execution.2 execution.1.secretKey.parameter
            execution.1.forgery.leafIndex chain)
          (execution.1.secretKey.chainStart execution.1.forgery.leafIndex chain))) level
      hevent ?_ ?_
  ·
    change Merkle.ascend
      (Concrete.CacheView.nodeHash execution.2 execution.1.secretKey.parameter
        execution.1.forgery.leafIndex)
      (Concrete.signaturePath honestSignature) 0 level.val
      (Concrete.CacheReplay.leafAt execution.2 execution.1.secretKey.parameter
        execution.1.secretKey.chainStart execution.1.forgery.leafIndex) = _
    exact Concrete.CacheReplay.authenticationPath_ascends_to_treeNode execution.2
      execution.1.secretKey execution.1.forgery.leafIndex
      execution.1.forgery.signature.randomness forgedEncoding level.val level.isLt.le
  · simp [honestSignature, Concrete.signaturePath,
      Concrete.CacheReplay.signWithEncoding, Concrete.CacheReplay.authenticationPath,
      level.isLt]

theorem merkle_event_afterKeygen_orientation
    (adversary : Adversary)
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
    (hkeygen : keyResult ∈ support
      ((simulateQ romImpl Concrete.scheme.keygen).run ∅))
    (execution : GameOutcome × QueryCache HashSpec)
    (hafter : execution ∈ support
      ((simulateQ romImpl
        (detailedGameAfterKeygen Concrete.scheme adversary keyResult.1.1 keyResult.1.2)).run
          keyResult.2))
    (level : MerkleLevel)
    (hevent : OutcomeBadEventOccurs execution.2 execution.1 (.merkle level)) :
    Rom.AdaptiveFreshDigestCollisionWith keyResult.2 execution.2
      (keygenMerkleTargetInput keyResult.1.2 keyResult.2) := by
  rcases hevent.2 with hsame | hfresh
  · obtain ⟨request, signature, signedEncoding, forgedEncoding, hsignedDecode,
      hforgedDecode, hreturned, hleafIndex, hmerkle⟩ := hsame
    exact same_merkle_witness_afterKeygen_orientation adversary keyResult hkeygen execution
      hafter hevent.1 request signature signedEncoding forgedEncoding hsignedDecode
      hforgedDecode hreturned hleafIndex level hmerkle
  · obtain ⟨forgedEncoding, hforgedValid, _hunsigned, hforgedDecode, hmerkle⟩ := hfresh
    exact fresh_merkle_witness_afterKeygen_orientation adversary keyResult hkeygen execution
      hafter hevent.1 forgedEncoding hforgedDecode level hmerkle

end XmssSecurity.CappedMerkle
