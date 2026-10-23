import XmssSecurity.Proof.GlobalBadEvent
import XmssSecurity.Proof.AdaptiveFreshTarget
import XmssSecurity.Proof.TopKeygenCache
import XmssSecurity.Proof.TopVerificationQueryPresence
import XmssSecurity.Proof.CappedSuffixEventProbability

/-!
# The top layer's bad events

A top bad event is either a guess, the forgery's top chain value at a coordinate the honest top
signature never reveals being the honest one (lane 1), or a hit, a query after key generation whose
output is the honest output key generation fixed at its address (lane 2).
-/

open OracleComp OracleSpec

namespace XmssSecurity

namespace CappedTop

/-- The honest input key generation used at an input's top address, or the input itself. The top
message digest's honest input is the selected trial of the top grinding. -/
noncomputable def keygenTopTargetInput (secretKey : SecretKey) (cache : QueryCache HashSpec)
    (input : HashInput) : HashInput :=
  if h : ∃ address : TopIndex × ChainIndex × ChainStep, ∃ value,
      input = Concrete.CacheView.topChainInput secretKey.parameter address.1 address.2.1
        address.2.2 value then
    let address := h.choose
    Concrete.CacheView.topChainInput secretKey.parameter address.1 address.2.1 address.2.2
      (Wots.walk (Concrete.CacheView.topChainStep cache secretKey.parameter address.1 address.2.1)
        0 address.2.2.val (secretKey.topChainStart address.1 address.2.1))
  else if h : ∃ key endpoints,
      input = Concrete.CacheView.topLeafInput secretKey.parameter key endpoints then
    Concrete.CacheView.topLeafInput secretKey.parameter h.choose
      (Concrete.CacheReplay.topOneTimePublicKey cache secretKey.parameter secretKey.topChainStart
        h.choose)
  else if h : ∃ address : MerkleLevel × TopNode, ∃ left right,
      input = Concrete.CacheView.topMerkleInput secretKey.parameter address.1 address.2 left right then
    let address := h.choose
    Concrete.CacheView.topMerkleInput secretKey.parameter address.1 address.2
      (Concrete.CacheReplay.topTreeNode cache secretKey.parameter secretKey.topChainStart
        address.1.val (Concrete.topChildNode address.2 false))
      (Concrete.CacheReplay.topTreeNode cache secretKey.parameter secretKey.topChainStart
        address.1.val (Concrete.topChildNode address.2 true))
  else if h : ∃ key payload,
      input = Concrete.CacheView.topEncodingInput secretKey.parameter key payload then
    match secretKey.topSigned h.choose with
    | some (randomness, _) =>
        Concrete.CacheView.topEncodingInput secretKey.parameter h.choose
          (Concrete.bottomRoot cache secretKey h.choose, randomness)
    | none => input
  else input

theorem keygenTopTargetInput_bottom (secretKey : SecretKey) (cache : QueryCache HashSpec)
    (domain : HashDomain) (message : HashInput) (hdomain : domain.isTop = false) :
    keygenTopTargetInput secretKey cache (tweakableHashInput secretKey.parameter domain message) =
      tweakableHashInput secretKey.parameter domain message := by
  unfold keygenTopTargetInput
  split_ifs with h1 h2 h3 h4
  · obtain ⟨_, _, h⟩ := h1
    cases domain_eq_of_tweakableHashInput_eq _ h; simp [HashDomain.isTop] at hdomain
  · obtain ⟨_, _, h⟩ := h2
    cases domain_eq_of_tweakableHashInput_eq _ h; simp [HashDomain.isTop] at hdomain
  · obtain ⟨_, _, _, h⟩ := h3
    cases domain_eq_of_tweakableHashInput_eq _ h; simp [HashDomain.isTop] at hdomain
  · obtain ⟨_, _, h⟩ := h4
    cases domain_eq_of_tweakableHashInput_eq _ h; simp [HashDomain.isTop] at hdomain
  · rfl

theorem top_of_keygenTopTargetInput_ne (secretKey : SecretKey) (cache : QueryCache HashSpec)
    (input : HashInput) (hne : keygenTopTargetInput secretKey cache input ≠ input) :
    ∃ domain message, domain.isTop = true ∧
      input = tweakableHashInput secretKey.parameter domain message := by
  unfold keygenTopTargetInput at hne
  split_ifs at hne with h1 h2 h3 h4
  · obtain ⟨address, value, h⟩ := h1
    exact ⟨_, _, rfl, h⟩
  · obtain ⟨key, endpoints, h⟩ := h2
    exact ⟨_, _, rfl, h⟩
  · obtain ⟨address, left, right, h⟩ := h3
    exact ⟨_, _, rfl, h⟩
  · obtain ⟨key, payload, h⟩ := h4
    exact ⟨_, _, rfl, h⟩
  · exact (hne rfl).elim

@[simp] theorem keygenTopTargetInput_encodingInput (secretKey : SecretKey)
    (cache : QueryCache HashSpec) (leafIndex : LeafIndex) (payload : Message × Randomness) :
    keygenTopTargetInput secretKey cache
        (Concrete.CacheView.encodingInput secretKey.parameter leafIndex payload) =
      Concrete.CacheView.encodingInput secretKey.parameter leafIndex payload :=
  keygenTopTargetInput_bottom _ _ _ _ rfl

@[simp] theorem keygenTopTargetInput_chainInput (secretKey : SecretKey)
    (cache : QueryCache HashSpec) (leafIndex : LeafIndex) (chain : ChainIndex) (step : ChainStep)
    (value : Digest) :
    keygenTopTargetInput secretKey cache
        (Concrete.CacheView.chainInput secretKey.parameter leafIndex chain step value) =
      Concrete.CacheView.chainInput secretKey.parameter leafIndex chain step value :=
  keygenTopTargetInput_bottom _ _ _ _ rfl

@[simp] theorem keygenTopTargetInput_leafInput (secretKey : SecretKey)
    (cache : QueryCache HashSpec) (leafIndex : LeafIndex) (endpoints : ChainIndex → Digest) :
    keygenTopTargetInput secretKey cache
        (Concrete.CacheView.leafInput secretKey.parameter leafIndex endpoints) =
      Concrete.CacheView.leafInput secretKey.parameter leafIndex endpoints :=
  keygenTopTargetInput_bottom _ _ _ _ rfl

@[simp] theorem keygenTopTargetInput_merkleInput (secretKey : SecretKey)
    (cache : QueryCache HashSpec) (level : MerkleLevel) (node : MerkleNode) (left right : Digest) :
    keygenTopTargetInput secretKey cache
        (Concrete.CacheView.merkleInput secretKey.parameter level node left right) =
      Concrete.CacheView.merkleInput secretKey.parameter level node left right :=
  keygenTopTargetInput_bottom _ _ _ _ rfl

theorem keygenTopTargetInput_topChainInput (secretKey : SecretKey) (cache : QueryCache HashSpec)
    (key : TopIndex) (chain : ChainIndex) (step : ChainStep) (value : Digest) :
    keygenTopTargetInput secretKey cache
        (Concrete.CacheView.topChainInput secretKey.parameter key chain step value) =
      Concrete.CacheView.topChainInput secretKey.parameter key chain step
        (Wots.walk (Concrete.CacheView.topChainStep cache secretKey.parameter key chain)
          0 step.val (secretKey.topChainStart key chain)) := by
  have hex : ∃ address : TopIndex × ChainIndex × ChainStep, ∃ value',
      Concrete.CacheView.topChainInput secretKey.parameter key chain step value =
        Concrete.CacheView.topChainInput secretKey.parameter address.1 address.2.1 address.2.2
          value' := ⟨(key, chain, step), value, rfl⟩
  unfold keygenTopTargetInput
  rw [dite_eq_left hex]
  obtain ⟨_, hinput⟩ := hex.choose_spec
  have hdomain := domain_eq_of_tweakableHashInput_eq secretKey.parameter hinput
  simp only [HashDomain.topChain.injEq] at hdomain
  obtain ⟨hkey, hchain, hstep⟩ := hdomain
  dsimp only
  rw [← hkey, ← hchain, ← hstep]

theorem keygenTopTargetInput_topLeafInput (secretKey : SecretKey) (cache : QueryCache HashSpec)
    (key : TopIndex) (endpoints : ChainIndex → Digest) :
    keygenTopTargetInput secretKey cache
        (Concrete.CacheView.topLeafInput secretKey.parameter key endpoints) =
      Concrete.CacheView.topLeafInput secretKey.parameter key
        (Concrete.CacheReplay.topOneTimePublicKey cache secretKey.parameter
          secretKey.topChainStart key) := by
  have hnot : ¬∃ address : TopIndex × ChainIndex × ChainStep, ∃ value,
      Concrete.CacheView.topLeafInput secretKey.parameter key endpoints =
        Concrete.CacheView.topChainInput secretKey.parameter address.1 address.2.1 address.2.2
          value := by
    rintro ⟨_, _, h⟩
    cases domain_eq_of_tweakableHashInput_eq _ h
  have hex : ∃ key' endpoints',
      Concrete.CacheView.topLeafInput secretKey.parameter key endpoints =
        Concrete.CacheView.topLeafInput secretKey.parameter key' endpoints' := ⟨key, endpoints, rfl⟩
  unfold keygenTopTargetInput
  rw [dite_eq_right hnot, dite_eq_left hex]
  obtain ⟨_, hinput⟩ := hex.choose_spec
  have hdomain := domain_eq_of_tweakableHashInput_eq secretKey.parameter hinput
  simp only [HashDomain.topLeaf.injEq] at hdomain
  rw [← hdomain]

theorem keygenTopTargetInput_topMerkleInput (secretKey : SecretKey) (cache : QueryCache HashSpec)
    (level : MerkleLevel) (node : TopNode) (left right : Digest) :
    keygenTopTargetInput secretKey cache
        (Concrete.CacheView.topMerkleInput secretKey.parameter level node left right) =
      Concrete.CacheView.topMerkleInput secretKey.parameter level node
        (Concrete.CacheReplay.topTreeNode cache secretKey.parameter secretKey.topChainStart
          level.val (Concrete.topChildNode node false))
        (Concrete.CacheReplay.topTreeNode cache secretKey.parameter secretKey.topChainStart
          level.val (Concrete.topChildNode node true)) := by
  have hnot1 : ¬∃ address : TopIndex × ChainIndex × ChainStep, ∃ value,
      Concrete.CacheView.topMerkleInput secretKey.parameter level node left right =
        Concrete.CacheView.topChainInput secretKey.parameter address.1 address.2.1 address.2.2
          value := by
    rintro ⟨_, _, h⟩
    cases domain_eq_of_tweakableHashInput_eq _ h
  have hnot2 : ¬∃ key endpoints,
      Concrete.CacheView.topMerkleInput secretKey.parameter level node left right =
        Concrete.CacheView.topLeafInput secretKey.parameter key endpoints := by
    rintro ⟨_, _, h⟩
    cases domain_eq_of_tweakableHashInput_eq _ h
  have hex : ∃ address : MerkleLevel × TopNode, ∃ left' right',
      Concrete.CacheView.topMerkleInput secretKey.parameter level node left right =
        Concrete.CacheView.topMerkleInput secretKey.parameter address.1 address.2 left' right' :=
    ⟨(level, node), left, right, rfl⟩
  unfold keygenTopTargetInput
  rw [dite_eq_right hnot1, dite_eq_right hnot2, dite_eq_left hex]
  obtain ⟨_, _, hinput⟩ := hex.choose_spec
  have hdomain := domain_eq_of_tweakableHashInput_eq secretKey.parameter hinput
  simp only [HashDomain.topMerkle.injEq] at hdomain
  obtain ⟨hlevel, hnode⟩ := hdomain
  dsimp only
  rw [← hlevel, ← hnode]

theorem keygenTopTargetInput_topEncodingInput (secretKey : SecretKey) (cache : QueryCache HashSpec)
    (key : TopIndex) (payload : Digest × Randomness) (randomness : Randomness)
    (encoding : Encoding) (hsigned : secretKey.topSigned key = some (randomness, encoding)) :
    keygenTopTargetInput secretKey cache
        (Concrete.CacheView.topEncodingInput secretKey.parameter key payload) =
      Concrete.CacheView.topEncodingInput secretKey.parameter key
        (Concrete.bottomRoot cache secretKey key, randomness) := by
  have hnot1 : ¬∃ address : TopIndex × ChainIndex × ChainStep, ∃ value,
      Concrete.CacheView.topEncodingInput secretKey.parameter key payload =
        Concrete.CacheView.topChainInput secretKey.parameter address.1 address.2.1 address.2.2
          value := by
    rintro ⟨_, _, h⟩
    cases domain_eq_of_tweakableHashInput_eq _ h
  have hnot2 : ¬∃ key' endpoints,
      Concrete.CacheView.topEncodingInput secretKey.parameter key payload =
        Concrete.CacheView.topLeafInput secretKey.parameter key' endpoints := by
    rintro ⟨_, _, h⟩
    cases domain_eq_of_tweakableHashInput_eq _ h
  have hnot3 : ¬∃ address : MerkleLevel × TopNode, ∃ left right,
      Concrete.CacheView.topEncodingInput secretKey.parameter key payload =
        Concrete.CacheView.topMerkleInput secretKey.parameter address.1 address.2 left right := by
    rintro ⟨_, _, _, h⟩
    cases domain_eq_of_tweakableHashInput_eq _ h
  have hex : ∃ key' payload',
      Concrete.CacheView.topEncodingInput secretKey.parameter key payload =
        Concrete.CacheView.topEncodingInput secretKey.parameter key' payload' :=
    ⟨key, payload, rfl⟩
  unfold keygenTopTargetInput
  rw [dite_eq_right hnot1, dite_eq_right hnot2, dite_eq_right hnot3, dite_eq_left hex]
  obtain ⟨_, hinput⟩ := hex.choose_spec
  have hdomain := domain_eq_of_tweakableHashInput_eq secretKey.parameter hinput
  simp only [HashDomain.topEncoding.injEq] at hdomain
  simp only [← hdomain, hsigned]


/-! ### Hits on a target key generation fixed -/

section Collisions

variable (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
  (hkeygen : keyResult ∈ support ((simulateQ romImpl Concrete.precomputedKeygen).run ∅))
  (finalCache : QueryCache HashSpec) (hle : keyResult.2 ≤ finalCache)

include hkeygen hle

set_option maxRecDepth 10000 in
/-- A cached top chain step that collides with the honest one at its address. -/
theorem topChainCollision_afterKeygen
    (key : TopIndex) (chain : ChainIndex) (step : ChainStep) (forgedValue : Digest)
    (forgedOutput : HashOutput)
    (hforgedCached : finalCache
      (Concrete.CacheView.topChainInput keyResult.1.2.parameter key chain step forgedValue) =
        some forgedOutput)
    (hne : forgedValue ≠ Wots.walk
      (Concrete.CacheView.topChainStep finalCache keyResult.1.2.parameter key chain)
      0 step.val (keyResult.1.2.topChainStart key chain))
    (hstepCollision : Concrete.CacheView.topChainStep finalCache keyResult.1.2.parameter key chain
        step.val forgedValue =
      Concrete.CacheView.topChainStep finalCache keyResult.1.2.parameter key chain step.val
        (Wots.walk (Concrete.CacheView.topChainStep finalCache keyResult.1.2.parameter key chain)
          0 step.val (keyResult.1.2.topChainStart key chain))) :
    Rom.AdaptiveFreshDigestCollisionWith keyResult.2 finalCache
      (keygenTopTargetInput keyResult.1.2 keyResult.2) := by
  have hstable := Concrete.precomputedKeygen_topChainWalk_eq_of_cache_le keyResult hkeygen
    finalCache hle key chain step.val (Nat.le_of_lt step.isLt)
  obtain ⟨honestOutput, hhonest⟩ :=
    Concrete.precomputedKeygen_cache_has_topChainInput keyResult hkeygen key chain step
  have hforgedInitial := Concrete.precomputedKeygen_cache_topChainInput_eq_none_of_ne keyResult
    hkeygen key chain step forgedValue (fun heq => hne (heq.trans hstable))
  refine ⟨Concrete.CacheView.topChainInput keyResult.1.2.parameter key chain step forgedValue,
    forgedOutput, honestOutput, hforgedCached, hforgedInitial, ?_, ?_⟩
  · rw [keygenTopTargetInput_topChainInput]
    exact hhonest
  · rw [keygenTopTargetInput_topChainInput, hstable]
    rwa [Concrete.CacheView.topChainStep_eq _ _ _ _ _ _ step.isLt,
      Concrete.CacheView.topChainStep_eq _ _ _ _ _ _ step.isLt] at hstepCollision

set_option maxRecDepth 10000 in
/-- A cached top leaf that collides with the honest one of its key. -/
theorem topLeafCollision_afterKeygen
    (key : TopIndex) (forgedEndpoints : ChainIndex → Digest) (forgedOutput : HashOutput)
    (hforgedCached : finalCache
      (Concrete.CacheView.topLeafInput keyResult.1.2.parameter key forgedEndpoints) =
        some forgedOutput)
    (hcollision : Wots.HasLeafCollision
      (Concrete.CacheView.topLeafHash finalCache keyResult.1.2.parameter key) forgedEndpoints
      (Concrete.CacheReplay.topOneTimePublicKey finalCache keyResult.1.2.parameter
        keyResult.1.2.topChainStart key)) :
    Rom.AdaptiveFreshDigestCollisionWith keyResult.2 finalCache
      (keygenTopTargetInput keyResult.1.2 keyResult.2) := by
  have hstable := Concrete.precomputedKeygen_topOneTimePublicKey_eq_of_cache_le keyResult hkeygen
    finalCache hle key
  obtain ⟨honestOutput, hhonest⟩ :=
    Concrete.precomputedKeygen_cache_has_topLeafInput keyResult hkeygen key
  have hforgedInitial := Concrete.precomputedKeygen_cache_topLeafInput_eq_none_of_ne keyResult
    hkeygen key forgedEndpoints (fun heq => hcollision.1 (heq.trans hstable))
  refine ⟨Concrete.CacheView.topLeafInput keyResult.1.2.parameter key forgedEndpoints,
    forgedOutput, honestOutput, hforgedCached, hforgedInitial, ?_, ?_⟩
  · rw [keygenTopTargetInput_topLeafInput]
    exact hhonest
  · rw [keygenTopTargetInput_topLeafInput, hstable]
    exact hcollision.2

/-- The children of a top node, ordered as the path's bit at its level orders them. -/
def topOrderedNodePair (key : TopIndex) (level : Nat) (current sibling : Digest) :
    Digest × Digest :=
  if key.val.testBit level then (sibling, current) else (current, sibling)

omit hkeygen hle in
theorem topNodeInput_eq_topMerkleInput_ordered (parameter : PublicParameter) (key : TopIndex)
    (level : MerkleLevel) (current sibling : Digest) :
    Concrete.CacheView.topNodeInput parameter key level current sibling =
      Concrete.CacheView.topMerkleInput parameter level (Concrete.topNodeIndex key level.val)
        (topOrderedNodePair key level.val current sibling).1
        (topOrderedNodePair key level.val current sibling).2 := by
  by_cases hbit : key.val.testBit level.val = true
  · simp [Concrete.CacheView.topNodeInput, Concrete.CacheView.topMerkleInput,
      Concrete.CacheView.topAuthenticationNodePayload, topOrderedNodePair, hbit]
  · have hbitFalse := Bool.eq_false_of_not_eq_true hbit
    simp [Concrete.CacheView.topNodeInput, Concrete.CacheView.topMerkleInput,
      Concrete.CacheView.topAuthenticationNodePayload, topOrderedNodePair, hbitFalse]

omit hkeygen hle in
theorem topOrderedNodePair_injective (key : TopIndex) (level : Nat) :
    Function.Injective fun pair : Digest × Digest =>
      topOrderedNodePair key level pair.1 pair.2 := by
  intro left right heq
  by_cases hbit : key.val.testBit level = true
  · simp [topOrderedNodePair, hbit] at heq
    exact Prod.ext heq.2 heq.1
  · have hbitFalse := Bool.eq_false_of_not_eq_true hbit
    simpa [topOrderedNodePair, hbitFalse] using heq

omit hkeygen hle in
theorem topNodeIndex_lt (key : TopIndex) (level : MerkleLevel) :
    (Concrete.topNodeIndex key level.val).val < 2 ^ (treeHeight - (level.val + 1)) := by
  have hsum : (treeHeight - (level.val + 1)) + (level.val + 1) = treeHeight := by
    have := level.isLt
    omega
  apply (Nat.div_lt_iff_lt_mul (by positivity : 0 < 2 ^ (level.val + 1))).2
  calc
    key.val < 2 ^ treeHeight := key.isLt
    _ = 2 ^ (treeHeight - (level.val + 1)) * 2 ^ (level.val + 1) := by
      rw [← Nat.pow_add, hsum]

omit hkeygen hle in
theorem topOrdered_honestNodePair_eq_children (cache : QueryCache HashSpec)
    (secretKey : SecretKey) (key : TopIndex) (level : MerkleLevel) :
    topOrderedNodePair key level.val
        (Concrete.CacheReplay.topTreeNode cache secretKey.parameter secretKey.topChainStart
          level.val (Concrete.CacheReplay.topPathNodeAt key level.val))
        (Concrete.CacheReplay.topTreeNode cache secretKey.parameter secretKey.topChainStart
          level.val (Concrete.topPathNode key level)) =
      (Concrete.CacheReplay.topTreeNode cache secretKey.parameter secretKey.topChainStart
          level.val (Concrete.topChildNode (Concrete.topNodeIndex key level.val) false),
        Concrete.CacheReplay.topTreeNode cache secretKey.parameter secretKey.topChainStart
          level.val (Concrete.topChildNode (Concrete.topNodeIndex key level.val) true)) := by
  rw [Concrete.CacheReplay.topNodeIndex_eq_topPathNodeAt_succ]
  have hchildren := Concrete.CacheReplay.topPathNode_children key level.val level.isLt
  by_cases hbit : key.val.testBit level.val = true
  · simp only [hbit, ↓reduceIte] at hchildren
    rcases hchildren with ⟨hleft, hright⟩
    simp [topOrderedNodePair, hbit, hleft, hright]
  · have hbitFalse := Bool.eq_false_of_not_eq_true hbit
    simp only [hbitFalse, Bool.false_eq_true, ↓reduceIte] at hchildren
    rcases hchildren with ⟨hleft, hright⟩
    simp [topOrderedNodePair, hbitFalse, hleft, hright]

set_option maxRecDepth 10000 in
/-- A cached top node on a path that collides with the honest one at its address. -/
theorem topMerkleCollision_afterKeygen
    (key : TopIndex) (level : MerkleLevel)
    (forgedCurrent forgedSibling honestCurrent honestSibling : Digest)
    (forgedOutput : HashOutput)
    (hforgedCached : finalCache
      (Concrete.CacheView.topNodeInput keyResult.1.2.parameter key level
        forgedCurrent forgedSibling) = some forgedOutput)
    (hne : (forgedCurrent, forgedSibling) ≠ (honestCurrent, honestSibling))
    (heq : Concrete.CacheView.topNodeHash finalCache keyResult.1.2.parameter key level.val
        forgedCurrent forgedSibling =
      Concrete.CacheView.topNodeHash finalCache keyResult.1.2.parameter key level.val
        honestCurrent honestSibling)
    (hhonest : topOrderedNodePair key level.val honestCurrent honestSibling =
      (Concrete.CacheReplay.topTreeNode finalCache keyResult.1.2.parameter
          keyResult.1.2.topChainStart level.val
          (Concrete.topChildNode (Concrete.topNodeIndex key level.val) false),
        Concrete.CacheReplay.topTreeNode finalCache keyResult.1.2.parameter
          keyResult.1.2.topChainStart level.val
          (Concrete.topChildNode (Concrete.topNodeIndex key level.val) true))) :
    Rom.AdaptiveFreshDigestCollisionWith keyResult.2 finalCache
      (keygenTopTargetInput keyResult.1.2 keyResult.2) := by
  let node := Concrete.topNodeIndex key level.val
  have hnode : node.val < 2 ^ (treeHeight - (level.val + 1)) := topNodeIndex_lt key level
  have hchild (right : Bool) :=
    Concrete.precomputedKeygen_topTreeNode_eq_of_cache_le keyResult hkeygen finalCache hle
      level.val level.isLt.le (Concrete.topChildNode node right)
      (Concrete.topChildNode_lt level.val node hnode level.isLt right)
  have hhonestInitial : topOrderedNodePair key level.val honestCurrent honestSibling =
      (Concrete.CacheReplay.topTreeNode keyResult.2 keyResult.1.2.parameter
          keyResult.1.2.topChainStart level.val (Concrete.topChildNode node false),
        Concrete.CacheReplay.topTreeNode keyResult.2 keyResult.1.2.parameter
          keyResult.1.2.topChainStart level.val (Concrete.topChildNode node true)) := by
    rw [hhonest, hchild false, hchild true]
  obtain ⟨honestOutput, hhonestCached⟩ :=
    Concrete.precomputedKeygen_cache_has_topMerkleInput keyResult hkeygen level node hnode
  have hforgedInitial := Concrete.precomputedKeygen_cache_topMerkleInput_eq_none_of_ne keyResult
    hkeygen level node hnode
    (topOrderedNodePair key level.val forgedCurrent forgedSibling).1
    (topOrderedNodePair key level.val forgedCurrent forgedSibling).2 (by
      rw [← hhonestInitial]
      intro hordered
      exact hne (topOrderedNodePair_injective key level.val hordered))
  rw [← topNodeInput_eq_topMerkleInput_ordered] at hforgedInitial
  refine ⟨Concrete.CacheView.topNodeInput keyResult.1.2.parameter key level forgedCurrent
    forgedSibling, forgedOutput, honestOutput, hforgedCached, hforgedInitial, ?_, ?_⟩
  · rw [topNodeInput_eq_topMerkleInput_ordered, keygenTopTargetInput_topMerkleInput]
    exact hhonestCached
  · rw [topNodeInput_eq_topMerkleInput_ordered, keygenTopTargetInput_topMerkleInput]
    unfold Concrete.CacheView.topNodeHash at heq
    rw [dite_eq_left level.isLt, dite_eq_left level.isLt] at heq
    rw [topNodeInput_eq_topMerkleInput_ordered, topNodeInput_eq_topMerkleInput_ordered,
      hhonestInitial] at heq
    exact heq

set_option maxRecDepth 10000 in
/-- A cached top message digest input, other than the honest selected trial, with its digest. -/
theorem topEncodingCollision_afterKeygen
    (key : TopIndex) (randomness : Randomness) (encoding : Encoding)
    (hsigned : keyResult.1.2.topSigned key = some (randomness, encoding))
    (forgedInput : Digest × Randomness) (forgedOutput : HashOutput) (forgedEncoding : Encoding)
    (hforgedCached : finalCache
      (Concrete.CacheView.topEncodingInput keyResult.1.2.parameter key forgedInput) =
        some forgedOutput)
    (hforgedDecode : TargetSum.decodeDigest
      (Concrete.CacheView.topEncodingHash finalCache keyResult.1.2.parameter key forgedInput) =
        some forgedEncoding)
    (hne : (Concrete.bottomRoot finalCache keyResult.1.2 key, randomness) ≠ forgedInput)
    (heq : Concrete.CacheView.topEncodingHash finalCache keyResult.1.2.parameter key
        (Concrete.bottomRoot finalCache keyResult.1.2 key, randomness) =
      Concrete.CacheView.topEncodingHash finalCache keyResult.1.2.parameter key forgedInput) :
    Rom.AdaptiveFreshDigestCollisionWith keyResult.2 finalCache
      (keygenTopTargetInput keyResult.1.2 keyResult.2) := by
  have hroot := Concrete.precomputedKeygen_bottomRoot_eq_of_cache_le keyResult hkeygen
    finalCache hle key
  obtain ⟨honestOutput, hhonest⟩ := Concrete.precomputedKeygen_cache_has_topEncodingInput
    keyResult hkeygen key randomness encoding hsigned
  have hforgedInitial : keyResult.2
      (Concrete.CacheView.topEncodingInput keyResult.1.2.parameter key forgedInput) = none := by
    cases hcached : keyResult.2
        (Concrete.CacheView.topEncodingInput keyResult.1.2.parameter key forgedInput) with
    | none => rfl
    | some output =>
        exfalso
        have hfinal := hle hcached
        rw [hforgedCached] at hfinal
        cases hfinal
        unfold Concrete.CacheView.topEncodingHash at hforgedDecode
        rw [Concrete.CacheView.digestAt_eq_of_cache_eq_some hforgedCached] at hforgedDecode
        obtain ⟨hselected, hforgedRoot⟩ := Concrete.precomputedKeygen_cache_topEncodingInput_decode
          keyResult hkeygen key forgedInput forgedOutput hcached forgedEncoding hforgedDecode
        rw [hsigned] at hselected
        simp only [Option.some.injEq, Prod.mk.injEq] at hselected
        apply hne
        rw [← hroot, ← hforgedRoot, hselected.1]
  refine ⟨Concrete.CacheView.topEncodingInput keyResult.1.2.parameter key forgedInput,
    forgedOutput, honestOutput, hforgedCached, hforgedInitial, ?_, ?_⟩
  · rw [keygenTopTargetInput_topEncodingInput _ _ _ _ randomness encoding hsigned]
    exact hhonest
  · rw [keygenTopTargetInput_topEncodingInput _ _ _ _ randomness encoding hsigned, hroot]
    exact heq.symm

end Collisions


/-! ### A forged chain value that is not the honest one at its digit -/

/-- The walk from a forged value at its digit first meets the honest walk at `offset` steps. -/
def ForgedStepCollision (step : ChainIndex → Nat → Digest → Digest) (encoding : Encoding)
    (forgedValue secret : ChainIndex → Digest) (chain : ChainIndex) (offset : Nat) : Prop :=
  Wots.walk (step chain) (encoding chain).val offset (forgedValue chain) ≠
      Wots.walk (step chain) 0 ((encoding chain).val + offset) (secret chain) ∧
    step chain ((encoding chain).val + offset)
        (Wots.walk (step chain) (encoding chain).val offset (forgedValue chain)) =
      step chain ((encoding chain).val + offset)
        (Wots.walk (step chain) 0 ((encoding chain).val + offset) (secret chain))

theorem forgedStepCollision_of_backward (step : ChainIndex → Nat → Digest → Digest)
    (signedEncoding forgedEncoding : Encoding) (forgedValue secret : ChainIndex → Digest)
    (chain : ChainIndex) (hlt : forgedEncoding chain < signedEncoding chain)
    (hcollision : Wots.HasStepCollision (step chain) (forgedEncoding chain).val
      ((signedEncoding chain).val - (forgedEncoding chain).val) (forgedValue chain)
      (Wots.signChain (step chain) (forgedEncoding chain) (secret chain))) :
    ∃ offset, offset < chainLength - 1 - (forgedEncoding chain).val ∧
      ForgedStepCollision step forgedEncoding forgedValue secret chain offset := by
  obtain ⟨offset, hoffset, hne, heq⟩ := hcollision
  rw [CappedSuffix.Wots.walk_signChain_eq_honest] at hne heq
  have hsigned := (signedEncoding chain).isLt
  have hltVal : (forgedEncoding chain).val < (signedEncoding chain).val := hlt
  exact ⟨offset, by simp only [chainLength] at hsigned ⊢; omega, hne, heq⟩

theorem forgedStepCollision_of_suffix (step : ChainIndex → Nat → Digest → Digest)
    (signedEncoding forgedEncoding : Encoding) (forgedValue secret : ChainIndex → Digest)
    (position : TargetSum.SuffixPosition signedEncoding)
    (hsuffix : Wots.IsSuffixCollisionAt step signedEncoding forgedEncoding
      (fun chain => Wots.signChain (step chain) (signedEncoding chain) (secret chain))
      forgedValue position) :
    ∃ chain offset, offset < chainLength - 1 - (forgedEncoding chain).val ∧
      ForgedStepCollision step forgedEncoding forgedValue secret chain offset := by
  obtain ⟨chain, suffixOffset⟩ := position
  dsimp only [Wots.IsSuffixCollisionAt] at hsuffix
  obtain ⟨hle, hne, heq⟩ := hsuffix
  have hleVal : (forgedEncoding chain).val ≤ (signedEncoding chain).val := hle
  have hsuffixLt := suffixOffset.isLt
  have hforgedWalk := Wots.walk_add (step chain) (forgedEncoding chain).val
    ((signedEncoding chain).val - (forgedEncoding chain).val) suffixOffset.val
    (forgedValue chain)
  rw [Nat.add_sub_cancel' hleVal] at hforgedWalk
  rw [CappedSuffix.Wots.walk_signChain_eq_honest, ← hforgedWalk] at hne heq
  have hposition : (forgedEncoding chain).val +
      ((signedEncoding chain).val - (forgedEncoding chain).val + suffixOffset.val) =
      (signedEncoding chain).val + suffixOffset.val := by omega
  refine ⟨chain, (signedEncoding chain).val - (forgedEncoding chain).val + suffixOffset.val,
    by omega, ?_, ?_⟩
  · rw [hposition]
    exact hne
  · rw [hposition]
    exact heq

section Collisions

variable (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
  (hkeygen : keyResult ∈ support ((simulateQ romImpl Concrete.precomputedKeygen).run ∅))
  (finalCache : QueryCache HashSpec) (hle : keyResult.2 ≤ finalCache)

include hkeygen hle

/-- A forged top chain value whose verification walk hits an honest step key generation cached. -/
theorem topForgedStep_afterKeygen (key : TopIndex) (encoding : Encoding)
    (forgedValue : ChainIndex → Digest)
    (hcached : ∀ chain offset (hoffset : offset < chainLength - 1 - (encoding chain).val),
      ∃ output, finalCache
        (Concrete.CacheView.topChainInput keyResult.1.2.parameter key chain
          ⟨(encoding chain).val + offset, by omega⟩
          (Wots.walk
            (Concrete.CacheView.topChainStep finalCache keyResult.1.2.parameter key chain)
            (encoding chain).val offset (forgedValue chain))) = some output)
    (chain : ChainIndex) (offset : Nat) (hoffset : offset < chainLength - 1 - (encoding chain).val)
    (hcollision : ForgedStepCollision
      (fun chain => Concrete.CacheView.topChainStep finalCache keyResult.1.2.parameter key chain)
      encoding forgedValue (keyResult.1.2.topChainStart key) chain offset) :
    Rom.AdaptiveFreshDigestCollisionWith keyResult.2 finalCache
      (keygenTopTargetInput keyResult.1.2 keyResult.2) := by
  obtain ⟨output, hforged⟩ := hcached chain offset hoffset
  exact topChainCollision_afterKeygen keyResult hkeygen finalCache hle key chain
    ⟨(encoding chain).val + offset, by omega⟩ _ output hforged hcollision.1 hcollision.2

/-- A path collision of a forged top path with the honest one of its key. -/
theorem topPathCollision_afterKeygen (key : TopIndex) (part : LayerSignature)
    (forgedLeaf : Digest) (level : MerkleLevel)
    (hcached : ∃ output, finalCache
      (Concrete.CacheView.topNodeInput keyResult.1.2.parameter key level
        (Merkle.ascend (Concrete.CacheView.topNodeHash finalCache keyResult.1.2.parameter key)
          (Concrete.layerPath part) 0 level.val forgedLeaf)
        (Concrete.layerPath part level.val)) = some output)
    (hevent : Merkle.IsXmssPathCollisionAt
      (Concrete.CacheView.topNodeHash finalCache keyResult.1.2.parameter key)
      (Concrete.layerPath part) (Concrete.honestTopPath finalCache keyResult.1.2 key) forgedLeaf
      (Concrete.CacheReplay.topLeafAt finalCache keyResult.1.2.parameter
        keyResult.1.2.topChainStart key) level) :
    Rom.AdaptiveFreshDigestCollisionWith keyResult.2 finalCache
      (keygenTopTargetInput keyResult.1.2 keyResult.2) := by
  obtain ⟨output, hforged⟩ := hcached
  obtain ⟨hne, heq⟩ := hevent
  have hcurrent := Concrete.CacheReplay.honestTopPath_ascends_to_topTreeNode finalCache
    keyResult.1.2 key level.val level.isLt.le
  have hsibling : Concrete.honestTopPath finalCache keyResult.1.2 key level.val =
      Concrete.CacheReplay.topTreeNode finalCache keyResult.1.2.parameter
        keyResult.1.2.topChainStart level.val (Concrete.topPathNode key level) := by
    simp [Concrete.honestTopPath, level.isLt]
  apply topMerkleCollision_afterKeygen keyResult hkeygen finalCache hle key level _ _ _ _ output
    hforged hne heq
  rw [hcurrent, hsibling]
  exact topOrdered_honestNodePair_eq_children finalCache keyResult.1.2 key level

end Collisions


/-- A top bad event that is not a guess, of a top signature whose check cached its queries. -/
theorem topBadEvent_afterKeygen
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
    (hkeygen : keyResult ∈ support ((simulateQ romImpl Concrete.precomputedKeygen).run ∅))
    (finalCache : QueryCache HashSpec) (hle : keyResult.2 ≤ finalCache)
    (secretKey : SecretKey) (hsecret : secretKey = keyResult.1.2)
    (key : TopIndex) (root : Digest) (part : LayerSignature) (forgedEncoding : Encoding)
    (hcached : Concrete.CacheReplay.TopQueriesCached finalCache secretKey.parameter key root part)
    (hdecode : TargetSum.decodeDigest
      (Concrete.CacheView.topEncodingHash finalCache secretKey.parameter key
        (root, part.randomness)) = some forgedEncoding)
    (event : BadEvent)
    (hevent : Concrete.TopBadEventOccurs finalCache secretKey key root part forgedEncoding event)
    (hnotRevealed : ∀ chain, event = .chain chain →
      part.chainValue chain ≠ Wots.signChain
        (Concrete.CacheView.topChainStep finalCache secretKey.parameter key chain)
        (forgedEncoding chain) (secretKey.topChainStart key chain)) :
    Rom.AdaptiveFreshDigestCollisionWith keyResult.2 finalCache
      (keygenTopTargetInput keyResult.1.2 keyResult.2) := by
  subst secretKey
  obtain ⟨encoding, hencodingDecode, hencodingCached, hchainCached, hleafCached, hnodeCached⟩ :=
    hcached
  have hencoding : encoding = forgedEncoding := by
    rw [hencodingDecode] at hdecode
    exact Option.some.inj hdecode
  subst encoding
  unfold Concrete.TopBadEventOccurs at hevent
  rcases hsigned : keyResult.1.2.topSigned key with _ | ⟨randomness, signedEncoding⟩
  · rw [hsigned] at hevent
    obtain ⟨_, hevent⟩ := hevent
    cases event with
    | encoding => exact hevent.elim
    | chain chain => exact (hnotRevealed chain rfl hevent).elim
    | suffixCollision slot =>
        obtain ⟨position, _, hsuffix⟩ := hevent
        obtain ⟨chain, offset, hoffset, hcollision⟩ := forgedStepCollision_of_suffix _ _ _ _ _
          position hsuffix
        exact topForgedStep_afterKeygen keyResult hkeygen finalCache hle key forgedEncoding
          part.chainValue hchainCached chain offset hoffset hcollision
    | leaf =>
        obtain ⟨output, hforged⟩ := hleafCached
        exact topLeafCollision_afterKeygen keyResult hkeygen finalCache hle key _ output hforged
          hevent
    | merkle level =>
        exact topPathCollision_afterKeygen keyResult hkeygen finalCache hle key part _ level
          (hnodeCached level) hevent
  · rw [hsigned] at hevent
    obtain ⟨_, hevent⟩ := hevent
    cases event with
    | encoding =>
        obtain ⟨output, hforged⟩ := hencodingCached
        exact topEncodingCollision_afterKeygen keyResult hkeygen finalCache hle key randomness
          signedEncoding hsigned (root, part.randomness) output forgedEncoding hforged hdecode
          hevent.1 hevent.2
    | chain chain =>
        rcases Wots.backwardWitness_eq_honest_or_hasStepCollision _ signedEncoding forgedEncoding
            _ part.chainValue (keyResult.1.2.topChainStart key) chain rfl hevent with
          hrevealed | hstep
        · exact (hnotRevealed chain rfl hrevealed).elim
        · obtain ⟨offset, hoffset, hcollision⟩ := forgedStepCollision_of_backward _ _ _ _ _ chain
            hevent.1 hstep
          exact topForgedStep_afterKeygen keyResult hkeygen finalCache hle key forgedEncoding
            part.chainValue hchainCached chain offset hoffset hcollision
    | suffixCollision slot =>
        obtain ⟨position, _, hsuffix⟩ := hevent
        obtain ⟨chain, offset, hoffset, hcollision⟩ := forgedStepCollision_of_suffix _ _ _ _ _
          position hsuffix
        exact topForgedStep_afterKeygen keyResult hkeygen finalCache hle key forgedEncoding
          part.chainValue hchainCached chain offset hoffset hcollision
    | leaf =>
        obtain ⟨output, hforged⟩ := hleafCached
        change Wots.HasLeafCollision _ _ (recoveredEndpoints _ signedEncoding
          (Concrete.honestTopValues finalCache keyResult.1.2 key signedEncoding)) at hevent
        rw [Concrete.CacheReplay.recover_honestTopValues] at hevent
        exact topLeafCollision_afterKeygen keyResult hkeygen finalCache hle key _ output hforged
          hevent
    | merkle level =>
        change Merkle.IsXmssPathCollisionAt _ _ _ _
          (Concrete.CacheView.topLeafHash finalCache keyResult.1.2.parameter key
            (recoveredEndpoints _ signedEncoding
              (Concrete.honestTopValues finalCache keyResult.1.2 key signedEncoding))) _ at hevent
        rw [Concrete.CacheReplay.recover_honestTopValues] at hevent
        exact topPathCollision_afterKeygen keyResult hkeygen finalCache hle key part _ level
          (hnodeCached level) hevent

end CappedTop

/-- A verified forgery's top check cached its queries, on the bottom root its bottom layer reaches. -/
theorem CappedTop.detailed_execution_topQueriesCached
    (adversary : Adversary)
    (execution : GameOutcome × QueryCache HashSpec)
    (hmem : execution ∈ support (detailedGameWithCache Concrete.scheme adversary))
    (hverified : execution.1.verified = true) (encoding : Encoding)
    (hdecode : TargetSum.decodeDigest
      (Concrete.CacheView.encodingHash execution.2 execution.1.secretKey.parameter
        execution.1.forgery.leafIndex
        (execution.1.forgery.message, execution.1.forgery.signature.randomness)) =
        some encoding) :
    Concrete.CacheReplay.TopQueriesCached execution.2 execution.1.secretKey.parameter
      (topKeyOf execution.1.forgery.leafIndex)
      (Merkle.ascend
        (Concrete.CacheView.nodeHash execution.2 execution.1.secretKey.parameter
          execution.1.forgery.leafIndex)
        (Concrete.signaturePath execution.1.forgery.signature) 0 treeHeight
        (Concrete.CacheView.leafHash execution.2 execution.1.secretKey.parameter
          execution.1.forgery.leafIndex
          (recoveredEndpoints
            (fun chain => Concrete.CacheView.chainStep execution.2
              execution.1.secretKey.parameter execution.1.forgery.leafIndex chain)
            encoding execution.1.forgery.signature.chainValue)))
      execution.1.forgery.signature.top := by
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
  obtain ⟨topCache, htop⟩ := Concrete.CacheReplay.verify_true_verifyTop_run publicKey
    forgery.leafIndex forgery.message forgery.signature encoding adversaryCache finalCache
    finalCache hverify hdecodePublic le_rfl
  have hcached := Concrete.CacheReplay.verifyTop_true_queries_cached publicKey _ _ _ topCache
    finalCache finalCache htop le_rfl
  rw [hparameter] at hcached
  exact hcached

namespace CappedTop

end CappedTop

/-- The forgery's top value at a chain is the honest one at its own digit. -/
noncomputable def OutcomeTopChainValueRevealed (cache : QueryCache HashSpec)
    (outcome : GameOutcome) (chain : ChainIndex) : Prop :=
  ∃ encoding forgedTopEncoding,
    TargetSum.decodeDigest
      (Concrete.CacheView.encodingHash cache outcome.secretKey.parameter outcome.forgery.leafIndex
        (outcome.forgery.message, outcome.forgery.signature.randomness)) = some encoding ∧
    TargetSum.decodeDigest
      (Concrete.CacheView.topEncodingHash cache outcome.secretKey.parameter
        (topKeyOf outcome.forgery.leafIndex)
        (Merkle.ascend
          (Concrete.CacheView.nodeHash cache outcome.secretKey.parameter outcome.forgery.leafIndex)
          (Concrete.signaturePath outcome.forgery.signature) 0 treeHeight
          (Concrete.CacheView.leafHash cache outcome.secretKey.parameter outcome.forgery.leafIndex
            (recoveredEndpoints
              (fun chain => Concrete.CacheView.chainStep cache outcome.secretKey.parameter
                outcome.forgery.leafIndex chain) encoding outcome.forgery.signature.chainValue)),
          outcome.forgery.signature.top.randomness)) = some forgedTopEncoding ∧
    outcome.forgery.signature.top.chainValue chain =
      Wots.signChain
        (Concrete.CacheView.topChainStep cache outcome.secretKey.parameter
          (topKeyOf outcome.forgery.leafIndex) chain)
        (forgedTopEncoding chain)
        (outcome.secretKey.topChainStart (topKeyOf outcome.forgery.leafIndex) chain)

/-- A winning top chain event whose forged value is a hidden honest one: a guess, charged to lane 1. -/
def WinningTopGuessOccurs (cache : QueryCache HashSpec) (outcome : GameOutcome) : Prop :=
  outcome.won = true ∧ ∃ chain,
    OutcomeTopBadEventOccurs cache outcome (.chain chain) ∧
      OutcomeTopChainValueRevealed cache outcome chain

/-- Every winning top bad event that is not a guess is a hit on a target key generation fixed. -/
theorem winningTopBadEvent_afterKeygen_orientation
    (adversary : Adversary)
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
    (hkeygen : keyResult ∈ support
      ((simulateQ romImpl Concrete.scheme.keygen).run ∅))
    (execution : GameOutcome × QueryCache HashSpec)
    (hafter : execution ∈ support
      ((simulateQ romImpl
        (detailedGameAfterKeygen Concrete.scheme adversary
          keyResult.1.1 keyResult.1.2)).run keyResult.2))
    (hevent : WinningGlobalBadEventOccurs execution.2 execution.1 .top)
    (hnotGuess : ¬WinningTopGuessOccurs execution.2 execution.1) :
    Rom.AdaptiveFreshDigestCollisionWith keyResult.2 execution.2
      (CappedTop.keygenTopTargetInput keyResult.1.2 keyResult.2) := by
  obtain ⟨hwon, event, hverified, encoding, forgedTopEncoding, hdecode, htopDecode, htop⟩ := hevent
  have hkeys := CappedLeaf.detailedGameAfterKeygen_keys_eq adversary keyResult.1.1 keyResult.1.2
    keyResult.2 execution hafter
  have hkeygen' : keyResult ∈ support
      ((simulateQ romImpl Concrete.precomputedKeygen).run ∅) := by
    simpa only [Concrete.scheme] using hkeygen
  have hle := xmssRom_cache_le
    (detailedGameAfterKeygen Concrete.scheme adversary keyResult.1.1 keyResult.1.2)
    keyResult.2 execution hafter
  have hgame := CappedLeaf.afterKeygen_execution_mem_detailedGame adversary keyResult hkeygen
    execution hafter
  have hcached := CappedTop.detailed_execution_topQueriesCached adversary execution hgame
    hverified encoding hdecode
  refine CappedTop.topBadEvent_afterKeygen keyResult hkeygen' execution.2 hle
    execution.1.secretKey hkeys.2 _ _ _ forgedTopEncoding hcached htopDecode event htop ?_
  rintro chain rfl hrevealed
  exact hnotGuess ⟨hwon, chain, ⟨hverified, encoding, forgedTopEncoding, hdecode, htopDecode, htop⟩,
    encoding, forgedTopEncoding, hdecode, htopDecode, hrevealed⟩

end XmssSecurity
