module

public import XmssSecurity.Proof.IdealStatement
public import XmssSecurity.Proof.Wots

@[expose] public section

/-!
Proof-side mirrors of the sealed statement definitions, and rewrite lemmas restating them so proofs can unfold them without unsealing.

The statement stores the precomputed secret key as `evalWithAnswerFn (replayHash cache)` runs of its own oracle algorithms. `Wots.walk`, `CacheView`, and `CacheReplay` are the equivalent first-order forms of those replays that the proof works with; `Proof.CacheReplayEval` bridges the two.
-/

open OracleComp OracleSpec

namespace XmssSecurity

@[simp]
theorem truncateHash_zero : truncateHash 0 = 0 := by decide

namespace Concrete

namespace CacheView

def digestAt (cache : QueryCache HashSpec) (input : HashInput) : Digest :=
  match cache input with
  | some output => truncateHash output
  | none => 0

def tweakableHash (cache : QueryCache HashSpec) (parameter : PublicParameter)
    (domain : HashDomain) (payload : HashInput) : Digest :=
  digestAt cache (XmssSecurity.tweakableHashInput parameter domain payload)

def encodingInput (parameter : PublicParameter) (leafIndex : LeafIndex)
    (input : Message × Randomness) : HashInput :=
  XmssSecurity.tweakableHashInput parameter (.encoding leafIndex)
    (Concrete.encodingPayload input.1 input.2)

def chainInput (parameter : PublicParameter) (leafIndex : LeafIndex) (chain : ChainIndex)
    (position : ChainStep) (value : Digest) : HashInput :=
  XmssSecurity.tweakableHashInput parameter (.chain leafIndex chain position)
    (Concrete.digestBytes value)

def leafInput (parameter : PublicParameter) (leafIndex : LeafIndex)
    (endpoints : ChainIndex → Digest) : HashInput :=
  XmssSecurity.tweakableHashInput parameter (.leaf leafIndex)
    (Concrete.leafPayload endpoints)

def merkleInput (parameter : PublicParameter) (level : MerkleLevel)
    (node : MerkleNode) (left right : Digest) : HashInput :=
  XmssSecurity.tweakableHashInput parameter (.merkle level node)
    (Concrete.nodePayload left right)

def encodingHash (cache : QueryCache HashSpec) (parameter : PublicParameter)
    (leafIndex : LeafIndex) (input : Message × Randomness) : Digest :=
  digestAt cache (encodingInput parameter leafIndex input)

def chainStep (cache : QueryCache HashSpec) (parameter : PublicParameter)
    (leafIndex : LeafIndex) (chain : ChainIndex) (position : Nat) (value : Digest) : Digest :=
  if hposition : position < chainLength - 1 then
    digestAt cache (chainInput parameter leafIndex chain ⟨position, hposition⟩ value)
  else
    0

def leafHash (cache : QueryCache HashSpec) (parameter : PublicParameter)
    (leafIndex : LeafIndex) (endpoints : ChainIndex → Digest) : Digest :=
  digestAt cache (leafInput parameter leafIndex endpoints)

def merkleHash (cache : QueryCache HashSpec) (parameter : PublicParameter)
    (level : MerkleLevel) (node : MerkleNode) (left right : Digest) : Digest :=
  digestAt cache (merkleInput parameter level node left right)

abbrev nodeIndex (leafIndex : LeafIndex) (level : Nat) : MerkleNode :=
  Concrete.nodeIndex leafIndex level

def authenticationNodePayload (leafIndex : LeafIndex) (level : Nat)
    (current sibling : Digest) : HashInput :=
  if leafIndex.val.testBit level then
    Concrete.nodePayload sibling current
  else
    Concrete.nodePayload current sibling

def nodeInput (parameter : PublicParameter) (leafIndex : LeafIndex) (level : MerkleLevel)
    (current sibling : Digest) : HashInput :=
  XmssSecurity.tweakableHashInput parameter (.merkle level (nodeIndex leafIndex level.val))
    (authenticationNodePayload leafIndex level.val current sibling)

def nodeHash (cache : QueryCache HashSpec) (parameter : PublicParameter)
    (leafIndex : LeafIndex) (level : Nat) (left right : Digest) : Digest :=
  if hlevel : level < treeHeight then
    digestAt cache (nodeInput parameter leafIndex ⟨level, hlevel⟩ left right)
  else
    0

/-! The top layer's cache view. -/

def topEncodingInput (parameter : PublicParameter) (key : TopIndex)
    (input : Digest × Randomness) : HashInput :=
  XmssSecurity.tweakableHashInput parameter (.topEncoding key)
    (Concrete.topEncodingPayload input.1 input.2)

def topChainInput (parameter : PublicParameter) (key : TopIndex) (chain : ChainIndex)
    (position : ChainStep) (value : Digest) : HashInput :=
  XmssSecurity.tweakableHashInput parameter (.topChain key chain position)
    (Concrete.digestBytes value)

def topLeafInput (parameter : PublicParameter) (key : TopIndex)
    (endpoints : ChainIndex → Digest) : HashInput :=
  XmssSecurity.tweakableHashInput parameter (.topLeaf key) (Concrete.leafPayload endpoints)

def topMerkleInput (parameter : PublicParameter) (level : MerkleLevel)
    (node : TopNode) (left right : Digest) : HashInput :=
  XmssSecurity.tweakableHashInput parameter (.topMerkle level node)
    (Concrete.nodePayload left right)

def topEncodingHash (cache : QueryCache HashSpec) (parameter : PublicParameter)
    (key : TopIndex) (input : Digest × Randomness) : Digest :=
  digestAt cache (topEncodingInput parameter key input)

def topChainStep (cache : QueryCache HashSpec) (parameter : PublicParameter)
    (key : TopIndex) (chain : ChainIndex) (position : Nat) (value : Digest) : Digest :=
  if hposition : position < chainLength - 1 then
    digestAt cache (topChainInput parameter key chain ⟨position, hposition⟩ value)
  else
    0

def topLeafHash (cache : QueryCache HashSpec) (parameter : PublicParameter)
    (key : TopIndex) (endpoints : ChainIndex → Digest) : Digest :=
  digestAt cache (topLeafInput parameter key endpoints)

def topMerkleHash (cache : QueryCache HashSpec) (parameter : PublicParameter)
    (level : MerkleLevel) (node : TopNode) (left right : Digest) : Digest :=
  digestAt cache (topMerkleInput parameter level node left right)

def topAuthenticationNodePayload (key : TopIndex) (level : Nat) (current sibling : Digest) :
    HashInput :=
  if key.val.testBit level then
    Concrete.nodePayload sibling current
  else
    Concrete.nodePayload current sibling

def topNodeInput (parameter : PublicParameter) (key : TopIndex) (level : MerkleLevel)
    (current sibling : Digest) : HashInput :=
  XmssSecurity.tweakableHashInput parameter (.topMerkle level (Concrete.topNodeIndex key level.val))
    (topAuthenticationNodePayload key level.val current sibling)

def topNodeHash (cache : QueryCache HashSpec) (parameter : PublicParameter)
    (key : TopIndex) (level : Nat) (left right : Digest) : Digest :=
  if hlevel : level < treeHeight then
    digestAt cache (topNodeInput parameter key ⟨level, hlevel⟩ left right)
  else
    0

end CacheView

namespace CacheReplay

def oneTimePublicKey (cache : QueryCache HashSpec) (parameter : PublicParameter)
    (secret : LeafIndex → ChainIndex → Digest) (leafIndex : LeafIndex) : ChainIndex → Digest :=
  fun chain => Wots.walk (CacheView.chainStep cache parameter leafIndex chain) 0
    (chainLength - 1) (secret leafIndex chain)

def leafAt (cache : QueryCache HashSpec) (parameter : PublicParameter)
    (secret : LeafIndex → ChainIndex → Digest) (leafIndex : LeafIndex) : Digest :=
  CacheView.leafHash cache parameter leafIndex
    (oneTimePublicKey cache parameter secret leafIndex)

def treeNode (cache : QueryCache HashSpec) (parameter : PublicParameter)
    (secret : LeafIndex → ChainIndex → Digest) : Nat → MerkleNode → Digest
  | 0, node => leafAt cache parameter secret node
  | levels + 1, node =>
      if hlevel : levels < treeHeight then
        CacheView.merkleHash cache parameter ⟨levels, hlevel⟩ node
          (treeNode cache parameter secret levels (Concrete.childNode node false))
          (treeNode cache parameter secret levels (Concrete.childNode node true))
      else
        0

attribute [irreducible] treeNode

def topOneTimePublicKey (cache : QueryCache HashSpec) (parameter : PublicParameter)
    (topSecret : TopIndex → ChainIndex → Digest) (key : TopIndex) : ChainIndex → Digest :=
  fun chain => Wots.walk (CacheView.topChainStep cache parameter key chain) 0
    (chainLength - 1) (topSecret key chain)

def topLeafAt (cache : QueryCache HashSpec) (parameter : PublicParameter)
    (topSecret : TopIndex → ChainIndex → Digest) (key : TopIndex) : Digest :=
  CacheView.topLeafHash cache parameter key (topOneTimePublicKey cache parameter topSecret key)

def topTreeNode (cache : QueryCache HashSpec) (parameter : PublicParameter)
    (topSecret : TopIndex → ChainIndex → Digest) : Nat → TopNode → Digest
  | 0, node => topLeafAt cache parameter topSecret node
  | levels + 1, node =>
      if hlevel : levels < treeHeight then
        CacheView.topMerkleHash cache parameter ⟨levels, hlevel⟩ node
          (topTreeNode cache parameter topSecret levels (Concrete.topChildNode node false))
          (topTreeNode cache parameter topSecret levels (Concrete.topChildNode node true))
      else
        0

attribute [irreducible] topTreeNode

end CacheReplay

attribute [local semireducible] treeNode CacheReplay.treeNode sampleSecret signingRandomness

noncomputable local instance : SampleableType (LeafIndex → ChainIndex → Digest) :=
  SampleableType.ofFintype (LeafIndex → ChainIndex → Digest)

noncomputable local instance : SampleableType Randomness :=
  SampleableType.ofFintype Randomness

@[simp]
theorem treeNode_zero_eq {m : Type → Type} [Monad m] [HasQuery HashSpec m]
    (parameter : PublicParameter) (secret : LeafIndex → ChainIndex → Digest)
    (node : MerkleNode) :
    treeNode (m := m) parameter secret 0 node =
      leafAt (m := m) parameter secret node := rfl

theorem treeNode_succ_eq {m : Type → Type} [Monad m] [HasQuery HashSpec m]
    (parameter : PublicParameter) (secret : LeafIndex → ChainIndex → Digest)
    (levels : Nat) (node : MerkleNode) :
    treeNode (m := m) parameter secret (levels + 1) node = (do
      let left ← treeNode (m := m) parameter secret levels (childNode node false)
      let right ← treeNode (m := m) parameter secret levels (childNode node true)
      if hlevel : levels < treeHeight then
        nodeHash (m := m) parameter ⟨levels, hlevel⟩ node left right
      else
        pure 0) := rfl

theorem sampleSecret_eq : sampleSecret = $ᵗ (LeafIndex → ChainIndex → Digest) := rfl

theorem signingRandomness_eq : signingRandomness = $ᵗ Randomness := rfl

namespace CacheReplay

@[simp]
theorem treeNode_zero_eq (cache : QueryCache HashSpec) (parameter : PublicParameter)
    (secret : LeafIndex → ChainIndex → Digest) (node : MerkleNode) :
    treeNode cache parameter secret 0 node = leafAt cache parameter secret node := by
  with_unfolding_all rfl

theorem treeNode_succ_eq (cache : QueryCache HashSpec) (parameter : PublicParameter)
    (secret : LeafIndex → ChainIndex → Digest) (levels : Nat) (node : MerkleNode) :
    treeNode cache parameter secret (levels + 1) node =
      if hlevel : levels < treeHeight then
        CacheView.merkleHash cache parameter ⟨levels, hlevel⟩ node
          (treeNode cache parameter secret levels (Concrete.childNode node false))
          (treeNode cache parameter secret levels (Concrete.childNode node true))
      else
        0 := by
  with_unfolding_all rfl

theorem topTreeNode_zero_eq (cache : QueryCache HashSpec) (parameter : PublicParameter)
    (topSecret : TopIndex → ChainIndex → Digest) (node : TopNode) :
    topTreeNode cache parameter topSecret 0 node = topLeafAt cache parameter topSecret node := by
  with_unfolding_all rfl

theorem topTreeNode_succ_eq (cache : QueryCache HashSpec) (parameter : PublicParameter)
    (topSecret : TopIndex → ChainIndex → Digest) (levels : Nat) (node : TopNode) :
    topTreeNode cache parameter topSecret (levels + 1) node =
      if hlevel : levels < treeHeight then
        CacheView.topMerkleHash cache parameter ⟨levels, hlevel⟩ node
          (topTreeNode cache parameter topSecret levels (Concrete.topChildNode node false))
          (topTreeNode cache parameter topSecret levels (Concrete.topChildNode node true))
      else
        0 := by
  with_unfolding_all rfl

end CacheReplay

end Concrete

end XmssSecurity
