import XmssSecurity.Proof.IdealStatement
import XmssSecurity.Proof.Wots

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

def encodingInput (parameter : PublicParameter) (epoch : Epoch)
    (input : Message × Randomness) : HashInput :=
  XmssSecurity.tweakableHashInput parameter (.encoding epoch)
    (Concrete.encodingPayload input.1 input.2)

def chainInput (parameter : PublicParameter) (epoch : Epoch) (chain : ChainIndex)
    (position : ChainStep) (value : Digest) : HashInput :=
  XmssSecurity.tweakableHashInput parameter (.chain epoch chain position)
    (Concrete.digestBytes value)

def leafInput (parameter : PublicParameter) (epoch : Epoch)
    (endpoints : ChainIndex → Digest) : HashInput :=
  XmssSecurity.tweakableHashInput parameter (.leaf epoch)
    (Concrete.leafPayload endpoints)

def merkleInput (parameter : PublicParameter) (level : MerkleLevel)
    (node : MerkleNode) (left right : Digest) : HashInput :=
  XmssSecurity.tweakableHashInput parameter (.merkle level node)
    (Concrete.nodePayload left right)

def encodingHash (cache : QueryCache HashSpec) (parameter : PublicParameter)
    (epoch : Epoch) (input : Message × Randomness) : Digest :=
  digestAt cache (encodingInput parameter epoch input)

def chainStep (cache : QueryCache HashSpec) (parameter : PublicParameter)
    (epoch : Epoch) (chain : ChainIndex) (position : Nat) (value : Digest) : Digest :=
  if hposition : position < chainLength - 1 then
    digestAt cache (chainInput parameter epoch chain ⟨position, hposition⟩ value)
  else
    0

def leafHash (cache : QueryCache HashSpec) (parameter : PublicParameter)
    (epoch : Epoch) (endpoints : ChainIndex → Digest) : Digest :=
  digestAt cache (leafInput parameter epoch endpoints)

def merkleHash (cache : QueryCache HashSpec) (parameter : PublicParameter)
    (level : MerkleLevel) (node : MerkleNode) (left right : Digest) : Digest :=
  digestAt cache (merkleInput parameter level node left right)

abbrev nodeIndex (epoch : Epoch) (level : Nat) : MerkleNode :=
  Concrete.nodeIndex epoch level

def authenticationNodePayload (epoch : Epoch) (level : Nat)
    (current sibling : Digest) : HashInput :=
  if epoch.val.testBit level then
    Concrete.nodePayload sibling current
  else
    Concrete.nodePayload current sibling

def nodeInput (parameter : PublicParameter) (epoch : Epoch) (level : MerkleLevel)
    (current sibling : Digest) : HashInput :=
  XmssSecurity.tweakableHashInput parameter (.merkle level (nodeIndex epoch level.val))
    (authenticationNodePayload epoch level.val current sibling)

def nodeHash (cache : QueryCache HashSpec) (parameter : PublicParameter)
    (epoch : Epoch) (level : Nat) (left right : Digest) : Digest :=
  if hlevel : level < treeHeight then
    digestAt cache (nodeInput parameter epoch ⟨level, hlevel⟩ left right)
  else
    0

end CacheView

namespace CacheReplay

def oneTimePublicKey (cache : QueryCache HashSpec) (parameter : PublicParameter)
    (secret : Epoch → ChainIndex → Digest) (epoch : Epoch) : ChainIndex → Digest :=
  fun chain => Wots.walk (CacheView.chainStep cache parameter epoch chain) 0
    (chainLength - 1) (secret epoch chain)

def leafAt (cache : QueryCache HashSpec) (parameter : PublicParameter)
    (secret : Epoch → ChainIndex → Digest) (epoch : Epoch) : Digest :=
  CacheView.leafHash cache parameter epoch
    (oneTimePublicKey cache parameter secret epoch)

def treeNode (cache : QueryCache HashSpec) (parameter : PublicParameter)
    (secret : Epoch → ChainIndex → Digest) : Nat → MerkleNode → Digest
  | 0, node => leafAt cache parameter secret node
  | levels + 1, node =>
      if hlevel : levels < treeHeight then
        CacheView.merkleHash cache parameter ⟨levels, hlevel⟩ node
          (treeNode cache parameter secret levels (Concrete.childNode node false))
          (treeNode cache parameter secret levels (Concrete.childNode node true))
      else
        0

attribute [irreducible] treeNode

end CacheReplay

attribute [local semireducible] treeNode CacheReplay.treeNode sampleSecret signingRandomness

noncomputable local instance : SampleableType (Epoch → ChainIndex → Digest) :=
  SampleableType.ofFintype (Epoch → ChainIndex → Digest)

noncomputable local instance : SampleableType Randomness :=
  SampleableType.ofFintype Randomness

@[simp]
theorem treeNode_zero_eq {m : Type → Type} [Monad m] [HasQuery HashSpec m]
    (parameter : PublicParameter) (secret : Epoch → ChainIndex → Digest)
    (node : MerkleNode) :
    treeNode (m := m) parameter secret 0 node =
      leafAt (m := m) parameter secret node := rfl

theorem treeNode_succ_eq {m : Type → Type} [Monad m] [HasQuery HashSpec m]
    (parameter : PublicParameter) (secret : Epoch → ChainIndex → Digest)
    (levels : Nat) (node : MerkleNode) :
    treeNode (m := m) parameter secret (levels + 1) node = (do
      let left ← treeNode (m := m) parameter secret levels (childNode node false)
      let right ← treeNode (m := m) parameter secret levels (childNode node true)
      if hlevel : levels < treeHeight then
        nodeHash (m := m) parameter ⟨levels, hlevel⟩ node left right
      else
        pure 0) := rfl

theorem sampleSecret_eq : sampleSecret = $ᵗ (Epoch → ChainIndex → Digest) := rfl

theorem signingRandomness_eq : signingRandomness = $ᵗ Randomness := rfl

namespace CacheReplay

@[simp]
theorem treeNode_zero_eq (cache : QueryCache HashSpec) (parameter : PublicParameter)
    (secret : Epoch → ChainIndex → Digest) (node : MerkleNode) :
    treeNode cache parameter secret 0 node = leafAt cache parameter secret node := by
  with_unfolding_all rfl

theorem treeNode_succ_eq (cache : QueryCache HashSpec) (parameter : PublicParameter)
    (secret : Epoch → ChainIndex → Digest) (levels : Nat) (node : MerkleNode) :
    treeNode cache parameter secret (levels + 1) node =
      if hlevel : levels < treeHeight then
        CacheView.merkleHash cache parameter ⟨levels, hlevel⟩ node
          (treeNode cache parameter secret levels (Concrete.childNode node false))
          (treeNode cache parameter secret levels (Concrete.childNode node true))
      else
        0 := by
  with_unfolding_all rfl

end CacheReplay

end Concrete

end XmssSecurity
