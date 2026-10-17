import XmssSecurity.Proof.HashInputLemmas
import XmssSecurity.Proof.HashAddress

/-!
# One-time keys of either layer

Lane 1 presamples the hidden chain values of both layers in one table. A `ChainKey` is a bottom leaf
index or a top key; its chain steps differ only in their address.
-/

open OracleComp OracleSpec

namespace XmssSecurity

/-- A one-time key of either layer: a bottom leaf index or a top key. -/
abbrev ChainKey := LeafIndex ⊕ TopIndex

instance : LawfulBEq ChainKey where
  eq_of_beq {a b} h := by
    cases a <;> cases b <;> simp_all [BEq.beq, Sum.instBEq.beq]
  rfl {a} := by cases a <;> simp [BEq.beq, Sum.instBEq.beq]

/-- The address of a chain step of a key of either layer. -/
def ChainKey.chainDomain : ChainKey → ChainIndex → ChainStep → HashDomain
  | .inl leafIndex, chain, step => .chain leafIndex chain step
  | .inr key, chain, step => .topChain key chain step

/-- The address of a key's leaf. -/
def ChainKey.leafDomain : ChainKey → HashDomain
  | .inl leafIndex => .leaf leafIndex
  | .inr key => .topLeaf key

@[simp] theorem ChainKey.chainDomain_inl (leafIndex : LeafIndex) (chain : ChainIndex)
    (step : ChainStep) : ChainKey.chainDomain (.inl leafIndex) chain step =
      .chain leafIndex chain step := rfl

@[simp] theorem ChainKey.chainDomain_inr (key : TopIndex) (chain : ChainIndex)
    (step : ChainStep) : ChainKey.chainDomain (.inr key) chain step =
      .topChain key chain step := rfl

theorem ChainKey.chainDomain_injective {leftKey rightKey : ChainKey}
    {leftChain rightChain : ChainIndex} {leftStep rightStep : ChainStep}
    (heq : leftKey.chainDomain leftChain leftStep = rightKey.chainDomain rightChain rightStep) :
    leftKey = rightKey ∧ leftChain = rightChain ∧ leftStep = rightStep := by
  cases leftKey <;> cases rightKey <;> simp_all [ChainKey.chainDomain]

theorem ChainKey.domainSuffix_chainDomain (key : ChainKey) (chain : ChainIndex)
    (step : ChainStep) :
    domainSuffix (key.chainDomain chain step) = bytesLE 16 (BitVec.ofNat 128 chain.val) := by
  cases key <;> rfl

/-- The chain starts of a key of either layer. -/
def SecretKey.keyChainStart (secretKey : SecretKey) : ChainKey → ChainIndex → Digest :=
  Sum.elim secretKey.chainStart secretKey.topChainStart

@[simp] theorem SecretKey.keyChainStart_inl (secretKey : SecretKey) (leafIndex : LeafIndex) :
    secretKey.keyChainStart (.inl leafIndex) = secretKey.chainStart leafIndex := rfl

@[simp] theorem SecretKey.keyChainStart_inr (secretKey : SecretKey) (key : TopIndex) :
    secretKey.keyChainStart (.inr key) = secretKey.topChainStart key := rfl

namespace Concrete

variable {m : Type → Type} [Monad m] [HasQuery HashSpec m]

/-- One chain step of a key of either layer. -/
def keyChainHash (parameter : PublicParameter) (key : ChainKey) (chain : ChainIndex)
    (step : ChainStep) (value : Digest) : m Digest :=
  tweakableHash parameter (key.chainDomain chain step) (bytesLE 16 value)

theorem keyChainHash_inl (parameter : PublicParameter) (leafIndex : LeafIndex)
    (chain : ChainIndex) (step : ChainStep) (value : Digest) :
    keyChainHash (m := m) parameter (.inl leafIndex) chain step value =
      chainHash parameter leafIndex chain step value := rfl

theorem keyChainHash_inr (parameter : PublicParameter) (key : TopIndex)
    (chain : ChainIndex) (step : ChainStep) (value : Digest) :
    keyChainHash (m := m) parameter (.inr key) chain step value =
      topChainHash parameter key chain step value := rfl

/-- A chain walk of a key of either layer, as `chainWalk`. -/
def keyChainWalk (parameter : PublicParameter) (key : ChainKey) (chain : ChainIndex) :
    Nat → Nat → Digest → m Digest
  | _, 0, value => pure value
  | position, steps + 1, value => do
      let previous ← keyChainWalk parameter key chain position steps value
      if hposition : position + steps < chainLength - 1 then
        keyChainHash parameter key chain ⟨position + steps, hposition⟩ previous
      else
        pure 0

theorem keyChainWalk_inl (parameter : PublicParameter) (leafIndex : LeafIndex)
    (chain : ChainIndex) (position steps : Nat) (value : Digest) :
    keyChainWalk (m := m) parameter (.inl leafIndex) chain position steps value =
      chainWalk parameter leafIndex chain position steps value := by
  induction steps with
  | zero => rfl
  | succ steps ih => simp only [keyChainWalk, chainWalk, ih]; rfl

theorem keyChainWalk_inr (parameter : PublicParameter) (key : TopIndex)
    (chain : ChainIndex) (position steps : Nat) (value : Digest) :
    keyChainWalk (m := m) parameter (.inr key) chain position steps value =
      topChainWalk parameter key chain position steps value := by
  induction steps with
  | zero => rfl
  | succ steps ih => simp only [keyChainWalk, topChainWalk, ih]; rfl

namespace CacheView

/-- The input of a chain step of a key of either layer. -/
def keyChainInput (parameter : PublicParameter) (key : ChainKey) (chain : ChainIndex)
    (position : ChainStep) (value : Digest) : HashInput :=
  XmssSecurity.tweakableHashInput parameter (key.chainDomain chain position)
    (Concrete.digestBytes value)

@[simp] theorem keyChainInput_inl (parameter : PublicParameter) (leafIndex : LeafIndex) :
    keyChainInput parameter (.inl leafIndex) = chainInput parameter leafIndex := rfl

@[simp] theorem keyChainInput_inr (parameter : PublicParameter) (key : TopIndex) :
    keyChainInput parameter (.inr key) = topChainInput parameter key := rfl

theorem keyChainInput_eq_iff (parameter : PublicParameter)
    (leftKey rightKey : ChainKey) (leftChain rightChain : ChainIndex)
    (leftStep rightStep : ChainStep) (leftValue rightValue : Digest) :
    keyChainInput parameter leftKey leftChain leftStep leftValue =
        keyChainInput parameter rightKey rightChain rightStep rightValue ↔
      leftKey = rightKey ∧ leftChain = rightChain ∧ leftStep = rightStep ∧
        leftValue = rightValue := by
  constructor
  · intro heq
    obtain ⟨hkey, hchain, hstep⟩ :=
      ChainKey.chainDomain_injective (domain_eq_of_tweakableHashInput_eq parameter heq)
    subst hkey hchain hstep
    exact ⟨rfl, rfl, rfl, Concrete.digestBytes_injective
      (payload_eq_of_tweakableHashInput_eq parameter _ heq)⟩
  · rintro ⟨rfl, rfl, rfl, rfl⟩
    rfl

theorem keyChainInput_atHashAddress (parameter : PublicParameter) (key : ChainKey)
    (chain : ChainIndex) (step : ChainStep) (value : Digest) :
    AtHashAddress parameter (key.chainDomain chain step)
      (keyChainInput parameter key chain step value) :=
  (atHashAddress_tweakableHashInput_iff parameter _ _ _).mpr rfl

/-- A chain step of a key of either layer, read from a cache. -/
def keyChainStep (cache : QueryCache HashSpec) (parameter : PublicParameter) (key : ChainKey)
    (chain : ChainIndex) (position : Nat) (value : Digest) : Digest :=
  if hposition : position < chainLength - 1 then
    digestAt cache (keyChainInput parameter key chain ⟨position, hposition⟩ value)
  else
    0

@[simp] theorem keyChainStep_inl (cache : QueryCache HashSpec) (parameter : PublicParameter)
    (leafIndex : LeafIndex) :
    keyChainStep cache parameter (.inl leafIndex) = chainStep cache parameter leafIndex := rfl

@[simp] theorem keyChainStep_inr (cache : QueryCache HashSpec) (parameter : PublicParameter)
    (key : TopIndex) :
    keyChainStep cache parameter (.inr key) = topChainStep cache parameter key := rfl

theorem keyChainStep_eq (cache : QueryCache HashSpec) (parameter : PublicParameter)
    (key : ChainKey) (chain : ChainIndex) (position : Nat) (value : Digest)
    (hposition : position < chainLength - 1) :
    keyChainStep cache parameter key chain position value =
      digestAt cache (keyChainInput parameter key chain ⟨position, hposition⟩ value) := by
  simp [keyChainStep, hposition]

/-- The leaf input of a key of either layer. -/
def keyLeafInput (parameter : PublicParameter) (key : ChainKey)
    (endpoints : ChainIndex → Digest) : HashInput :=
  XmssSecurity.tweakableHashInput parameter key.leafDomain (Concrete.leafPayload endpoints)

@[simp] theorem keyLeafInput_inl (parameter : PublicParameter) (leafIndex : LeafIndex) :
    keyLeafInput parameter (.inl leafIndex) = leafInput parameter leafIndex := rfl

@[simp] theorem keyLeafInput_inr (parameter : PublicParameter) (key : TopIndex) :
    keyLeafInput parameter (.inr key) = topLeafInput parameter key := rfl

theorem keyLeafInput_eq_iff (parameter : PublicParameter) (leftKey rightKey : ChainKey)
    (left right : ChainIndex → Digest) :
    keyLeafInput parameter leftKey left = keyLeafInput parameter rightKey right ↔
      leftKey = rightKey ∧ left = right := by
  constructor
  · intro heq
    have hdomain := domain_eq_of_tweakableHashInput_eq parameter heq
    have hkey : leftKey = rightKey := by
      cases leftKey <;> cases rightKey <;> simp_all [ChainKey.leafDomain]
    subst hkey
    exact ⟨rfl, Concrete.leafPayload_injective
      (payload_eq_of_tweakableHashInput_eq parameter _ heq)⟩
  · rintro ⟨rfl, rfl⟩
    rfl

theorem keyChainInput_ne_keyLeafInput (parameter : PublicParameter) (key : ChainKey)
    (chain : ChainIndex) (step : ChainStep) (value : Digest) (leafKey : ChainKey)
    (endpoints : ChainIndex → Digest) :
    keyChainInput parameter key chain step value ≠ keyLeafInput parameter leafKey endpoints := by
  intro heq
  have hdomain := domain_eq_of_tweakableHashInput_eq parameter heq
  cases key <;> cases leafKey <;> simp_all [ChainKey.chainDomain, ChainKey.leafDomain]

end CacheView

namespace CacheReplay

/-- The public chain ends of a key of either layer, replayed from a cache. -/
def keyOneTimePublicKey (cache : QueryCache HashSpec) (parameter : PublicParameter)
    (start : ChainKey → ChainIndex → Digest) (key : ChainKey) : ChainIndex → Digest :=
  fun chain => Wots.walk (CacheView.keyChainStep cache parameter key chain) 0
    (chainLength - 1) (start key chain)

end CacheReplay

end Concrete

end XmssSecurity
