module

public import XmssSecurity.Proof.StatementLemmas

@[expose] public section

/-!
# The model's key generation is natural in its monad

Simulating a computation of the model's key generation, written against one oracle capability, gives
the same computation against another, provided each hash query is simulated by a hash query.
-/

open OracleComp OracleSpec

namespace XmssSecurity.Bridge

set_option backward.isDefEq.respectTransparency false

theorem nat_sequenceFin {ι : Type} {s₁ : OracleSpec ι} {m₂ : Type → Type} [Monad m₂] [LawfulMonad m₂]
    (impl : QueryImpl s₁ m₂) {α : Type} {n : Nat} (c : Fin n → OracleComp s₁ α) :
    simulateQ impl (Concrete.sequenceFin c) = Concrete.sequenceFin fun i => simulateQ impl (c i) := by
  induction n with
  | zero => simp [Concrete.sequenceFin]
  | succ n ih =>
      simp only [Concrete.sequenceFin, simulateQ_bind, simulateQ_pure, ih (fun i => c i.succ)]

variable {ι : Type} {s₁ : OracleSpec ι} [inst₁ : HasQuery HashSpec (OracleComp s₁)]
  {m₂ : Type → Type} [Monad m₂] [LawfulMonad m₂] [inst₂ : HasQuery HashSpec m₂]
  (impl : QueryImpl s₁ m₂)
  (hq : ∀ x, simulateQ impl (HasQuery.query (spec := HashSpec) (m := OracleComp s₁) x) =
    HasQuery.query (spec := HashSpec) (m := m₂) x)

include hq

theorem nat_tweakableHash (parameter : PublicParameter) (domain : HashDomain) (payload : HashInput) :
    simulateQ impl (Concrete.tweakableHash (m := OracleComp s₁) parameter domain payload) =
      Concrete.tweakableHash (m := m₂) parameter domain payload := by
  simp only [Concrete.tweakableHash, Concrete.oracleHash, simulateQ_bind, simulateQ_pure, hq]

theorem nat_chainWalk (parameter : PublicParameter) (index : LeafIndex) (chain : ChainIndex)
    (start steps : Nat) (value : Digest) :
    simulateQ impl (Concrete.chainWalk (m := OracleComp s₁) parameter index chain start steps value) =
      Concrete.chainWalk (m := m₂) parameter index chain start steps value := by
  induction steps with
  | zero => simp [Concrete.chainWalk]
  | succ steps ih =>
      rw [Concrete.chainWalk, Concrete.chainWalk, simulateQ_bind, ih]
      apply bind_congr
      intro previous
      split
      · exact nat_tweakableHash impl hq _ _ _
      · simp

theorem nat_topChainWalk (parameter : PublicParameter) (key : TopIndex) (chain : ChainIndex)
    (start steps : Nat) (value : Digest) :
    simulateQ impl (Concrete.topChainWalk (m := OracleComp s₁) parameter key chain start steps value) =
      Concrete.topChainWalk (m := m₂) parameter key chain start steps value := by
  induction steps with
  | zero => simp [Concrete.topChainWalk]
  | succ steps ih =>
      rw [Concrete.topChainWalk, Concrete.topChainWalk, simulateQ_bind, ih]
      apply bind_congr
      intro previous
      split
      · exact nat_tweakableHash impl hq _ _ _
      · simp

theorem nat_treeNode (parameter : PublicParameter) (secret : LeafIndex → ChainIndex → Digest)
    (levels : Nat) (node : MerkleNode) :
    simulateQ impl (Concrete.treeNode (m := OracleComp s₁) parameter secret levels node) =
      Concrete.treeNode (m := m₂) parameter secret levels node := by
  induction levels generalizing node with
  | zero =>
      simp only [Concrete.treeNode_zero_eq, Concrete.leafAt, Concrete.oneTimePublicKey, Concrete.leafHash,
        simulateQ_bind, nat_sequenceFin impl, nat_chainWalk impl hq, nat_tweakableHash impl hq]
  | succ levels ih =>
      simp only [Concrete.treeNode_succ_eq, simulateQ_bind, ih]
      apply bind_congr
      intro left
      apply bind_congr
      intro right
      split
      · exact nat_tweakableHash impl hq _ _ _
      · simp

theorem nat_topTreeNode (parameter : PublicParameter) (topSecret : TopIndex → ChainIndex → Digest)
    (levels : Nat) (node : TopNode) :
    simulateQ impl (Concrete.topTreeNode (m := OracleComp s₁) parameter topSecret levels node) =
      Concrete.topTreeNode (m := m₂) parameter topSecret levels node := by
  induction levels generalizing node with
  | zero =>
      simp only [Concrete.topTreeNode, Concrete.topLeafAt, Concrete.topOneTimePublicKey,
        Concrete.topLeafHash, simulateQ_bind, nat_sequenceFin impl, nat_topChainWalk impl hq,
        nat_tweakableHash impl hq]
  | succ levels ih =>
      simp only [Concrete.topTreeNode, simulateQ_bind, ih]
      apply bind_congr
      intro left
      apply bind_congr
      intro right
      split
      · exact nat_tweakableHash impl hq _ _ _
      · simp

theorem nat_topSignFrom (parameter : PublicParameter) (key : TopIndex) (root : Digest) (base : Randomness)
    (attempts trial : Nat) :
    simulateQ impl (Concrete.topSignFrom (m := OracleComp s₁) parameter key root base attempts trial) =
      Concrete.topSignFrom (m := m₂) parameter key root base attempts trial := by
  induction attempts generalizing trial with
  | zero => simp [Concrete.topSignFrom]
  | succ attempts ih =>
      simp only [Concrete.topSignFrom, Concrete.topEncodingHash, simulateQ_bind, nat_tweakableHash impl hq]
      apply bind_congr
      intro digest
      split
      · simp
      · exact ih _

theorem nat_honestKeygen (parameter : PublicParameter) (secret : LeafIndex → ChainIndex → Digest)
    (topSecret : TopIndex → ChainIndex → Digest) (topBase : TopIndex → Digest → OracleComp s₁ Randomness) :
    simulateQ impl (Concrete.honestKeygen (m := OracleComp s₁) parameter secret topSecret topBase) =
      Concrete.honestKeygen (m := m₂) parameter secret topSecret
        fun key root => simulateQ impl (topBase key root) := by
  simp only [Concrete.honestKeygen, simulateQ_bind, simulateQ_pure, nat_sequenceFin impl,
    nat_treeNode impl hq, nat_topSignFrom impl hq, nat_topTreeNode impl hq]

end XmssSecurity.Bridge
