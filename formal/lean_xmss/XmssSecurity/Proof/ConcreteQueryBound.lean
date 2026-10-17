import XmssSecurity.Proof.HashAddress
import XmssSecurity.Proof.IdealStatement
import XmssSecurity.Proof.StatementLemmas

open OracleComp OracleSpec

namespace XmssSecurity

theorem Concrete.chainWalk_queryBound_zero_of_avoids
    (parameter : PublicParameter) (leafIndex : LeafIndex) (chain : ChainIndex)
    (position steps : Nat) (value : Digest) (targetDomain : HashDomain)
    (havoid : ∀ offset, offset < steps →
      ∀ hvalid : position + offset < chainLength - 1,
        HashDomain.chain leafIndex chain ⟨position + offset, hvalid⟩ ≠ targetDomain) :
    (Concrete.chainWalk parameter leafIndex chain position steps value :
      OracleComp HashSpec Digest).IsQueryBoundP
        (AtHashAddress parameter targetDomain) 0 := by
  induction steps with
  | zero => simp [Concrete.chainWalk]
  | succ steps ih =>
      rw [Concrete.chainWalk]
      refine OracleComp.isQueryBoundP_bind (m := 0)
        (ih fun offset hoffset => havoid offset (by omega)) ?_
      intro previous _
      split
      · exact Concrete.tweakableHash_queryBound_atOtherAddress parameter targetDomain
          (.chain leafIndex chain ⟨position + steps, by assumption⟩)
          (Concrete.digestBytes previous) (havoid steps (by omega) _)
      · simp

set_option maxHeartbeats 800000 in
theorem Concrete.chainWalk_queryBound_atAddress
    (parameter : PublicParameter) (leafIndex : LeafIndex) (chain : ChainIndex)
    (position steps : Nat) (value : Digest) (targetDomain : HashDomain) :
    (Concrete.chainWalk parameter leafIndex chain position steps value :
      OracleComp HashSpec Digest).IsQueryBoundP
        (AtHashAddress parameter targetDomain) 1 := by
  induction steps with
  | zero => simp [Concrete.chainWalk]
  | succ steps ih =>
      rw [Concrete.chainWalk]
      split
      · rename_i hposition
        let calledDomain : HashDomain :=
          .chain leafIndex chain ⟨position + steps, hposition⟩
        by_cases heq : calledDomain = targetDomain
        · subst targetDomain
          have hprefix :
              (Concrete.chainWalk parameter leafIndex chain position steps value :
                OracleComp HashSpec Digest).IsQueryBoundP
                  (AtHashAddress parameter calledDomain) 0 := by
            apply Concrete.chainWalk_queryBound_zero_of_avoids
            intro offset hoffset hvalid hsame
            simp only [calledDomain, HashDomain.chain.injEq, Fin.mk.injEq] at hsame
            omega
          refine OracleComp.isQueryBoundP_bind (m := 1) hprefix ?_
          intro previous _
          exact Concrete.tweakableHash_queryBound_atAddress parameter calledDomain
            (Concrete.digestBytes previous)
        · refine OracleComp.isQueryBoundP_bind (m := 0) ih ?_
          intro previous _
          exact Concrete.tweakableHash_queryBound_atOtherAddress parameter targetDomain
            calledDomain (Concrete.digestBytes previous) heq
      · refine OracleComp.isQueryBoundP_bind (m := 0) ih ?_
        intro previous _
        simp

theorem Concrete.chainWalk_queryBound_zero_at_other_chain
    (parameter : PublicParameter) (leafIndex targetLeafIndex : LeafIndex)
    (chain targetChain : ChainIndex) (targetStep : ChainStep)
    (position steps : Nat) (value : Digest)
    (hne : leafIndex ≠ targetLeafIndex ∨ chain ≠ targetChain) :
    (Concrete.chainWalk parameter leafIndex chain position steps value :
      OracleComp HashSpec Digest).IsQueryBoundP
        (AtHashAddress parameter (.chain targetLeafIndex targetChain targetStep)) 0 := by
  apply Concrete.chainWalk_queryBound_zero_of_avoids
  intro offset hoffset hvalid heq
  simp only [HashDomain.chain.injEq] at heq
  rcases hne with hleafIndex | hchain
  · exact hleafIndex heq.1
  · exact hchain heq.2.1

theorem Concrete.sequenceFin_queryBound_zero {α : Type} {n : Nat}
    (computation : Fin n → OracleComp HashSpec α)
    (p : HashInput → Prop) [DecidablePred p]
    (hzero : ∀ index, (computation index).IsQueryBoundP p 0) :
    (Concrete.sequenceFin computation).IsQueryBoundP p 0 := by
  induction n with
  | zero => simp [Concrete.sequenceFin]
  | succ n ih =>
      rw [Concrete.sequenceFin]
      refine OracleComp.isQueryBoundP_bind (m := 0) (hzero 0) ?_
      intro head _
      refine OracleComp.isQueryBoundP_bind (m := 0)
        (ih (fun index => computation index.succ) (fun index => hzero index.succ)) ?_
      intro tail _
      simp

theorem Concrete.sequenceFin_queryBound_one {α : Type} {n : Nat}
    (computation : Fin n → OracleComp HashSpec α)
    (p : HashInput → Prop) [DecidablePred p] (target : Fin n)
    (hone : (computation target).IsQueryBoundP p 1)
    (hzero : ∀ index, index ≠ target → (computation index).IsQueryBoundP p 0) :
    (Concrete.sequenceFin computation).IsQueryBoundP p 1 := by
  induction n with
  | zero => exact Fin.elim0 target
  | succ n ih =>
      rw [Concrete.sequenceFin]
      obtain rfl | ⟨tailTarget, rfl⟩ := target.eq_zero_or_eq_succ
      · refine OracleComp.isQueryBoundP_bind (m := 0) hone ?_
        intro head _
        refine OracleComp.isQueryBoundP_bind (m := 0)
          (Concrete.sequenceFin_queryBound_zero
            (fun index : Fin n => computation index.succ) p ?_) ?_
        · intro index
          apply hzero index.succ
          simp
        · intro tail _
          simp
      · have hhead : (computation 0).IsQueryBoundP p 0 := by
          apply hzero
          intro heq
          have hval := congrArg Fin.val heq
          simp at hval
        refine OracleComp.isQueryBoundP_bind (m := 1) hhead ?_
        intro head _
        refine OracleComp.isQueryBoundP_bind (m := 0)
          (ih (fun index => computation index.succ) tailTarget ?_ ?_) ?_
        · exact hone
        · intro index hne
          apply hzero index.succ
          simpa using hne
        · intro tail _
          simp

theorem Concrete.oneTimePublicKey_queryBound_chainAddress
    (parameter : PublicParameter) (secret : LeafIndex → ChainIndex → Digest)
    (leafIndex targetLeafIndex : LeafIndex) (targetChain : ChainIndex) (targetStep : ChainStep) :
    (Concrete.oneTimePublicKey parameter secret leafIndex :
      OracleComp HashSpec (ChainIndex → Digest)).IsQueryBoundP
        (AtHashAddress parameter (.chain targetLeafIndex targetChain targetStep)) 1 := by
  rw [Concrete.oneTimePublicKey]
  by_cases hleafIndex : leafIndex = targetLeafIndex
  · subst targetLeafIndex
    apply Concrete.sequenceFin_queryBound_one _ _ targetChain
    · exact Concrete.chainWalk_queryBound_atAddress parameter leafIndex targetChain 0
        (chainLength - 1) (secret leafIndex targetChain)
        (.chain leafIndex targetChain targetStep)
    · intro chain hchain
      exact Concrete.chainWalk_queryBound_zero_at_other_chain parameter leafIndex leafIndex
        chain targetChain targetStep 0 (chainLength - 1) (secret leafIndex chain)
        (Or.inr hchain)
  · exact (Concrete.sequenceFin_queryBound_zero _ _ fun chain =>
      Concrete.chainWalk_queryBound_zero_at_other_chain parameter leafIndex targetLeafIndex
        chain targetChain targetStep 0 (chainLength - 1) (secret leafIndex chain)
        (Or.inl hleafIndex)).mono (by omega)

theorem Concrete.oneTimePublicKey_queryBound_zero_chainAddress_at_other_leafIndex
    (parameter : PublicParameter) (secret : LeafIndex → ChainIndex → Digest)
    (leafIndex targetLeafIndex : LeafIndex) (targetChain : ChainIndex) (targetStep : ChainStep)
    (hne : leafIndex ≠ targetLeafIndex) :
    (Concrete.oneTimePublicKey parameter secret leafIndex :
      OracleComp HashSpec (ChainIndex → Digest)).IsQueryBoundP
        (AtHashAddress parameter (.chain targetLeafIndex targetChain targetStep)) 0 := by
  rw [Concrete.oneTimePublicKey]
  exact Concrete.sequenceFin_queryBound_zero _ _ fun chain =>
    Concrete.chainWalk_queryBound_zero_at_other_chain parameter leafIndex targetLeafIndex
      chain targetChain targetStep 0 (chainLength - 1) (secret leafIndex chain)
      (Or.inl hne)

theorem Concrete.leafAt_queryBound_chainAddress
    (parameter : PublicParameter) (secret : LeafIndex → ChainIndex → Digest)
    (leafIndex targetLeafIndex : LeafIndex) (targetChain : ChainIndex) (targetStep : ChainStep) :
    (Concrete.leafAt parameter secret leafIndex : OracleComp HashSpec Digest).IsQueryBoundP
      (AtHashAddress parameter (.chain targetLeafIndex targetChain targetStep)) 1 := by
  rw [Concrete.leafAt]
  refine OracleComp.isQueryBoundP_bind (m := 0)
    (Concrete.oneTimePublicKey_queryBound_chainAddress parameter secret leafIndex
      targetLeafIndex targetChain targetStep) ?_
  intro endpoints _
  exact Concrete.tweakableHash_queryBound_atOtherAddress parameter
    (.chain targetLeafIndex targetChain targetStep) (.leaf leafIndex)
    (Concrete.leafPayload endpoints) (by simp)

theorem Concrete.leafAt_queryBound_zero_chainAddress_at_other_leafIndex
    (parameter : PublicParameter) (secret : LeafIndex → ChainIndex → Digest)
    (leafIndex targetLeafIndex : LeafIndex) (targetChain : ChainIndex) (targetStep : ChainStep)
    (hne : leafIndex ≠ targetLeafIndex) :
    (Concrete.leafAt parameter secret leafIndex : OracleComp HashSpec Digest).IsQueryBoundP
      (AtHashAddress parameter (.chain targetLeafIndex targetChain targetStep)) 0 := by
  rw [Concrete.leafAt]
  refine OracleComp.isQueryBoundP_bind (m := 0)
    (Concrete.oneTimePublicKey_queryBound_zero_chainAddress_at_other_leafIndex parameter secret
      leafIndex targetLeafIndex targetChain targetStep hne) ?_
  intro endpoints _
  exact Concrete.tweakableHash_queryBound_atOtherAddress parameter
    (.chain targetLeafIndex targetChain targetStep) (.leaf leafIndex)
    (Concrete.leafPayload endpoints) (by simp)

theorem Concrete.chainWalk_queryBound_zero_leafAddress
    (parameter : PublicParameter) (leafIndex targetLeafIndex : LeafIndex) (chain : ChainIndex)
    (position steps : Nat) (value : Digest) :
    (Concrete.chainWalk parameter leafIndex chain position steps value :
      OracleComp HashSpec Digest).IsQueryBoundP
        (AtHashAddress parameter (.leaf targetLeafIndex)) 0 := by
  apply Concrete.chainWalk_queryBound_zero_of_avoids
  simp

theorem Concrete.oneTimePublicKey_queryBound_zero_leafAddress
    (parameter : PublicParameter) (secret : LeafIndex → ChainIndex → Digest)
    (leafIndex targetLeafIndex : LeafIndex) :
    (Concrete.oneTimePublicKey parameter secret leafIndex :
      OracleComp HashSpec (ChainIndex → Digest)).IsQueryBoundP
        (AtHashAddress parameter (.leaf targetLeafIndex)) 0 := by
  rw [Concrete.oneTimePublicKey]
  exact Concrete.sequenceFin_queryBound_zero _ _ fun chain =>
    Concrete.chainWalk_queryBound_zero_leafAddress parameter leafIndex targetLeafIndex chain
      0 (chainLength - 1) (secret leafIndex chain)

theorem Concrete.leafAt_queryBound_zero_at_other_leaf
    (parameter : PublicParameter) (secret : LeafIndex → ChainIndex → Digest)
    (leafIndex targetLeafIndex : LeafIndex) (hne : leafIndex ≠ targetLeafIndex) :
    (Concrete.leafAt parameter secret leafIndex : OracleComp HashSpec Digest).IsQueryBoundP
      (AtHashAddress parameter (.leaf targetLeafIndex)) 0 := by
  rw [Concrete.leafAt]
  refine OracleComp.isQueryBoundP_bind (m := 0)
    (Concrete.oneTimePublicKey_queryBound_zero_leafAddress parameter secret leafIndex targetLeafIndex) ?_
  intro endpoints _
  exact Concrete.tweakableHash_queryBound_atOtherAddress parameter (.leaf targetLeafIndex)
    (.leaf leafIndex) (Concrete.leafPayload endpoints) (by simpa using hne)

theorem Concrete.leafAt_queryBound_leafAddress
    (parameter : PublicParameter) (secret : LeafIndex → ChainIndex → Digest)
    (leafIndex targetLeafIndex : LeafIndex) :
    (Concrete.leafAt parameter secret leafIndex : OracleComp HashSpec Digest).IsQueryBoundP
      (AtHashAddress parameter (.leaf targetLeafIndex)) 1 := by
  by_cases hleafIndex : leafIndex = targetLeafIndex
  · subst targetLeafIndex
    rw [Concrete.leafAt]
    refine OracleComp.isQueryBoundP_bind (m := 1)
      (Concrete.oneTimePublicKey_queryBound_zero_leafAddress parameter secret leafIndex leafIndex) ?_
    intro endpoints _
    exact Concrete.tweakableHash_queryBound_atAddress parameter (.leaf leafIndex)
      (Concrete.leafPayload endpoints)
  · exact (Concrete.leafAt_queryBound_zero_at_other_leaf parameter secret leafIndex
      targetLeafIndex hleafIndex).mono (by omega)

theorem Concrete.chainWalk_queryBound_zero_merkleAddress
    (parameter : PublicParameter) (leafIndex : LeafIndex) (chain : ChainIndex)
    (position steps : Nat) (value : Digest)
    (targetLevel : MerkleLevel) (targetNode : MerkleNode) :
    (Concrete.chainWalk parameter leafIndex chain position steps value :
      OracleComp HashSpec Digest).IsQueryBoundP
        (AtHashAddress parameter (.merkle targetLevel targetNode)) 0 := by
  apply Concrete.chainWalk_queryBound_zero_of_avoids
  simp

theorem Concrete.oneTimePublicKey_queryBound_zero_merkleAddress
    (parameter : PublicParameter) (secret : LeafIndex → ChainIndex → Digest)
    (leafIndex : LeafIndex) (targetLevel : MerkleLevel) (targetNode : MerkleNode) :
    (Concrete.oneTimePublicKey parameter secret leafIndex :
      OracleComp HashSpec (ChainIndex → Digest)).IsQueryBoundP
        (AtHashAddress parameter (.merkle targetLevel targetNode)) 0 := by
  rw [Concrete.oneTimePublicKey]
  exact Concrete.sequenceFin_queryBound_zero _ _ fun chain =>
    Concrete.chainWalk_queryBound_zero_merkleAddress parameter leafIndex chain
      0 (chainLength - 1) (secret leafIndex chain) targetLevel targetNode

theorem Concrete.leafAt_queryBound_zero_merkleAddress
    (parameter : PublicParameter) (secret : LeafIndex → ChainIndex → Digest)
    (leafIndex : LeafIndex) (targetLevel : MerkleLevel) (targetNode : MerkleNode) :
    (Concrete.leafAt parameter secret leafIndex : OracleComp HashSpec Digest).IsQueryBoundP
      (AtHashAddress parameter (.merkle targetLevel targetNode)) 0 := by
  rw [Concrete.leafAt]
  refine OracleComp.isQueryBoundP_bind (m := 0)
    (Concrete.oneTimePublicKey_queryBound_zero_merkleAddress parameter secret leafIndex
      targetLevel targetNode) ?_
  intro endpoints _
  exact Concrete.tweakableHash_queryBound_atOtherAddress parameter
    (.merkle targetLevel targetNode) (.leaf leafIndex)
    (Concrete.leafPayload endpoints) (by simp)

theorem Concrete.chainWalk_queryBound_zero_encodingAddress
    (parameter : PublicParameter) (leafIndex targetLeafIndex : LeafIndex)
    (chain : ChainIndex) (position steps : Nat) (value : Digest) :
    (Concrete.chainWalk parameter leafIndex chain position steps value :
      OracleComp HashSpec Digest).IsQueryBoundP
        (AtHashAddress parameter (.encoding targetLeafIndex)) 0 := by
  apply Concrete.chainWalk_queryBound_zero_of_avoids
  simp

theorem Concrete.oneTimePublicKey_queryBound_zero_encodingAddress
    (parameter : PublicParameter) (secret : LeafIndex → ChainIndex → Digest)
    (leafIndex targetLeafIndex : LeafIndex) :
    (Concrete.oneTimePublicKey parameter secret leafIndex :
      OracleComp HashSpec (ChainIndex → Digest)).IsQueryBoundP
        (AtHashAddress parameter (.encoding targetLeafIndex)) 0 := by
  rw [Concrete.oneTimePublicKey]
  exact Concrete.sequenceFin_queryBound_zero _ _ fun chain =>
    Concrete.chainWalk_queryBound_zero_encodingAddress parameter leafIndex targetLeafIndex
      chain 0 (chainLength - 1) (secret leafIndex chain)

theorem Concrete.leafAt_queryBound_zero_encodingAddress
    (parameter : PublicParameter) (secret : LeafIndex → ChainIndex → Digest)
    (leafIndex targetLeafIndex : LeafIndex) :
    (Concrete.leafAt parameter secret leafIndex : OracleComp HashSpec Digest).IsQueryBoundP
      (AtHashAddress parameter (.encoding targetLeafIndex)) 0 := by
  rw [Concrete.leafAt]
  refine OracleComp.isQueryBoundP_bind (m := 0)
    (Concrete.oneTimePublicKey_queryBound_zero_encodingAddress parameter secret leafIndex
      targetLeafIndex) ?_
  intro endpoints _
  exact Concrete.tweakableHash_queryBound_atOtherAddress parameter
    (.encoding targetLeafIndex) (.leaf leafIndex) (Concrete.leafPayload endpoints) (by simp)

theorem Concrete.treeNode_queryBound_zero_encodingAddress
    (parameter : PublicParameter) (secret : LeafIndex → ChainIndex → Digest)
    (targetLeafIndex : LeafIndex) (levels : Nat) (node : MerkleNode) :
    (Concrete.treeNode parameter secret levels node :
      OracleComp HashSpec Digest).IsQueryBoundP
        (AtHashAddress parameter (.encoding targetLeafIndex)) 0 := by
  induction levels generalizing node with
  | zero =>
      rw [Concrete.treeNode_zero_eq]
      exact Concrete.leafAt_queryBound_zero_encodingAddress parameter secret node targetLeafIndex
  | succ levels ih =>
      rw [Concrete.treeNode_succ_eq]
      refine OracleComp.isQueryBoundP_bind (m := 0) (ih _) ?_
      intro left _
      refine OracleComp.isQueryBoundP_bind (m := 0) (ih _) ?_
      intro right _
      split
      · exact Concrete.tweakableHash_queryBound_atOtherAddress parameter
          (.encoding targetLeafIndex) (.merkle ⟨levels, by assumption⟩ node)
          (Concrete.nodePayload left right) (by simp)
      · simp

theorem Concrete.encodingHash_queryBound_zero_at_other_input
    (parameter : PublicParameter) (leafIndex : LeafIndex)
    (message : Message) (randomness : Randomness) (target : HashInput)
    (hne : Concrete.CacheView.encodingInput parameter leafIndex (message, randomness) ≠
      target) :
    (Concrete.encodingHash parameter leafIndex message randomness :
      OracleComp HashSpec Digest).IsQueryBoundP (· = target) 0 := by
  simp [Concrete.encodingHash, Concrete.tweakableHash, Concrete.oracleHash,
    show ¬tweakableHashInput parameter (.encoding leafIndex)
      (Concrete.encodingPayload message randomness) = target by
        simpa only [Concrete.CacheView.encodingInput] using hne]

end XmssSecurity
