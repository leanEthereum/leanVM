module

public import XmssSecurity.Proof.Bridge.Honest

@[expose] public section

/-!
# What the prepared cache resolves

Every chain prefix, leaf and in-range node of both layers, and every top grinding, resolves in the
prepared cache to the value the model's secret key stores.
-/

open OracleComp OracleSpec

namespace XmssSecurity.Bridge

open Seeded DeterministicSigning

set_option backward.isDefEq.respectTransparency false

theorem chainWalk_split (parameter : PublicParameter) (index : LeafIndex) (chain : ChainIndex)
    (start s1 s2 : Nat) (value : Digest) :
    (Concrete.chainWalk parameter index chain start (s1 + s2) value : OracleComp HashSpec Digest) =
      Concrete.chainWalk parameter index chain start s1 value >>=
        Concrete.chainWalk parameter index chain (start + s1) s2 := by
  induction s2 with
  | zero => simp [Concrete.chainWalk]
  | succ s2 ih =>
      rw [show s1 + (s2 + 1) = s1 + s2 + 1 from rfl, Concrete.chainWalk, ih, bind_assoc]
      apply bind_congr
      intro x
      rw [Concrete.chainWalk]
      simp only [Nat.add_assoc]

theorem topChainWalk_split (parameter : PublicParameter) (key : TopIndex) (chain : ChainIndex)
    (start s1 s2 : Nat) (value : Digest) :
    (Concrete.topChainWalk parameter key chain start (s1 + s2) value : OracleComp HashSpec Digest) =
      Concrete.topChainWalk parameter key chain start s1 value >>=
        Concrete.topChainWalk parameter key chain (start + s1) s2 := by
  induction s2 with
  | zero => simp [Concrete.topChainWalk]
  | succ s2 ih =>
      rw [show s1 + (s2 + 1) = s1 + s2 + 1 from rfl, Concrete.topChainWalk, ih, bind_assoc]
      apply bind_congr
      intro x
      rw [Concrete.topChainWalk]
      simp only [Nat.add_assoc]

/-- The computation resolves to some value. -/
def Res {α : Type} (cache : QueryCache HashSpec) (c : OracleComp HashSpec α) : Prop :=
  ∃ v, Resolves cache c v

theorem Res.of_bind {α β : Type} {cache : QueryCache HashSpec} {c : OracleComp HashSpec α}
    {f : α → OracleComp HashSpec β} (h : Res cache (c >>= f)) : Res cache c := by
  obtain ⟨v, hv⟩ := h
  obtain ⟨a, ha, -⟩ := hv.of_bind
  exact ⟨a, ha⟩

theorem treeNode_children {cache : QueryCache HashSpec} {parameter : PublicParameter}
    {secret : LeafIndex → ChainIndex → Digest} {levels : Nat} {node : MerkleNode}
    (h : Res cache (Concrete.treeNode parameter secret (levels + 1) node : OracleComp HashSpec Digest))
    (right : Bool) :
    Res cache (Concrete.treeNode parameter secret levels (Concrete.childNode node right) :
      OracleComp HashSpec Digest) := by
  obtain ⟨v, hv⟩ := h
  rw [Concrete.treeNode_succ_eq] at hv
  obtain ⟨left, hleft, hv⟩ := hv.of_bind
  obtain ⟨rightValue, hright, -⟩ := hv.of_bind
  cases right
  · exact ⟨left, hleft⟩
  · exact ⟨rightValue, hright⟩

theorem topTreeNode_children {cache : QueryCache HashSpec} {parameter : PublicParameter}
    {topSecret : TopIndex → ChainIndex → Digest} {levels : Nat} {node : TopNode}
    (h : Res cache (Concrete.topTreeNode parameter topSecret (levels + 1) node : OracleComp HashSpec Digest))
    (right : Bool) :
    Res cache (Concrete.topTreeNode parameter topSecret levels (Concrete.topChildNode node right) :
      OracleComp HashSpec Digest) := by
  obtain ⟨v, hv⟩ := h
  rw [Concrete.topTreeNode] at hv
  obtain ⟨left, hleft, hv⟩ := hv.of_bind
  obtain ⟨rightValue, hright, -⟩ := hv.of_bind
  cases right
  · exact ⟨left, hleft⟩
  · exact ⟨rightValue, hright⟩

theorem merkleNodeOfNat_child (j : Nat) :
    Concrete.merkleNodeOfNat j = Concrete.childNode (Concrete.merkleNodeOfNat (j / 2)) (j % 2 == 1) := by
  apply Fin.ext
  simp only [Concrete.merkleNodeOfNat, Concrete.childNode, lifetime, treeHeight]
  rcases Nat.mod_two_eq_zero_or_one j with h | h <;> simp [h] <;> omega

theorem topNodeOfNat_child (j : Nat) :
    Concrete.topNodeOfNat j = Concrete.topChildNode (Concrete.topNodeOfNat (j / 2)) (j % 2 == 1) := by
  apply Fin.ext
  simp only [Concrete.topNodeOfNat, Concrete.topChildNode, topLifetime, treeHeight]
  rcases Nat.mod_two_eq_zero_or_one j with h | h <;> simp [h] <;> omega

namespace Prepared

variable {seed : MasterSeed} {d : Derivations}
  {result : (Digest × (TopIndex → Option (Randomness × Encoding))) × QueryLog HashSpec}
  {cache : QueryCache HashSpec}

theorem steps (h : Prepared seed d result cache) :
    Resolves cache (Concrete.sequenceFin fun key => do
        let bottomRoot ← Concrete.treeNode d.parameter d.secret treeHeight (Concrete.bottomRootNode key)
        let base ← (pure (d.topBase key bottomRoot) : OracleComp HashSpec Randomness)
        Concrete.topSignFrom d.parameter key bottomRoot base signingAttemptLimit 0) result.1.2 ∧
      Resolves cache (Concrete.topTreeNode d.parameter d.topSecret treeHeight Concrete.rootNode) result.1.1 := by
  have hres := h.resolves
  unfold honestRun Concrete.honestKeygen at hres
  obtain ⟨ts, hts, hrest⟩ := hres.of_bind
  obtain ⟨root, hroot, hpure⟩ := hrest.of_bind
  have heq := hpure.pure_inv
  rw [← heq]
  exact ⟨hts, hroot⟩

theorem bottomRoot (h : Prepared seed d result cache) (key : TopIndex) :
    Res cache (Concrete.treeNode d.parameter d.secret treeHeight (Concrete.bottomRootNode key) :
      OracleComp HashSpec Digest) :=
  Res.of_bind ⟨_, h.steps.1.of_sequenceFin key⟩

theorem tree_res (h : Prepared seed d result cache) (m : Nat) (hm : m ≤ 16) (j : Nat)
    (hj : j < 2 ^ (16 + m)) :
    Res cache (Concrete.treeNode d.parameter d.secret (16 - m) (Concrete.merkleNodeOfNat j) :
      OracleComp HashSpec Digest) := by
  induction m generalizing j with
  | zero =>
      have hj' : j < topLifetime := by simp only [topLifetime, treeHeight]; simpa using hj
      have hnode : Concrete.merkleNodeOfNat j = Concrete.bottomRootNode ⟨j, hj'⟩ := by
        apply Fin.ext
        simp only [Concrete.merkleNodeOfNat, Concrete.bottomRootNode, lifetime, treeHeight]
        omega
      rw [hnode]
      exact h.bottomRoot _
  | succ m ih =>
      have hparent := ih (by omega) (j / 2) (Nat.div_lt_of_lt_mul (by
        rw [show 16 + (m + 1) = 16 + m + 1 by omega, pow_succ] at hj
        omega))
      rw [show 16 - m = 16 - (m + 1) + 1 by omega] at hparent
      rw [merkleNodeOfNat_child j]
      exact treeNode_children hparent _

theorem top_res (h : Prepared seed d result cache) (m : Nat) (hm : m ≤ 16) (j : Nat) (hj : j < 2 ^ m) :
    Res cache (Concrete.topTreeNode d.parameter d.topSecret (16 - m) (Concrete.topNodeOfNat j) :
      OracleComp HashSpec Digest) := by
  induction m generalizing j with
  | zero =>
      have hj0 : j = 0 := by simpa using hj
      subst hj0
      exact ⟨_, h.steps.2⟩
  | succ m ih =>
      have hparent := ih (by omega) (j / 2) (Nat.div_lt_of_lt_mul (by
        rw [pow_succ] at hj
        omega))
      rw [show 16 - m = 16 - (m + 1) + 1 by omega] at hparent
      rw [topNodeOfNat_child j]
      exact topTreeNode_children hparent _

/-! ## Values -/

theorem tree (h : Prepared seed d result cache) (level : Nat) (hlevel : level ≤ 16) (j : Nat)
    (hj : j < 2 ^ (32 - level)) :
    Resolves cache (Concrete.treeNode d.parameter d.secret level (Concrete.merkleNodeOfNat j))
      ((modelSecretKey d result).treeValue ⟨level, by simp [treeHeight]; omega⟩ (Concrete.merkleNodeOfNat j)) := by
  have hres := h.tree_res (16 - level) (by omega) j (by
    rw [show 16 + (16 - level) = 32 - level by omega]
    exact hj)
  rw [show 16 - (16 - level) = level by omega] at hres
  obtain ⟨v, hv⟩ := hres
  have hval := h.replay_eq (treeNode_tweakable _ _ _ _) hv
  simp only [modelSecretKey, Concrete.precomputedSecretKey]
  rw [hval]
  exact hv

theorem topTree (h : Prepared seed d result cache) (level : Nat) (hlevel : level ≤ 16) (j : Nat)
    (hj : j < 2 ^ (16 - level)) :
    Resolves cache (Concrete.topTreeNode d.parameter d.topSecret level (Concrete.topNodeOfNat j))
      ((modelSecretKey d result).topTreeValue ⟨level, by simp [treeHeight]; omega⟩ (Concrete.topNodeOfNat j)) := by
  have hres := h.top_res (16 - level) (by omega) j hj
  rw [show 16 - (16 - level) = level by omega] at hres
  obtain ⟨v, hv⟩ := hres
  have hval := h.replay_eq (topTreeNode_tweakable _ _ _ _) hv
  simp only [modelSecretKey, Concrete.precomputedSecretKey]
  rw [hval]
  exact hv

theorem chain (h : Prepared seed d result cache) (index : LeafIndex) (chain : ChainIndex) (digit : Digit) :
    Resolves cache (Concrete.chainWalk d.parameter index chain 0 digit.val (d.secret index chain))
      ((modelSecretKey d result).chainValue index chain digit) := by
  have hleaf := h.tree 0 (by omega) index.val (lt_of_lt_of_eq index.isLt (by norm_num [lifetime, treeHeight]))
  have hnode : Concrete.merkleNodeOfNat index.val = index := by
    apply Fin.ext
    simp [Concrete.merkleNodeOfNat, Nat.mod_eq_of_lt index.isLt]
  rw [hnode, Concrete.treeNode_zero_eq] at hleaf
  obtain ⟨endpoints, hendpoints, -⟩ := hleaf.of_bind
  have hfull := hendpoints.of_sequenceFin chain
  have hsplit := chainWalk_split d.parameter index chain 0 digit.val (chainLength - 1 - digit.val)
    (d.secret index chain)
  have hd : digit.val + (chainLength - 1 - digit.val) = chainLength - 1 := by
    have := digit.isLt
    simp only [chainLength, winternitzBits] at this ⊢
    omega
  rw [hd] at hsplit
  rw [hsplit] at hfull
  obtain ⟨v, hv, -⟩ := hfull.of_bind
  have hval := h.replay_eq (chainWalk_tweakable _ _ _ _ _ _) hv
  simp only [modelSecretKey, Concrete.precomputedSecretKey]
  rw [hval]
  exact hv

theorem topChain (h : Prepared seed d result cache) (key : TopIndex) (chain : ChainIndex) (digit : Digit) :
    Resolves cache (Concrete.topChainWalk d.parameter key chain 0 digit.val (d.topSecret key chain))
      ((modelSecretKey d result).topChainValue key chain digit) := by
  have hleaf := h.topTree 0 (by omega) key.val (lt_of_lt_of_eq key.isLt (by norm_num [topLifetime, treeHeight]))
  have hnode : Concrete.topNodeOfNat key.val = key := by
    apply Fin.ext
    simp [Concrete.topNodeOfNat, Nat.mod_eq_of_lt key.isLt]
  rw [hnode, Concrete.topTreeNode] at hleaf
  obtain ⟨endpoints, hendpoints, -⟩ := hleaf.of_bind
  have hfull := hendpoints.of_sequenceFin chain
  have hsplit := topChainWalk_split d.parameter key chain 0 digit.val (chainLength - 1 - digit.val)
    (d.topSecret key chain)
  have hd : digit.val + (chainLength - 1 - digit.val) = chainLength - 1 := by
    have := digit.isLt
    simp only [chainLength, winternitzBits] at this ⊢
    omega
  rw [hd] at hsplit
  rw [hsplit] at hfull
  obtain ⟨v, hv, -⟩ := hfull.of_bind
  have hval := h.replay_eq (topChainWalk_tweakable _ _ _ _ _ _) hv
  simp only [modelSecretKey, Concrete.precomputedSecretKey]
  rw [hval]
  exact hv

/-- The bottom root of tree `b` the key stores. -/
noncomputable def root (_h : Prepared seed d result cache) (key : TopIndex) : Digest :=
  (modelSecretKey d result).treeValue ⟨16, by simp [treeHeight]⟩ (Concrete.bottomRootNode key)

theorem bottomRootNode_eq (key : TopIndex) :
    Concrete.bottomRootNode key = Concrete.merkleNodeOfNat key.val := by
  apply Fin.ext
  have := key.isLt
  simp only [Concrete.bottomRootNode, Concrete.merkleNodeOfNat, lifetime, topLifetime, treeHeight] at this ⊢
  omega

theorem topSign (h : Prepared seed d result cache) (key : TopIndex) :
    Resolves cache (Concrete.topSignFrom d.parameter key (h.root key) (d.topBase key (h.root key))
      signingAttemptLimit 0) (result.1.2 key) := by
  have hstep := h.steps.1.of_sequenceFin key
  obtain ⟨r, hr, hrest⟩ := hstep.of_bind
  have hroot := h.tree 16 le_rfl key.val (by simp [topLifetime, treeHeight])
  rw [← bottomRootNode_eq] at hroot
  have hreq : r = h.root key := hr.unique hroot
  subst hreq
  obtain ⟨base, hbase, hsign⟩ := hrest.of_bind
  rw [← hbase.pure_inv] at hsign
  exact hsign

theorem rootValue (h : Prepared seed d result cache) :
    (modelSecretKey d result).topTreeValue ⟨16, by simp [treeHeight]⟩ Concrete.rootNode = result.1.1 := by
  have hv := h.steps.2
  have hval := h.replay_eq (topTreeNode_tweakable _ _ _ _) hv
  simp only [modelSecretKey, Concrete.precomputedSecretKey]
  exact hval

end Prepared

end XmssSecurity.Bridge
