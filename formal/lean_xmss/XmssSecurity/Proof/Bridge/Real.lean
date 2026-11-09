module

public import XmssSecurity.Proof.Bridge.Resolution
public import Common.WithHash

@[expose] public section

/-!
# The real scheme's honest computations

With every derivation programmed, a real tree node is the model's node with the derivation queries
erased. The real key generation makes exactly `K = 13,434,881` hash calls: the seed hash, then
`K - 1` from the scheme's seed `S`.
-/

open OracleComp OracleSpec

namespace XmssSecurity.Bridge

open Seeded DeterministicSigning

set_option backward.isDefEq.respectTransparency false

/-- The hash calls of the real key generation: the seed hash, the parameter and the top tree. -/
def keygenQueries : Nat := 2 + 2 ^ 16 * (29 + 174 + 1) + 2 ^ 16 - 1

theorem keygenQueries_eq : keygenQueries = 13434881 := by decide

/-- The real key generation from the scheme's seed `S`, after the seed hash. -/
def realKeygen (seed : MasterSeed) : OracleComp HashSpec (HashSig.PublicKey × LeanXmss.SchemeSeedKey) :=
  (do
    let parameter ← LeanXmss.deriveKey 0 .parameter seed
    let root ← LeanXmss.KeyGenerationAndSigning.treeNodeWithHash parameter LeanXmss.topLayer seed LeanXmss.layerHeight 0
    return (⟨root, parameter⟩, ⟨seed, parameter⟩) : OracleComp LeanXmss.HashSpec _)

theorem keygenFromSeed_eq (keySeed : MasterSeed) :
    LeanXmss.KeyGenerationAndSigning.keygenFromSeedWithHash keySeed =
      (LeanXmss.schemeSeed keySeed : OracleComp LeanXmss.HashSpec MasterSeed) >>= realKeygen := rfl

/-! ## Counts -/

theorem queryCount_oracleHash (x : HashInput) :
    QueryCount (Concrete.oracleHash x : OracleComp HashSpec HashOutput) 1 := by
  change QueryCount (liftM (HashSpec.query x) : OracleComp HashSpec HashOutput) 1
  rw [← bind_pure (liftM (HashSpec.query x) : OracleComp HashSpec HashOutput)]
  exact .query x _ 0 fun a => .pure a

theorem queryCount_realHash (parameter : PublicParameter) (domain : LeanXmss.HashDomain)
    (payload : HashInput) :
    QueryCount (LeanXmss.Verification.tweakableHashWithHash parameter domain payload :
      OracleComp LeanXmss.HashSpec HashSig.Digest) 1 := by
  unfold LeanXmss.Verification.tweakableHashWithHash LeanXmss.Verification.thWithHash
  have h := (queryCount_oracleHash (LeanXmss.tweakableHashInput parameter domain payload)).bind
    (f := fun output => (pure (HashSig.truncateHash output) : OracleComp HashSpec HashSig.Digest))
    fun _ => QueryCount.pure _
  exact h

theorem queryCount_realChainWalk (parameter : PublicParameter) (lay : LeanXmss.Layer)
    (key : LeanXmss.KeyIndex) (chain : ChainIndex) (start steps : Nat)
    (hsteps : start + steps ≤ chainLength - 1) (value : Digest) :
    QueryCount (LeanXmss.Verification.chainWalkWithHash parameter lay key chain start steps value :
      OracleComp LeanXmss.HashSpec HashSig.Digest) steps := by
  induction steps with
  | zero => exact .pure _
  | succ steps ih =>
      rw [LeanXmss.Verification.chainWalkWithHash]
      refine (ih (by omega)).bind fun previous => ?_
      rw [dite_eq_left (show start + steps < HashSig.chainLength - 1 by
        simp only [chainLength, winternitzBits, HashSig.chainLength, HashSig.winternitzBits] at hsteps ⊢
        omega)]
      exact queryCount_realHash _ _ _

theorem queryCount_otsSecrets (parameter : PublicParameter) (lay : LeanXmss.Layer)
    (key : LeanXmss.KeyIndex) (seed : MasterSeed) :
    QueryCount (LeanXmss.KeyGenerationAndSigning.otsSecretsWithHash parameter lay key seed :
      OracleComp LeanXmss.HashSpec (LeanXmss.ChainIndex → HashSig.Digest)) 29 := by
  unfold LeanXmss.KeyGenerationAndSigning.otsSecretsWithHash
  rw [sequenceFin_eq]
  have h := (QueryCount.sequenceFin (n := 1) fun pair : ChainPair =>
    queryCount_oracleHash (LeanXmss.keygenHashInput parameter (.oneTimeChainPair lay key pair)
        seed)).bind
      (f := fun outputs => (pure fun chainIdx : LeanXmss.ChainIndex =>
        LeanXmss.hashHalfForChain chainIdx.val (outputs (LeanXmss.chainPair chainIdx)) :
          OracleComp HashSpec (LeanXmss.ChainIndex → HashSig.Digest))) fun _ => QueryCount.pure _
  exact h

/-- The hash calls of a real node at `level`, its subtree's one-time keys included. -/
def nodeQueries (level : Nat) : Nat := 2 ^ level * (29 + 174 + 1) + 2 ^ level - 1

theorem queryCount_realTreeNode (parameter : PublicParameter) (lay : LeanXmss.Layer) (seed : MasterSeed)
    (level node : Nat) :
    QueryCount (LeanXmss.KeyGenerationAndSigning.treeNodeWithHash parameter lay seed level node :
      OracleComp LeanXmss.HashSpec HashSig.Digest) (nodeQueries level) := by
  induction level generalizing node with
  | zero =>
      rw [LeanXmss.KeyGenerationAndSigning.treeNodeWithHash]
      unfold LeanXmss.KeyGenerationAndSigning.oneTimePublicKeyWithHash
          LeanXmss.Verification.leafHashWithHash
      simp only [sequenceFin_eq, bind_assoc]
      rw [show nodeQueries 0 = 29 + (numChains * 3 + 1) by decide]
      refine (queryCount_otsSecrets parameter lay _ seed).bind fun secrets => ?_
      refine (QueryCount.sequenceFin fun chain => queryCount_realChainWalk parameter lay _ chain 0
        (HashSig.chainLength - 1) (by decide) (secrets chain)).bind fun endpoints => ?_
      exact queryCount_realHash _ _ _
  | succ level ih =>
      rw [LeanXmss.KeyGenerationAndSigning.treeNodeWithHash]
      have hcount : nodeQueries (level + 1) = nodeQueries level + (nodeQueries level + 1) := by
        simp only [nodeQueries, pow_succ]
        have : 1 ≤ 2 ^ level := Nat.one_le_two_pow
        omega
      rw [hcount]
      exact (ih (2 * node)).bind fun _ => (ih (2 * node + 1)).bind fun _ => queryCount_realHash _ _ _

theorem queryCount_realKeygen (seed : MasterSeed) :
    QueryCount (realKeygen seed) (keygenQueries - 1) := by
  unfold realKeygen LeanXmss.deriveKey LeanXmss.Verification.thWithHash
  rw [bind_assoc, show keygenQueries - 1 = 1 + (0 + (nodeQueries LeanXmss.layerHeight + 0)) by decide]
  refine (queryCount_oracleHash _).bind fun output => (QueryCount.pure _).bind fun parameter => ?_
  exact (queryCount_realTreeNode _ _ _ _ _).bind fun _ => .pure _

/-! ## Erasing the derivations -/

theorem otsSecrets_bottom (seed : MasterSeed) (d : Derivations) (index : LeafIndex) :
    Resolves (progCache seed d) (LeanXmss.KeyGenerationAndSigning.otsSecretsWithHash d.parameter LeanXmss.bottomLayer index seed :
      OracleComp LeanXmss.HashSpec (LeanXmss.ChainIndex → HashSig.Digest)) (d.secret index) := by
  unfold LeanXmss.KeyGenerationAndSigning.otsSecretsWithHash
  rw [sequenceFin_eq]
  refine (Resolves.sequenceFin (v := fun pair => d.bottom (index, pair)) fun pair => ?_).bind (.pure _)
  have h := progCache_bottom seed d (index, pair)
  change Resolves _ (liftM (HashSpec.query (bottomInput d.parameter seed (index, pair))) :
    OracleComp HashSpec HashOutput) _
  rw [← bind_pure (liftM (HashSpec.query _) : OracleComp HashSpec HashOutput)]
  exact .query _ _ h _ _ (.pure _)

theorem otsSecrets_top (seed : MasterSeed) (d : Derivations) (key : TopIndex) :
    Resolves (progCache seed d) (LeanXmss.KeyGenerationAndSigning.otsSecretsWithHash d.parameter LeanXmss.topLayer (topKey key) seed :
      OracleComp LeanXmss.HashSpec (LeanXmss.ChainIndex → HashSig.Digest)) (d.topSecret key) := by
  unfold LeanXmss.KeyGenerationAndSigning.otsSecretsWithHash
  rw [sequenceFin_eq]
  refine (Resolves.sequenceFin (v := fun pair => d.top (key, pair)) fun pair => ?_).bind (.pure _)
  have h := progCache_top seed d (key, pair)
  change Resolves _ (liftM (HashSpec.query (topInput d.parameter seed (key, pair))) :
    OracleComp HashSpec HashOutput) _
  rw [← bind_pure (liftM (HashSpec.query _) : OracleComp HashSpec HashOutput)]
  exact .query _ _ h _ _ (.pure _)

theorem leafKey_bottom (j : Nat) :
    (⟨j % LeanXmss.lifetime, Nat.mod_lt _ (by decide)⟩ : LeanXmss.KeyIndex) = Concrete.merkleNodeOfNat j := by
  apply Fin.ext
  simp [Concrete.merkleNodeOfNat, LeanXmss.lifetime, lifetime, LeanXmss.layerCount, LeanXmss.layerHeight,
    treeHeight]

theorem leafKey_top (j : Nat) (hj : j < 2 ^ 16) :
    (⟨j % LeanXmss.lifetime, Nat.mod_lt _ (by decide)⟩ : LeanXmss.KeyIndex) =
      topKey (Concrete.topNodeOfNat j) := by
  apply Fin.ext
  simp only [topKey, Concrete.topNodeOfNat, LeanXmss.lifetime, LeanXmss.layerCount, LeanXmss.layerHeight,
    topLifetime, treeHeight]
  omega

/-- A real bottom node is the model's with its derivations erased. -/
theorem erases_treeNode_bottom (seed : MasterSeed) (d : Derivations) (level : Nat) (hlevel : level ≤ 16)
    (j : Nat) (hj : j < 2 ^ (32 - level)) :
    Erases (progCache seed d) (LeanXmss.KeyGenerationAndSigning.treeNodeWithHash d.parameter LeanXmss.bottomLayer seed level j :
        OracleComp LeanXmss.HashSpec HashSig.Digest)
      (Concrete.treeNode d.parameter d.secret level (Concrete.merkleNodeOfNat j)) := by
  induction level generalizing j with
  | zero =>
      rw [LeanXmss.KeyGenerationAndSigning.treeNode_eq_zero, Concrete.treeNode_zero_eq,
          leafKey_bottom j]
      unfold LeanXmss.KeyGenerationAndSigning.oneTimePublicKeyWithHash Concrete.leafAt
          Concrete.oneTimePublicKey
      rw [bind_assoc]
      apply (erases_pure_of_resolves (otsSecrets_bottom seed d _)).bind_known
      simp only [sequenceFin_eq, chainWalk_bottom, leafHash_bottom]
      exact .refl _ _
  | succ level ih =>
      rw [LeanXmss.KeyGenerationAndSigning.treeNode_eq_succ, Concrete.treeNode_succ_eq]
      simp only [dite_eq_left (show level < treeHeight by simp only [treeHeight]; omega)]
      have hj2 : 2 * j + 1 < 2 ^ (32 - level) := by
        rw [show 32 - level = 32 - (level + 1) + 1 by omega, pow_succ]
        omega
      have hjlt : j < 4294967296 := by
        have := lt_of_lt_of_le hj (Nat.pow_le_pow_right (by decide) (show 32 - (level + 1) ≤ 32 by omega))
        simpa using this
      have hleft : Concrete.childNode (Concrete.merkleNodeOfNat j) false = Concrete.merkleNodeOfNat (2 * j) := by
        apply Fin.ext
        simp [Concrete.childNode, Concrete.merkleNodeOfNat, lifetime, treeHeight, Nat.mod_eq_of_lt hjlt]
      have hright : Concrete.childNode (Concrete.merkleNodeOfNat j) true =
          Concrete.merkleNodeOfNat (2 * j + 1) := by
        apply Fin.ext
        simp [Concrete.childNode, Concrete.merkleNodeOfNat, lifetime, treeHeight, Nat.mod_eq_of_lt hjlt]
      rw [hleft, hright]
      refine (ih (by omega) (2 * j) (by omega)).bind _ _ fun left =>
        (ih (by omega) (2 * j + 1) hj2).bind _ _ fun right => ?_
      have hnode := nodeHash_bottom d.parameter ⟨level, by simp only [treeHeight]; omega⟩
        (Concrete.merkleNodeOfNat j) left right
      have hval : (Concrete.merkleNodeOfNat j).val = j := by
        simp [Concrete.merkleNodeOfNat, lifetime, treeHeight, Nat.mod_eq_of_lt hjlt]
      rw [hval] at hnode
      rw [← hnode]
      exact .refl _ _

/-- A real top node is the model's with its derivations erased. -/
theorem erases_treeNode_top (seed : MasterSeed) (d : Derivations) (level : Nat) (hlevel : level ≤ 16)
    (j : Nat) (hj : j < 2 ^ (16 - level)) :
    Erases (progCache seed d) (LeanXmss.KeyGenerationAndSigning.treeNodeWithHash d.parameter LeanXmss.topLayer seed level j :
        OracleComp LeanXmss.HashSpec HashSig.Digest)
      (Concrete.topTreeNode d.parameter d.topSecret level (Concrete.topNodeOfNat j)) := by
  induction level generalizing j with
  | zero =>
      rw [LeanXmss.KeyGenerationAndSigning.treeNode_eq_zero, Concrete.topTreeNode, leafKey_top j
          (by simpa using hj)]
      unfold LeanXmss.KeyGenerationAndSigning.oneTimePublicKeyWithHash Concrete.topLeafAt Concrete.topOneTimePublicKey
      rw [bind_assoc]
      apply (erases_pure_of_resolves (otsSecrets_top seed d _)).bind_known
      simp only [sequenceFin_eq, chainWalk_top, leafHash_top]
      exact .refl _ _
  | succ level ih =>
      rw [LeanXmss.KeyGenerationAndSigning.treeNode_eq_succ, Concrete.topTreeNode]
      simp only [dite_eq_left (show level < treeHeight by simp only [treeHeight]; omega)]
      have hj2 : 2 * j + 1 < 2 ^ (16 - level) := by
        rw [show 16 - level = 16 - (level + 1) + 1 by omega, pow_succ]
        omega
      have hjlt : j < 65536 := by
        have := lt_of_lt_of_le hj (Nat.pow_le_pow_right (by decide) (show 16 - (level + 1) ≤ 16 by omega))
        simpa using this
      have hleft : Concrete.topChildNode (Concrete.topNodeOfNat j) false = Concrete.topNodeOfNat (2 * j) := by
        apply Fin.ext
        simp [Concrete.topChildNode, Concrete.topNodeOfNat, topLifetime, treeHeight, Nat.mod_eq_of_lt hjlt]
      have hright : Concrete.topChildNode (Concrete.topNodeOfNat j) true =
          Concrete.topNodeOfNat (2 * j + 1) := by
        apply Fin.ext
        simp [Concrete.topChildNode, Concrete.topNodeOfNat, topLifetime, treeHeight, Nat.mod_eq_of_lt hjlt]
      rw [hleft, hright]
      refine (ih (by omega) (2 * j) (by omega)).bind _ _ fun left =>
        (ih (by omega) (2 * j + 1) hj2).bind _ _ fun right => ?_
      have hnode := nodeHash_top d.parameter ⟨level, by simp only [treeHeight]; omega⟩
        (Concrete.topNodeOfNat j) left right
      have hval : (Concrete.topNodeOfNat j).val = j := by
        simp [Concrete.topNodeOfNat, topLifetime, treeHeight, Nat.mod_eq_of_lt hjlt]
      rw [hval] at hnode
      rw [← hnode]
      exact .refl _ _

/-! ## Under the prepared cache -/

namespace Prepared

variable {seed : MasterSeed} {d : Derivations}
  {result : (Digest × (TopIndex → Option (Randomness × Encoding))) × QueryLog HashSpec}
  {cache : QueryCache HashSpec}

theorem realBottomNode (h : Prepared seed d result cache) (level : Nat) (hlevel : level ≤ 16) (j : Nat)
    (hj : j < 2 ^ (32 - level)) :
    Resolves cache (LeanXmss.KeyGenerationAndSigning.treeNodeWithHash d.parameter
        LeanXmss.bottomLayer seed level j :
        OracleComp LeanXmss.HashSpec HashSig.Digest)
      ((modelSecretKey d result).treeValue ⟨level, by simp [treeHeight]; omega⟩ (Concrete.merkleNodeOfNat j)) :=
  (erases_treeNode_bottom seed d level hlevel j hj).resolves h.prog_le (h.tree level hlevel j hj)

theorem realTopNode (h : Prepared seed d result cache) (level : Nat) (hlevel : level ≤ 16) (j : Nat)
    (hj : j < 2 ^ (16 - level)) :
    Resolves cache (LeanXmss.KeyGenerationAndSigning.treeNodeWithHash d.parameter LeanXmss.topLayer
        seed level j :
        OracleComp LeanXmss.HashSpec HashSig.Digest)
      ((modelSecretKey d result).topTreeValue ⟨level, by simp [treeHeight]; omega⟩ (Concrete.topNodeOfNat j)) :=
  (erases_treeNode_top seed d level hlevel j hj).resolves h.prog_le (h.topTree level hlevel j hj)

/-- The real key generation from `S` resolves to the model's public key. -/
theorem realKeygen (h : Prepared seed d result cache) :
    Resolves cache (Bridge.realKeygen seed)
      ((⟨result.1.1, d.parameter⟩ : HashSig.PublicKey), (⟨seed, d.parameter⟩ : LeanXmss.SchemeSeedKey)) := by
  unfold Bridge.realKeygen LeanXmss.deriveKey LeanXmss.Verification.thWithHash
  rw [bind_assoc]
  have hparam : cache (paramInput seed) = some d.param := h.prog_le (progCache_param seed d)
  change Resolves cache (liftM (HashSpec.query (paramInput seed)) >>= _) _
  refine .query _ _ hparam _ _ ?_
  rw [pure_bind]
  have hroot := h.realTopNode 16 le_rfl 0 (by decide)
  have hnode : Concrete.topNodeOfNat 0 = Concrete.rootNode := rfl
  rw [hnode, h.rootValue] at hroot
  exact hroot.bind (.pure _)

end Prepared

end XmssSecurity.Bridge
