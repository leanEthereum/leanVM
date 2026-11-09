module

public import XmssSecurity.Proof.CacheReplayEval
public import Mathlib.Data.Nat.Bitwise

@[expose] public section

open OracleSpec

namespace XmssSecurity.Concrete.CacheReplay

def pathNode (leafIndex : LeafIndex) (level : Nat) : MerkleNode :=
  Concrete.merkleNodeOfNat (leafIndex.val / 2 ^ level)

@[simp]
theorem pathNode_zero (leafIndex : LeafIndex) : pathNode leafIndex 0 = leafIndex := by
  apply Fin.ext
  simp only [pathNode, Concrete.merkleNodeOfNat, pow_zero, Nat.div_one]
  exact Nat.mod_eq_of_lt leafIndex.isLt

theorem testBit_div_pow (value level : Nat) :
    (value / 2 ^ level).testBit 0 = value.testBit level := by
  simpa only [Nat.zero_add] using (Nat.testBit_add value 0 level).symm

theorem div_pow_succ (value level : Nat) :
    value / 2 ^ (level + 1) = (value / 2 ^ level) / 2 := by
  rw [pow_succ, Nat.div_div_eq_div_mul]

private theorem even_parts (value : Nat) (hbit : value.testBit 0 = false) :
    value = 2 * (value / 2) ∧ value ^^^ 1 = 2 * (value / 2) + 1 := by
  have heven : Even value := Nat.even_iff.mpr
    (Nat.mod_two_eq_zero_iff_testBit_zero.mpr hbit)
  constructor
  · have h := Nat.bit_testBit_zero_shiftRight_one value
    rw [hbit, Nat.bit_false, Nat.shiftRight_one] at h
    exact h.symm
  · rw [Nat.xor_one_of_even heven]
    have h := Nat.bit_testBit_zero_shiftRight_one value
    rw [hbit, Nat.bit_false, Nat.shiftRight_one] at h
    exact congrArg (fun current => current + 1) h.symm

private theorem odd_parts (value : Nat) (hbit : value.testBit 0 = true) :
    value = 2 * (value / 2) + 1 ∧ value ^^^ 1 = 2 * (value / 2) := by
  have hodd : Odd value := Nat.odd_iff.mpr
    (Nat.mod_two_eq_one_iff_testBit_zero.mpr hbit)
  constructor
  · have h := Nat.bit_testBit_zero_shiftRight_one value
    rw [hbit, Nat.bit_true, Nat.shiftRight_one] at h
    exact h.symm
  · rw [Nat.xor_one_of_odd hodd]
    have h := Nat.bit_testBit_zero_shiftRight_one value
    rw [hbit, Nat.bit_true, Nat.shiftRight_one] at h
    calc
      value - 1 = (2 * (value / 2) + 1) - 1 :=
        congrArg (fun current => current - 1) h.symm
      _ = 2 * (value / 2) := by omega

theorem nodeIndex_eq_pathNode_succ (leafIndex : LeafIndex) (level : Nat) :
    CacheView.nodeIndex leafIndex level = pathNode leafIndex (level + 1) := by
  apply Fin.ext
  simp only [CacheView.nodeIndex, Concrete.nodeIndex, pathNode, Concrete.merkleNodeOfNat]
  exact (Nat.mod_eq_of_lt
    ((Nat.div_le_self leafIndex.val _).trans_lt leafIndex.isLt)).symm

theorem pathNode_children (leafIndex : LeafIndex) (level : Nat) (hlevel : level < treeHeight) :
    if leafIndex.val.testBit level then
      Concrete.childNode (pathNode leafIndex (level + 1)) false =
          Concrete.authenticationPathNode leafIndex ⟨level, hlevel⟩ ∧
        Concrete.childNode (pathNode leafIndex (level + 1)) true = pathNode leafIndex level
    else
      Concrete.childNode (pathNode leafIndex (level + 1)) false = pathNode leafIndex level ∧
        Concrete.childNode (pathNode leafIndex (level + 1)) true =
          Concrete.authenticationPathNode leafIndex ⟨level, hlevel⟩ := by
  let quotient := leafIndex.val / 2 ^ level
  have hquotient : quotient < lifetime :=
    (Nat.div_le_self leafIndex.val _).trans_lt leafIndex.isLt
  have hparent : (pathNode leafIndex (level + 1)).val = quotient / 2 := by
    simp only [pathNode, Concrete.merkleNodeOfNat]
    rw [div_pow_succ]
    exact Nat.mod_eq_of_lt
      ((Nat.div_le_self (leafIndex.val / 2 ^ level) _).trans_lt hquotient)
  have hcurrent : (pathNode leafIndex level).val = quotient := by
    simp [pathNode, Concrete.merkleNodeOfNat, quotient,
      Nat.mod_eq_of_lt hquotient]
  have hauth :
      (Concrete.authenticationPathNode leafIndex ⟨level, hlevel⟩).val =
        (quotient ^^^ 1) % lifetime := by
    rfl
  have hquotientBit : quotient.testBit 0 = leafIndex.val.testBit level := by
    exact testBit_div_pow leafIndex.val level
  by_cases hbit : leafIndex.val.testBit level = true
  · simp only [hbit, ↓reduceIte]
    obtain ⟨hcurrentParts, hauthParts⟩ := odd_parts quotient (hquotientBit.trans hbit)
    constructor
    · apply Fin.ext
      rw [hauth]
      simp only [Concrete.childNode, Concrete.merkleNodeOfNat, Bool.false_eq_true,
        ↓reduceIte, hparent]
      exact congrArg (fun value => value % lifetime) hauthParts.symm

    · apply Fin.ext
      rw [hcurrent]
      simp only [Concrete.childNode, Concrete.merkleNodeOfNat, ↓reduceIte, hparent]
      calc
        (2 * (quotient / 2) + 1) % lifetime = quotient % lifetime :=
          congrArg (fun value => value % lifetime) hcurrentParts.symm
        _ = quotient := Nat.mod_eq_of_lt hquotient
  · have hbitFalse : leafIndex.val.testBit level = false := Bool.eq_false_of_not_eq_true hbit
    simp only [hbitFalse, Bool.false_eq_true, ↓reduceIte]
    obtain ⟨hcurrentParts, hauthParts⟩ := even_parts quotient
      (hquotientBit.trans hbitFalse)
    constructor
    · apply Fin.ext
      rw [hcurrent]
      simp only [Concrete.childNode, Concrete.merkleNodeOfNat, Bool.false_eq_true,
        ↓reduceIte, hparent]
      calc
        (2 * (quotient / 2) + 0) % lifetime = quotient % lifetime :=
          congrArg (fun value => value % lifetime) (by omega :
            2 * (quotient / 2) + 0 = quotient)
        _ = quotient := Nat.mod_eq_of_lt hquotient
    · apply Fin.ext
      rw [hauth]
      simp only [Concrete.childNode, Concrete.merkleNodeOfNat, ↓reduceIte, hparent]
      exact congrArg (fun value => value % lifetime) hauthParts.symm

theorem authentication_step_eq_treeNode (cache : QueryCache HashSpec)
    (parameter : PublicParameter) (secret : LeafIndex → ChainIndex → Digest)
    (leafIndex : LeafIndex) (level : Nat) (hlevel : level < treeHeight) :
    CacheView.nodeHash cache parameter leafIndex level
        (treeNode cache parameter secret level (pathNode leafIndex level))
        (treeNode cache parameter secret level
          (Concrete.authenticationPathNode leafIndex ⟨level, hlevel⟩)) =
      treeNode cache parameter secret (level + 1) (pathNode leafIndex (level + 1)) := by
  have hnode := nodeIndex_eq_pathNode_succ leafIndex level
  have hchildren := pathNode_children leafIndex level hlevel
  by_cases hbit : leafIndex.val.testBit level = true
  · simp only [hbit, ↓reduceIte] at hchildren
    rcases hchildren with ⟨hleft, hright⟩
    simp [CacheView.nodeHash, hlevel, CacheView.nodeInput,
      CacheView.authenticationNodePayload, CacheView.merkleHash,
      CacheView.merkleInput, treeNode_succ_eq, hbit, hnode, hleft, hright]
  · have hbitFalse : leafIndex.val.testBit level = false := Bool.eq_false_of_not_eq_true hbit
    simp only [hbitFalse, Bool.false_eq_true, ↓reduceIte] at hchildren
    rcases hchildren with ⟨hleft, hright⟩
    simp [CacheView.nodeHash, hlevel, CacheView.nodeInput,
      CacheView.authenticationNodePayload, CacheView.merkleHash,
      CacheView.merkleInput, treeNode_succ_eq, hbitFalse, hnode, hleft, hright]

theorem recover_signedChainValues (cache : QueryCache HashSpec)
    (secretKey : SecretKey) (leafIndex : LeafIndex) (encoding : Encoding) :
    XmssSecurity.recoveredEndpoints
        (fun chain => CacheView.chainStep cache secretKey.parameter leafIndex chain)
        encoding (signedChainValues cache secretKey leafIndex encoding) =
      oneTimePublicKey cache secretKey.parameter secretKey.chainStart leafIndex := by
  funext chain
  exact Wots.recover_signChain_eq_publicChain
    (CacheView.chainStep cache secretKey.parameter leafIndex chain)
    (encoding chain) (secretKey.chainStart leafIndex chain)

theorem recoveredEndpoints_signWithEncoding (cache : QueryCache HashSpec)
    (secretKey : SecretKey) (leafIndex : LeafIndex) (randomness : Randomness)
    (encoding : Encoding) :
    XmssSecurity.recoveredEndpoints
        (fun chain => CacheView.chainStep cache secretKey.parameter leafIndex chain)
        encoding (signWithEncoding cache secretKey leafIndex randomness encoding).chainValue =
      oneTimePublicKey cache secretKey.parameter secretKey.chainStart leafIndex := by
  exact recover_signedChainValues cache secretKey leafIndex encoding

theorem leafHash_recovered_signWithEncoding (cache : QueryCache HashSpec)
    (secretKey : SecretKey) (leafIndex : LeafIndex) (randomness : Randomness)
    (encoding : Encoding) :
    CacheView.leafHash cache secretKey.parameter leafIndex
        (XmssSecurity.recoveredEndpoints
          (fun chain => CacheView.chainStep cache secretKey.parameter leafIndex chain)
          encoding (signWithEncoding cache secretKey leafIndex randomness encoding).chainValue) =
      leafAt cache secretKey.parameter secretKey.chainStart leafIndex := by
  rw [recoveredEndpoints_signWithEncoding]
  rfl

theorem authenticationPath_ascends_to_treeNode (cache : QueryCache HashSpec)
    (secretKey : SecretKey) (leafIndex : LeafIndex) (randomness : Randomness)
    (encoding : Encoding) (levels : Nat) (hlevels : levels ≤ treeHeight) :
    Merkle.ascend (CacheView.nodeHash cache secretKey.parameter leafIndex)
        (Concrete.signaturePath
          (signWithEncoding cache secretKey leafIndex randomness encoding))
        0 levels (leafAt cache secretKey.parameter secretKey.chainStart leafIndex) =
      treeNode cache secretKey.parameter secretKey.chainStart levels
        (pathNode leafIndex levels) := by
  induction levels with
  | zero => simp [Merkle.ascend]
  | succ level ih =>
      have hlevel : level < treeHeight := Nat.lt_of_succ_le hlevels
      rw [Merkle.ascend, ih (Nat.le_of_succ_le hlevels)]
      simp only [Nat.zero_add]
      have hpath :
          Concrete.signaturePath
              (signWithEncoding cache secretKey leafIndex randomness encoding) level =
            treeNode cache secretKey.parameter secretKey.chainStart level
              (Concrete.authenticationPathNode leafIndex ⟨level, hlevel⟩) := by
        simp [Concrete.signaturePath, signWithEncoding, authenticationPath, hlevel]
      rw [hpath]
      exact authentication_step_eq_treeNode cache secretKey.parameter
        secretKey.chainStart leafIndex level hlevel

theorem authenticationPath_ascends_to_root (cache : QueryCache HashSpec)
    (secretKey : SecretKey) (leafIndex : LeafIndex) (randomness : Randomness)
    (encoding : Encoding) :
    Merkle.ascend (CacheView.nodeHash cache secretKey.parameter leafIndex)
        (Concrete.signaturePath
          (signWithEncoding cache secretKey leafIndex randomness encoding))
        0 treeHeight (leafAt cache secretKey.parameter secretKey.chainStart leafIndex) =
      Concrete.bottomRoot cache secretKey (topKeyOf leafIndex) := by
  rw [authenticationPath_ascends_to_treeNode cache secretKey leafIndex randomness encoding
    treeHeight le_rfl]
  unfold Concrete.bottomRoot
  congr 1
  apply Fin.ext
  simp only [pathNode, Concrete.bottomRootNode, topKeyOf, Concrete.merkleNodeOfNat]
  exact Nat.mod_eq_of_lt ((Nat.div_le_self leafIndex.val _).trans_lt leafIndex.isLt)

/-! ### The top layer -/

def topPathNodeAt (key : TopIndex) (level : Nat) : TopNode :=
  Concrete.topNodeOfNat (key.val / 2 ^ level)

@[simp]
theorem topPathNodeAt_zero (key : TopIndex) : topPathNodeAt key 0 = key := by
  apply Fin.ext
  simp only [topPathNodeAt, Concrete.topNodeOfNat, pow_zero, Nat.div_one]
  exact Nat.mod_eq_of_lt key.isLt

theorem topNodeIndex_eq_topPathNodeAt_succ (key : TopIndex) (level : Nat) :
    Concrete.topNodeIndex key level = topPathNodeAt key (level + 1) := by
  apply Fin.ext
  simp only [Concrete.topNodeIndex, topPathNodeAt, Concrete.topNodeOfNat]
  exact (Nat.mod_eq_of_lt ((Nat.div_le_self key.val _).trans_lt key.isLt)).symm

theorem topPathNode_children (key : TopIndex) (level : Nat) (hlevel : level < treeHeight) :
    if key.val.testBit level then
      Concrete.topChildNode (topPathNodeAt key (level + 1)) false =
          Concrete.topPathNode key ⟨level, hlevel⟩ ∧
        Concrete.topChildNode (topPathNodeAt key (level + 1)) true = topPathNodeAt key level
    else
      Concrete.topChildNode (topPathNodeAt key (level + 1)) false = topPathNodeAt key level ∧
        Concrete.topChildNode (topPathNodeAt key (level + 1)) true =
          Concrete.topPathNode key ⟨level, hlevel⟩ := by
  let quotient := key.val / 2 ^ level
  have hquotient : quotient < topLifetime := (Nat.div_le_self key.val _).trans_lt key.isLt
  have hparent : (topPathNodeAt key (level + 1)).val = quotient / 2 := by
    simp only [topPathNodeAt, Concrete.topNodeOfNat]
    rw [div_pow_succ]
    exact Nat.mod_eq_of_lt ((Nat.div_le_self (key.val / 2 ^ level) _).trans_lt hquotient)
  have hcurrent : (topPathNodeAt key level).val = quotient := by
    simp [topPathNodeAt, Concrete.topNodeOfNat, quotient, Nat.mod_eq_of_lt hquotient]
  have hauth : (Concrete.topPathNode key ⟨level, hlevel⟩).val = (quotient ^^^ 1) % topLifetime :=
    rfl
  have hquotientBit : quotient.testBit 0 = key.val.testBit level := testBit_div_pow key.val level
  by_cases hbit : key.val.testBit level = true
  · simp only [hbit, ↓reduceIte]
    obtain ⟨hcurrentParts, hauthParts⟩ := odd_parts quotient (hquotientBit.trans hbit)
    constructor
    · apply Fin.ext
      rw [hauth]
      simp only [Concrete.topChildNode, Concrete.topNodeOfNat, Bool.false_eq_true, ↓reduceIte,
        hparent]
      exact congrArg (fun value => value % topLifetime) hauthParts.symm
    · apply Fin.ext
      rw [hcurrent]
      simp only [Concrete.topChildNode, Concrete.topNodeOfNat, ↓reduceIte, hparent]
      rw [← hcurrentParts]
      exact Nat.mod_eq_of_lt hquotient
  · have hbitFalse : key.val.testBit level = false := Bool.eq_false_of_not_eq_true hbit
    simp only [hbitFalse, Bool.false_eq_true, ↓reduceIte]
    obtain ⟨hcurrentParts, hauthParts⟩ := even_parts quotient (hquotientBit.trans hbitFalse)
    constructor
    · apply Fin.ext
      rw [hcurrent]
      simp only [Concrete.topChildNode, Concrete.topNodeOfNat, Bool.false_eq_true, ↓reduceIte,
        hparent, Nat.add_zero]
      rw [← hcurrentParts]
      exact Nat.mod_eq_of_lt hquotient
    · apply Fin.ext
      rw [hauth]
      simp only [Concrete.topChildNode, Concrete.topNodeOfNat, ↓reduceIte, hparent]
      exact congrArg (fun value => value % topLifetime) hauthParts.symm

theorem top_authentication_step_eq_topTreeNode (cache : QueryCache HashSpec)
    (parameter : PublicParameter) (topSecret : TopIndex → ChainIndex → Digest)
    (key : TopIndex) (level : Nat) (hlevel : level < treeHeight) :
    CacheView.topNodeHash cache parameter key level
        (topTreeNode cache parameter topSecret level (topPathNodeAt key level))
        (topTreeNode cache parameter topSecret level (Concrete.topPathNode key ⟨level, hlevel⟩)) =
      topTreeNode cache parameter topSecret (level + 1) (topPathNodeAt key (level + 1)) := by
  have hnode := topNodeIndex_eq_topPathNodeAt_succ key level
  have hchildren := topPathNode_children key level hlevel
  by_cases hbit : key.val.testBit level = true
  · simp only [hbit, ↓reduceIte] at hchildren
    rcases hchildren with ⟨hleft, hright⟩
    simp [CacheView.topNodeHash, hlevel, CacheView.topNodeInput,
      CacheView.topAuthenticationNodePayload, CacheView.topMerkleHash,
      CacheView.topMerkleInput, topTreeNode_succ_eq, hbit, hnode, hleft, hright]
  · have hbitFalse : key.val.testBit level = false := Bool.eq_false_of_not_eq_true hbit
    simp only [hbitFalse, Bool.false_eq_true, ↓reduceIte] at hchildren
    rcases hchildren with ⟨hleft, hright⟩
    simp [CacheView.topNodeHash, hlevel, CacheView.topNodeInput,
      CacheView.topAuthenticationNodePayload, CacheView.topMerkleHash,
      CacheView.topMerkleInput, topTreeNode_succ_eq, hbitFalse, hnode, hleft, hright]

theorem honestTopPath_ascends_to_topTreeNode (cache : QueryCache HashSpec)
    (secretKey : SecretKey) (key : TopIndex) (levels : Nat) (hlevels : levels ≤ treeHeight) :
    Merkle.ascend (CacheView.topNodeHash cache secretKey.parameter key)
        (Concrete.honestTopPath cache secretKey key) 0 levels
        (topLeafAt cache secretKey.parameter secretKey.topChainStart key) =
      topTreeNode cache secretKey.parameter secretKey.topChainStart levels
        (topPathNodeAt key levels) := by
  induction levels with
  | zero => simp [Merkle.ascend, topTreeNode_zero_eq]
  | succ level ih =>
      have hlevel : level < treeHeight := Nat.lt_of_succ_le hlevels
      rw [Merkle.ascend, ih (Nat.le_of_succ_le hlevels)]
      simp only [Nat.zero_add, Concrete.honestTopPath, hlevel, ↓reduceDIte]
      exact top_authentication_step_eq_topTreeNode cache secretKey.parameter
        secretKey.topChainStart key level hlevel

/-- The honest top path ascends from the honest top leaf to the public root. -/
theorem honestTopPath_ascends_to_root (cache : QueryCache HashSpec)
    (secretKey : SecretKey) (key : TopIndex) :
    Merkle.ascend (CacheView.topNodeHash cache secretKey.parameter key)
        (Concrete.honestTopPath cache secretKey key) 0 treeHeight
        (topLeafAt cache secretKey.parameter secretKey.topChainStart key) =
      topTreeNode cache secretKey.parameter secretKey.topChainStart treeHeight
        Concrete.rootNode := by
  rw [honestTopPath_ascends_to_topTreeNode cache secretKey key treeHeight le_rfl]
  congr 1
  apply Fin.ext
  simp only [topPathNodeAt, Concrete.topNodeOfNat, Concrete.rootNode]
  have hkey : key.val < 2 ^ treeHeight := key.isLt
  rw [Nat.div_eq_of_lt hkey]
  rfl

theorem recover_honestTopValues (cache : QueryCache HashSpec) (secretKey : SecretKey)
    (key : TopIndex) (encoding : Encoding) :
    XmssSecurity.recoveredEndpoints
        (fun chain => CacheView.topChainStep cache secretKey.parameter key chain)
        encoding (Concrete.honestTopValues cache secretKey key encoding) =
      topOneTimePublicKey cache secretKey.parameter secretKey.topChainStart key := by
  funext chain
  exact Wots.recover_signChain_eq_publicChain
    (CacheView.topChainStep cache secretKey.parameter key chain)
    (encoding chain) (secretKey.topChainStart key chain)

theorem layerPath_topPartFromCache (cache : QueryCache HashSpec) (secretKey : SecretKey)
    (key : TopIndex) (randomness : Randomness) (encoding : Encoding)
    (hsigned : secretKey.topSigned key = some (randomness, encoding)) :
    topPartFromCache cache secretKey key =
        ⟨randomness, Concrete.honestTopValues cache secretKey key encoding,
          fun level => Concrete.honestTopPath cache secretKey key level.val⟩ ∧
      Concrete.layerPath (topPartFromCache cache secretKey key) =
        Concrete.honestTopPath cache secretKey key := by
  have hpart : topPartFromCache cache secretKey key =
      ⟨randomness, Concrete.honestTopValues cache secretKey key encoding,
        fun level => Concrete.honestTopPath cache secretKey key level.val⟩ := by
    unfold topPartFromCache
    rw [hsigned]
  refine ⟨hpart, ?_⟩
  rw [hpart]
  funext level
  by_cases hlevel : level < treeHeight
  · simp [Concrete.layerPath, hlevel]
  · simp [Concrete.layerPath, Concrete.honestTopPath, hlevel]

def publicKeyFromCache (cache : QueryCache HashSpec) (secretKey : SecretKey) : PublicKey :=
  ⟨topTreeNode cache secretKey.parameter secretKey.topChainStart treeHeight Concrete.rootNode,
    secretKey.parameter⟩

attribute [irreducible] publicKeyFromCache

theorem publicKey_eq_publicKeyFromCache (cache : QueryCache HashSpec)
    (secretKey : SecretKey) (root : Digest)
    (hroot : root = topTreeNode cache secretKey.parameter secretKey.topChainStart
      treeHeight Concrete.rootNode) :
    PublicKey.mk root secretKey.parameter = publicKeyFromCache cache secretKey := by
  rw [publicKeyFromCache]
  exact congrArg₂ PublicKey.mk hroot rfl

/-- The honest top signature of tree `b`, whose digest decodes in the cache, verifies on the honest
bottom root. -/
theorem verifyTopFromCache_topPart (cache : QueryCache HashSpec) (secretKey : SecretKey)
    (key : TopIndex) (randomness : Randomness) (encoding : Encoding)
    (hsigned : secretKey.topSigned key = some (randomness, encoding))
    (hdecode : TargetSum.decodeDigest
      (CacheView.topEncodingHash cache secretKey.parameter key
        (Concrete.bottomRoot cache secretKey key, randomness)) = some encoding) :
    Concrete.verifyTopFromCache cache (publicKeyFromCache cache secretKey) key
      (Concrete.bottomRoot cache secretKey key) (topPartFromCache cache secretKey key) = true := by
  have hpk : publicKeyFromCache cache secretKey =
      ⟨topTreeNode cache secretKey.parameter secretKey.topChainStart treeHeight Concrete.rootNode,
        secretKey.parameter⟩ := by
    rw [publicKeyFromCache]
  obtain ⟨hpart, hpath⟩ := layerPath_topPartFromCache cache secretKey key randomness encoding hsigned
  rw [Concrete.verifyTopFromCache_eq_true_iff, hpk, hpath]
  refine ⟨encoding, ?_, ?_⟩
  · rw [hpart]
    exact hdecode
  · rw [hpart]
    simp only
    rw [recover_honestTopValues]
    exact honestTopPath_ascends_to_root cache secretKey key

theorem verifyFromCache_signWithEncoding (cache : QueryCache HashSpec)
    (secretKey : SecretKey) (leafIndex : LeafIndex) (message : Message)
    (randomness : Randomness) (encoding : Encoding)
    (hdecode : TargetSum.decodeDigest
      (CacheView.encodingHash cache secretKey.parameter leafIndex (message, randomness)) =
        some encoding)
    (htop : ∃ topRandomness topEncoding,
      secretKey.topSigned (topKeyOf leafIndex) = some (topRandomness, topEncoding) ∧
      TargetSum.decodeDigest
        (CacheView.topEncodingHash cache secretKey.parameter (topKeyOf leafIndex)
          (Concrete.bottomRoot cache secretKey (topKeyOf leafIndex), topRandomness)) =
        some topEncoding) :
    Concrete.verifyFromCache cache (publicKeyFromCache cache secretKey) leafIndex message
      (signWithEncoding cache secretKey leafIndex randomness encoding) = true := by
  obtain ⟨topRandomness, topEncoding, hsigned, htopDecode⟩ := htop
  apply (Concrete.verifyFromCache_eq_true_iff _ _ _ _ _).2
  refine ⟨encoding, ?_, ?_⟩
  · simpa [publicKeyFromCache, signWithEncoding] using hdecode
  · have hparam : (publicKeyFromCache cache secretKey).parameter = secretKey.parameter := by
      simp [publicKeyFromCache]
    rw [hparam, leafHash_recovered_signWithEncoding,
      authenticationPath_ascends_to_root cache secretKey leafIndex randomness encoding]
    exact verifyTopFromCache_topPart cache secretKey (topKeyOf leafIndex) topRandomness topEncoding
      hsigned htopDecode

end XmssSecurity.Concrete.CacheReplay
