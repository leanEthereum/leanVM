import XmssSecurity.Proof.Bridge.Basic
import LeanXmss.Statement

/-!
# The real scheme in the model's terms

`LeanXmss` and the model hash the same bytes. Each hash call, decoding step and verification routine
of `LeanXmss` equals the model's, with the leaf index of a signature moved to the request and a
layer's key `b < 2^16` read as a top index.
-/

open OracleComp OracleSpec

namespace XmssSecurity.Bridge

set_option backward.isDefEq.respectTransparency false

/-- A top index as a key of the real scheme. -/
def topKey (key : TopIndex) : LeanXmss.KeyIndex :=
  ⟨key.val, by
    have := key.isLt
    simp only [topLifetime, treeHeight, LeanXmss.lifetime, LeanXmss.numLayers,
      LeanXmss.layerHeight] at *
    omega⟩

@[simp] theorem topKey_val (key : TopIndex) : (topKey key).val = key.val := rfl

theorem topKey_injective : Function.Injective topKey := fun _ _ h =>
  Fin.ext (by simpa using congrArg Fin.val h)

theorem keyAt_bottom (index : LeafIndex) :
    LeanXmss.keyAt index LeanXmss.bottomLayer = index := by
  apply Fin.ext
  simp [LeanXmss.keyAt, LeanXmss.bottomLayer]

theorem keyAt_top (index : LeafIndex) :
    LeanXmss.keyAt index LeanXmss.topLayer = topKey (topKeyOf index) := by
  apply Fin.ext
  simp [LeanXmss.keyAt, LeanXmss.topLayer, topKeyOf, LeanXmss.layerHeight, treeHeight,
    LeanXmss.numLayers]

/-! ## Hash inputs -/

theorem hash_eq {parameter : PublicParameter} {domain : LeanXmss.HashDomain} {domain' : HashDomain}
    {payload payload' : HashInput}
    (h : LeanXmss.tweakableHashInput parameter domain payload =
      tweakableHashInput parameter domain' payload') :
    (LeanXmss.Concrete.tweakableHash parameter domain payload :
        OracleComp LeanXmss.HashSpec LeanXmss.Digest) =
      (Concrete.tweakableHash parameter domain' payload' : OracleComp HashSpec Digest) := by
  unfold Concrete.tweakableHash LeanXmss.Concrete.tweakableHash
  rw [h]
  rfl

theorem chain_input (parameter : PublicParameter) (key : LeafIndex) (chain : ChainIndex)
    (step : ChainStep) (value : Digest) :
    LeanXmss.tweakableHashInput parameter (.chain LeanXmss.bottomLayer key step)
        (LeanXmss.Concrete.chainPayload chain value) =
      tweakableHashInput parameter (.chain key chain step) (bytesLE 16 value) := by
  simp only [LeanXmss.tweakableHashInput, tweakableHashInput, LeanXmss.tweakBytes, tweakBytes,
    LeanXmss.hashDomainFields, hashDomainFields, LeanXmss.Concrete.chainPayload, domainSuffix,
    List.append_assoc]
  rfl

theorem topChain_input (parameter : PublicParameter) (key : TopIndex) (chain : ChainIndex)
    (step : ChainStep) (value : Digest) :
    LeanXmss.tweakableHashInput parameter (.chain LeanXmss.topLayer (topKey key) step)
        (LeanXmss.Concrete.chainPayload chain value) =
      tweakableHashInput parameter (.topChain key chain step) (bytesLE 16 value) := by
  simp only [LeanXmss.tweakableHashInput, tweakableHashInput, LeanXmss.tweakBytes, tweakBytes,
    LeanXmss.hashDomainFields, hashDomainFields, LeanXmss.Concrete.chainPayload, domainSuffix,
    List.append_assoc]
  rfl

theorem leaf_input (parameter : PublicParameter) (key : LeafIndex) (payload : HashInput) :
    LeanXmss.tweakableHashInput parameter (.leaf LeanXmss.bottomLayer key) payload =
      tweakableHashInput parameter (.leaf key) payload := by
  simp only [LeanXmss.tweakableHashInput, tweakableHashInput, LeanXmss.tweakBytes, tweakBytes,
    LeanXmss.hashDomainFields, hashDomainFields, domainSuffix, List.append_nil]
  rfl

theorem topLeaf_input (parameter : PublicParameter) (key : TopIndex) (payload : HashInput) :
    LeanXmss.tweakableHashInput parameter (.leaf LeanXmss.topLayer (topKey key)) payload =
      tweakableHashInput parameter (.topLeaf key) payload := by
  simp only [LeanXmss.tweakableHashInput, tweakableHashInput, LeanXmss.tweakBytes, tweakBytes,
    LeanXmss.hashDomainFields, hashDomainFields, domainSuffix, List.append_nil]
  rfl

theorem node_input (parameter : PublicParameter) (level : MerkleLevel) (node : MerkleNode)
    (payload : HashInput) :
    LeanXmss.tweakableHashInput parameter (.node LeanXmss.bottomLayer (level.val + 1) node.val) payload =
      tweakableHashInput parameter (.merkle level node) payload := by
  simp only [LeanXmss.tweakableHashInput, tweakableHashInput, LeanXmss.tweakBytes, tweakBytes,
    LeanXmss.hashDomainFields, hashDomainFields, domainSuffix, List.append_nil]
  rfl

theorem topNode_input (parameter : PublicParameter) (level : MerkleLevel) (node : TopNode)
    (payload : HashInput) :
    LeanXmss.tweakableHashInput parameter (.node LeanXmss.topLayer (level.val + 1) node.val) payload =
      tweakableHashInput parameter (.topMerkle level node) payload := by
  simp only [LeanXmss.tweakableHashInput, tweakableHashInput, LeanXmss.tweakBytes, tweakBytes,
    LeanXmss.hashDomainFields, hashDomainFields, domainSuffix, List.append_nil]
  have h : LeanXmss.layerHi LeanXmss.topLayer (level.val + 1) = topFlag + level.val + 1 := by
    simp only [LeanXmss.layerHi, LeanXmss.topLayer, topFlag]
    omega
  rw [h]
  rfl

theorem message_input (parameter : PublicParameter) (key : LeafIndex) (message : Message)
    (randomness : Randomness) :
    LeanXmss.tweakableHashInput parameter (.message LeanXmss.bottomLayer key)
        (LeanXmss.bytesLE 32 message ++ LeanXmss.bytesLE 16 randomness) =
      tweakableHashInput parameter (.encoding key) (Concrete.encodingPayload message randomness) := by
  simp only [LeanXmss.tweakableHashInput, tweakableHashInput, LeanXmss.tweakBytes, tweakBytes,
    LeanXmss.hashDomainFields, hashDomainFields, domainSuffix, List.append_nil,
    Concrete.encodingPayload]
  rfl

theorem topMessage_input (parameter : PublicParameter) (key : TopIndex) (root : Digest)
    (randomness : Randomness) :
    LeanXmss.tweakableHashInput parameter (.message LeanXmss.topLayer (topKey key))
        (LeanXmss.bytesLE 16 root ++ LeanXmss.bytesLE 16 randomness) =
      tweakableHashInput parameter (.topEncoding key) (Concrete.topEncodingPayload root randomness) := by
  simp only [LeanXmss.tweakableHashInput, tweakableHashInput, LeanXmss.tweakBytes, tweakBytes,
    LeanXmss.hashDomainFields, hashDomainFields, domainSuffix, List.append_nil,
    Concrete.topEncodingPayload]
  rfl


/-! ## Hashing routines -/

theorem chainLength_eq : LeanXmss.chainLength = chainLength := rfl

theorem chainWalk_bottom (parameter : PublicParameter) (key : LeafIndex) (chain : ChainIndex)
    (start steps : Nat) (value : Digest) :
    (LeanXmss.Concrete.chainWalk parameter LeanXmss.bottomLayer key chain start steps value :
        OracleComp LeanXmss.HashSpec LeanXmss.Digest) =
      (Concrete.chainWalk parameter key chain start steps value : OracleComp HashSpec Digest) := by
  induction steps with
  | zero => rfl
  | succ steps ih =>
      rw [LeanXmss.Concrete.chainWalk, Concrete.chainWalk, ih]
      apply bind_congr
      intro previous
      by_cases h : start + steps < chainLength - 1
      · conv_lhs => rw [dite_eq_left (show start + steps < LeanXmss.chainLength - 1 from h)]
        conv_rhs => rw [dite_eq_left h]
        exact hash_eq (chain_input parameter key chain ⟨start + steps, h⟩ previous)
      · conv_lhs => rw [dite_eq_right (show ¬start + steps < LeanXmss.chainLength - 1 from h)]
        conv_rhs => rw [dite_eq_right h]

theorem chainWalk_top (parameter : PublicParameter) (key : TopIndex) (chain : ChainIndex)
    (start steps : Nat) (value : Digest) :
    (LeanXmss.Concrete.chainWalk parameter LeanXmss.topLayer (topKey key) chain start steps value :
        OracleComp LeanXmss.HashSpec LeanXmss.Digest) =
      (Concrete.topChainWalk parameter key chain start steps value : OracleComp HashSpec Digest) := by
  induction steps with
  | zero => rfl
  | succ steps ih =>
      rw [LeanXmss.Concrete.chainWalk, Concrete.topChainWalk, ih]
      apply bind_congr
      intro previous
      by_cases h : start + steps < chainLength - 1
      · conv_lhs => rw [dite_eq_left (show start + steps < LeanXmss.chainLength - 1 from h)]
        conv_rhs => rw [dite_eq_left h]
        exact hash_eq (topChain_input parameter key chain ⟨start + steps, h⟩ previous)
      · conv_lhs => rw [dite_eq_right (show ¬start + steps < LeanXmss.chainLength - 1 from h)]
        conv_rhs => rw [dite_eq_right h]

theorem leafHash_bottom (parameter : PublicParameter) (key : LeafIndex)
    (endpoints : ChainIndex → Digest) :
    (LeanXmss.Concrete.leafHash parameter LeanXmss.bottomLayer key endpoints :
        OracleComp LeanXmss.HashSpec LeanXmss.Digest) =
      (Concrete.leafHash parameter key endpoints : OracleComp HashSpec Digest) :=
  hash_eq (leaf_input parameter key _)

theorem leafHash_top (parameter : PublicParameter) (key : TopIndex)
    (endpoints : ChainIndex → Digest) :
    (LeanXmss.Concrete.leafHash parameter LeanXmss.topLayer (topKey key) endpoints :
        OracleComp LeanXmss.HashSpec LeanXmss.Digest) =
      (Concrete.topLeafHash parameter key endpoints : OracleComp HashSpec Digest) :=
  hash_eq (topLeaf_input parameter key _)

theorem messageDigest_bottom (parameter : PublicParameter) (key : LeafIndex) (message : Message)
    (randomness : Randomness) :
    (LeanXmss.Concrete.messageDigest parameter LeanXmss.bottomLayer key (LeanXmss.bytesLE 32 message)
        randomness : OracleComp LeanXmss.HashSpec LeanXmss.Digest) =
      (Concrete.encodingHash parameter key message randomness : OracleComp HashSpec Digest) :=
  hash_eq (message_input parameter key message randomness)

theorem messageDigest_top (parameter : PublicParameter) (key : TopIndex) (root : Digest)
    (randomness : Randomness) :
    (LeanXmss.Concrete.messageDigest parameter LeanXmss.topLayer (topKey key) (LeanXmss.bytesLE 16 root)
        randomness : OracleComp LeanXmss.HashSpec LeanXmss.Digest) =
      (Concrete.topEncodingHash parameter key root randomness : OracleComp HashSpec Digest) :=
  hash_eq (topMessage_input parameter key root randomness)

theorem nodeHash_bottom (parameter : PublicParameter) (level : MerkleLevel) (node : MerkleNode)
    (left right : Digest) :
    (LeanXmss.Concrete.tweakableHash parameter (.node LeanXmss.bottomLayer (level.val + 1) node.val)
        (LeanXmss.Concrete.nodePayload left right) : OracleComp LeanXmss.HashSpec LeanXmss.Digest) =
      (Concrete.nodeHash parameter level node left right : OracleComp HashSpec Digest) :=
  hash_eq (node_input parameter level node _)

theorem nodeHash_top (parameter : PublicParameter) (level : MerkleLevel) (node : TopNode)
    (left right : Digest) :
    (LeanXmss.Concrete.tweakableHash parameter (.node LeanXmss.topLayer (level.val + 1) node.val)
        (LeanXmss.Concrete.nodePayload left right) : OracleComp LeanXmss.HashSpec LeanXmss.Digest) =
      (Concrete.topNodeHash parameter level node left right : OracleComp HashSpec Digest) :=
  hash_eq (topNode_input parameter level node _)

/-! ## The codeword -/

theorem encoding_eq (digest : Digest) :
    LeanXmss.Codeword.encoding digest = TargetSum.digestEncoding digest := rfl

theorem digestTop_eq_zero_iff (digest : Digest) :
    TargetSum.digestTop digest = 0 ↔
      digest.toNat / 2 ^ (LeanXmss.winternitzBits * LeanXmss.numChains) = 0 := by
  have hlt : digest.toNat < 2 ^ 128 := digest.isLt
  rw [← BitVec.toNat_inj]
  simp only [TargetSum.digestTop, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow,
    TargetSum.zeroBits, digestBits, winternitzBits, numChains,
    LeanXmss.winternitzBits, LeanXmss.numChains]
  rw [Nat.mod_eq_of_lt (by omega)]
  exact Iff.rfl

theorem decode_eq (digest : Digest) :
    LeanXmss.Codeword.decode digest = TargetSum.decodeDigest digest := by
  unfold LeanXmss.Codeword.decode TargetSum.decodeDigest LeanXmss.Codeword.Valid TargetSum.Valid
  rw [← encoding_eq]
  by_cases h : TargetSum.digestTop digest = 0
  · have h' := (digestTop_eq_zero_iff digest).1 h
    simp only [h, h', true_and]
    rfl
  · have h' : ¬digest.toNat / 2 ^ (LeanXmss.winternitzBits * LeanXmss.numChains) = 0 :=
      fun h'' => h ((digestTop_eq_zero_iff digest).2 h'')
    simp only [h, h', false_and, ite_false]


/-! ## Verification -/

theorem sequenceFin_eq {m : Type → Type} [Monad m] {α : Type} {n : Nat} (c : Fin n → m α) :
    LeanXmss.Concrete.sequenceFin c = Concrete.sequenceFin c := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [LeanXmss.Concrete.sequenceFin, Concrete.sequenceFin, ih]

theorem treeFold_bottom (parameter : PublicParameter) (key : LeafIndex) (signature : Signature)
    (leaf : Digest) (levels : Nat) (hlevels : levels ≤ treeHeight) :
    (LeanXmss.Concrete.treeFold parameter LeanXmss.bottomLayer key signature.authPath levels leaf :
        OracleComp LeanXmss.HashSpec LeanXmss.Digest) =
      (Concrete.authenticationRoot parameter key signature levels leaf : OracleComp HashSpec Digest) := by
  induction levels with
  | zero => rfl
  | succ levels ih =>
      have h : levels < treeHeight := by omega
      rw [LeanXmss.Concrete.treeFold, Concrete.authenticationRoot, ih (by omega)]
      apply bind_congr
      intro current
      simp only [Concrete.authenticationNodeHash, Concrete.signaturePath, dite_eq_left h,
        dite_eq_left (show levels < LeanXmss.layerHeight from h)]
      by_cases hb : key.val.testBit levels
      · simp only [hb, ite_true]
        exact nodeHash_bottom parameter ⟨levels, h⟩ (Concrete.nodeIndex key levels) _ _
      · simp only [hb, Bool.false_eq_true, ite_false]
        exact nodeHash_bottom parameter ⟨levels, h⟩ (Concrete.nodeIndex key levels) _ _

theorem treeFold_top (parameter : PublicParameter) (key : TopIndex) (path : Fin treeHeight → Digest)
    (leaf : Digest) (levels : Nat) (hlevels : levels ≤ treeHeight) :
    (LeanXmss.Concrete.treeFold parameter LeanXmss.topLayer (topKey key) path levels leaf :
        OracleComp LeanXmss.HashSpec LeanXmss.Digest) =
      (Concrete.topAuthenticationRoot parameter key path levels leaf : OracleComp HashSpec Digest) := by
  induction levels with
  | zero => rfl
  | succ levels ih =>
      have h : levels < treeHeight := by omega
      rw [LeanXmss.Concrete.treeFold, Concrete.topAuthenticationRoot, ih (by omega)]
      apply bind_congr
      intro current
      simp only [dite_eq_left h, dite_eq_left (show levels < LeanXmss.layerHeight from h), topKey_val]
      by_cases hb : key.val.testBit levels
      · simp only [hb, ite_true]
        exact nodeHash_top parameter ⟨levels, h⟩ (Concrete.topNodeIndex key levels) _ _
      · simp only [hb, Bool.false_eq_true, ite_false]
        exact nodeHash_top parameter ⟨levels, h⟩ (Concrete.topNodeIndex key levels) _ _

/-- A model layer signature as the real scheme's. -/
def layerToReal (part : LayerSignature) : LeanXmss.LayerSignature :=
  ⟨part.randomness, part.chainValue, part.authPath⟩

/-- A real layer signature as the model's. -/
def layerToModel (part : LeanXmss.LayerSignature) : LayerSignature :=
  ⟨part.randomness, part.chainValues, part.path⟩

/-- A model signature at a leaf index as the real scheme's. -/
def toRealSig (index : LeafIndex) (signature : Signature) : LeanXmss.Signature :=
  ⟨index, fun lay => if lay = LeanXmss.bottomLayer then
    ⟨signature.randomness, signature.chainValue, signature.authPath⟩ else layerToReal signature.top⟩

/-- A real signature as the model's, its leaf index dropped. -/
def toModelSig (signature : LeanXmss.Signature) : Signature where
  randomness := (signature.layers LeanXmss.bottomLayer).randomness
  chainValue := (signature.layers LeanXmss.bottomLayer).chainValues
  authPath := (signature.layers LeanXmss.bottomLayer).path
  top := layerToModel (signature.layers LeanXmss.topLayer)

def toRealPk (publicKey : PublicKey) : LeanXmss.PublicKey := ⟨publicKey.root, publicKey.parameter⟩

def toModelPk (publicKey : LeanXmss.PublicKey) : PublicKey := ⟨publicKey.root, publicKey.parameter⟩

theorem layer_cases (lay : LeanXmss.Layer) : lay = LeanXmss.bottomLayer ∨ lay = LeanXmss.topLayer := by
  rcases lay with ⟨v, hv⟩
  simp only [LeanXmss.numLayers] at hv
  interval_cases v
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem topLayer_ne_bottom : LeanXmss.topLayer ≠ LeanXmss.bottomLayer := by decide

@[simp] theorem toRealSig_leafIndex (index : LeafIndex) (signature : Signature) :
    (toRealSig index signature).leafIndex = index := rfl

@[simp] theorem toModelSig_toRealSig (index : LeafIndex) (signature : Signature) :
    toModelSig (toRealSig index signature) = signature := by
  simp [toModelSig, toRealSig, layerToModel, layerToReal, topLayer_ne_bottom]

@[simp] theorem toRealSig_toModelSig (signature : LeanXmss.Signature) :
    toRealSig signature.leafIndex (toModelSig signature) = signature := by
  rcases signature with ⟨index, layers⟩
  simp only [toRealSig, toModelSig, layerToReal, layerToModel, LeanXmss.Signature.mk.injEq, true_and]
  funext lay
  rcases layer_cases lay with h | h <;> subst h
  · simp
  · simp [topLayer_ne_bottom]

theorem toModelPk_toRealPk (publicKey : PublicKey) : toModelPk (toRealPk publicKey) = publicKey := rfl

theorem recoverChain_bottom (parameter : PublicParameter) (key : LeafIndex) (chain : ChainIndex)
    (digit : Digit) (value : Digest) :
    (LeanXmss.Concrete.recoverChain parameter LeanXmss.bottomLayer key chain digit value :
        OracleComp LeanXmss.HashSpec LeanXmss.Digest) =
      (Concrete.recoverChain parameter key chain digit value : OracleComp HashSpec Digest) :=
  chainWalk_bottom parameter key chain _ _ value

/-- The bottom layer's root in the model's terms. -/
theorem layerRoot_bottom (parameter : PublicParameter) (key : LeafIndex) (message : Message)
    (signature : Signature) :
    (LeanXmss.Concrete.layerRoot parameter LeanXmss.bottomLayer key (LeanXmss.bytesLE 32 message)
        ⟨signature.randomness, signature.chainValue, signature.authPath⟩ :
        OracleComp LeanXmss.HashSpec (Option LeanXmss.Digest)) =
      ((do
        let digest ← Concrete.encodingHash parameter key message signature.randomness
        match TargetSum.decodeDigest digest with
        | none => pure none
        | some encoding => do
            let endpoints ← Concrete.recoverEndpoints parameter key encoding signature
            let leaf ← Concrete.leafHash parameter key endpoints
            let root ← Concrete.authenticationRoot parameter key signature treeHeight leaf
            pure (some root)) : OracleComp HashSpec (Option Digest)) := by
  unfold LeanXmss.Concrete.layerRoot LeanXmss.Concrete.otsLeaf
  simp only [bind_assoc]
  rw [messageDigest_bottom]
  apply bind_congr
  intro digest
  rw [decode_eq]
  cases TargetSum.decodeDigest digest with
  | none => simp
  | some encoding =>
      simp only [bind_assoc, pure_bind, sequenceFin_eq, recoverChain_bottom, leafHash_bottom,
        Concrete.recoverEndpoints]
      apply bind_congr
      intro endpoints
      apply bind_congr
      intro leaf
      rw [treeFold_bottom parameter key signature leaf LeanXmss.layerHeight le_rfl]
      rfl


/-- The top layer's root in the model's terms. -/
theorem layerRoot_top (parameter : PublicParameter) (key : TopIndex) (root : Digest)
    (part : LayerSignature) :
    (LeanXmss.Concrete.layerRoot parameter LeanXmss.topLayer (topKey key) (LeanXmss.bytesLE 16 root)
        (layerToReal part) : OracleComp LeanXmss.HashSpec (Option LeanXmss.Digest)) =
      ((do
        let digest ← Concrete.topEncodingHash parameter key root part.randomness
        match TargetSum.decodeDigest digest with
        | none => pure none
        | some encoding => do
            let endpoints ← Concrete.sequenceFin fun chain =>
              Concrete.topChainWalk parameter key chain (encoding chain).val
                (chainLength - 1 - (encoding chain).val) (part.chainValue chain)
            let leaf ← Concrete.topLeafHash parameter key endpoints
            let topRoot ← Concrete.topAuthenticationRoot parameter key part.authPath treeHeight leaf
            pure (some topRoot)) : OracleComp HashSpec (Option Digest)) := by
  unfold LeanXmss.Concrete.layerRoot LeanXmss.Concrete.otsLeaf
  simp only [bind_assoc, layerToReal]
  rw [messageDigest_top]
  apply bind_congr
  intro digest
  rw [decode_eq]
  cases TargetSum.decodeDigest digest with
  | none => simp
  | some encoding =>
      simp only [bind_assoc, pure_bind, sequenceFin_eq, LeanXmss.Concrete.recoverChain, chainWalk_top,
        leafHash_top]
      apply bind_congr
      intro endpoints
      apply bind_congr
      intro leaf
      rw [treeFold_top parameter key part.authPath leaf LeanXmss.layerHeight le_rfl]
      rfl

theorem verify_eq (publicKey : PublicKey) (index : LeafIndex) (message : Message)
    (signature : Signature) :
    (LeanXmss.Concrete.verify (toRealPk publicKey) message (toRealSig index signature) :
        OracleComp LeanXmss.HashSpec Bool) =
      (Concrete.verify publicKey index message signature : OracleComp HashSpec Bool) := by
  unfold LeanXmss.Concrete.verify Concrete.verify Concrete.verifyAfterLeaf Concrete.verifyTop
  simp only [toRealSig, toRealPk, ite_eq_left, ite_eq_right topLayer_ne_bottom, keyAt_bottom, keyAt_top]
  rw [layerRoot_bottom]
  simp only [bind_assoc]
  apply bind_congr
  intro digest
  cases TargetSum.decodeDigest digest with
  | none => simp
  | some encoding =>
      simp only [bind_assoc, pure_bind]
      apply bind_congr
      intro endpoints
      apply bind_congr
      intro leaf
      apply bind_congr
      intro root
      rw [layerRoot_top]
      simp only [bind_assoc]
      apply bind_congr
      intro digest'
      cases TargetSum.decodeDigest digest' with
      | none => simp
      | some encoding' => simp [bind_assoc]

theorem verify_eq' (publicKey : PublicKey) (message : Message) (signature : LeanXmss.Signature) :
    (LeanXmss.Concrete.verify (toRealPk publicKey) message signature :
        OracleComp LeanXmss.HashSpec Bool) =
      (Concrete.verify publicKey signature.leafIndex message (toModelSig signature) :
        OracleComp HashSpec Bool) := by
  conv_lhs => rw [← toRealSig_toModelSig signature]
  exact verify_eq publicKey signature.leafIndex message (toModelSig signature)

theorem verify_real (publicKey : LeanXmss.PublicKey) (message : Message) (signature : LeanXmss.Signature) :
    (LeanXmss.Concrete.verify publicKey message signature : OracleComp LeanXmss.HashSpec Bool) =
      (Concrete.verify (toModelPk publicKey) signature.leafIndex message (toModelSig signature) :
        OracleComp HashSpec Bool) :=
  verify_eq' (toModelPk publicKey) message signature

end XmssSecurity.Bridge
