module

public import FORS.Statement
public import FORS.Scheme.DigestView
public import Statement.LeanSphincs
public import Common.WithHash

@[expose] public section

/-!
# The statement's leanSPHINCS and upstream's model: the maps and the verifier

The proof of this project (`FORS`, leanVM's `formal/lean_sphincs` at `40f877dc`) is about
`FORS.Scheme`, a model of leanSPHINCS generic in its shape (`FORS.Params`), the hash a random oracle
(`FORS.HashSpec`). At the deployed configuration, `.layered 26 3 8 24 10 1182000000` (`params`), its
verifier, its queries answered by Keccak-256 over `π` (`schemeHashOverPermutation`), is the
statement's (`simulateQ_verify`), through the maps of the keys and signatures. The two differ in
presentation only:

* the model numbers the layers from the top (`lay = 0` the top layer, the address's layer word
  `2 - lay`), the statement from the bottom as the crate does (`toLayer`);
* the model's address has a 96-bit tree word, the statement's a zero word and a 64-bit tree
  (`treeBytes_eq`: the same bytes below `2^64`), and the model places a FORS node index past its
  tree's width above `2^31`, which no algorithm computes;
* the model's digest packs the index and the FORS leaves into one bit vector, the statement reads
  them off the digest's bytes (`digestIndex_eq`, `digestForsLeaves_eq`).
-/

open OracleComp OracleSpec

namespace Sphincs.Model

open HashSig HashSig.OverPermutation Common Common.SufCma

/-- The deployed configuration: height 26, three layers of 10 + 8 + 8 from the top, FORS of 24
trees of height 10, `N = 1,182,000,000`. -/
abbrev params : FORS.Params := .layered 26 3 8 24 10 1182000000

attribute [local instance] params

/-! ## Bytes -/

theorem bytesLE_eq : @FORS.bytesLE = @littleEndianBytes := rfl

theorem bytesBE_eq : @FORS.bytesBE = @bigEndianBytes := rfl

/-- **The tree word**: the model's 96-bit tree word is the statement's zero word and 64-bit tree,
below `2^64`. -/
theorem treeBytes_eq (tree : ℕ) (htree : tree < 2 ^ 64) :
    FORS.bytesBE 12 (BitVec.ofNat 96 tree) =
      bigEndianBytes 4 0 ++ bigEndianBytes 8 (BitVec.ofNat 64 tree) := by
  have h64 : tree < 18446744073709551616 := by simpa using htree
  have h96 : tree < 79228162514264337593543950336 := by omega
  simp only [FORS.bytesBE, bigEndianBytes, List.ofFn_succ, List.ofFn_zero]
  simp only [List.cons_append, List.nil_append, List.cons.injEq]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩ <;>
  · congr 1
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.extractLsb'_toNat, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
    simp only [Fin.val_succ, Fin.val_zero, Nat.reduceAdd, Nat.reduceSub, Nat.reduceMul,
      Nat.reducePow, Nat.mod_eq_of_lt h96, Nat.mod_eq_of_lt h64]
    try rw [Nat.div_eq_of_lt (by omega)]
    try simp

/-! ## Layers, indices and addresses -/

/-- A model layer (`0` the top) as the statement's layer (`0` the bottom). -/
def toLayer (lay : FORS.Layer) : Layer :=
  ⟨2 - lay.val, by have := lay.isLt; unfold layerCount; omega⟩

/-- A statement layer as the model's. -/
def ofLayer (layer : Layer) : FORS.Layer :=
  ⟨2 - layer.val, by have := layer.isLt; unfold layerCount at this; show _ < 3; omega⟩

theorem toLayer_ofLayer (layer : Layer) : toLayer (ofLayer layer) = layer := by
  have := layer.isLt; unfold layerCount at this
  apply Fin.ext; simp only [toLayer, ofLayer]; omega

theorem ofLayer_toLayer (lay : FORS.Layer) : ofLayer (toLayer lay) = lay := by
  have := lay.isLt; change _ < 3 at this
  apply Fin.ext; simp only [toLayer, ofLayer]; omega

theorem layerHeight_toLayer (lay : FORS.Layer) :
    layerHeight (toLayer lay) = FORS.layerHeight lay := by
  rcases lay with ⟨_ | _ | _ | n, h⟩ <;> first | rfl | (change _ < 3 at h; omega)

theorem layerByte_eq (lay : FORS.Layer) : FORS.layerByte lay = (toLayer lay).val := rfl

theorem maxLayerHeight_eq : FORS.maxLayerHeight = 10 := rfl

/-- A model leaf (of any layer) as the statement's. -/
def toLeaf (leaf : FORS.LeafIndex) : TreeLeafIndex := ⟨leaf.val, leaf.isLt⟩

theorem treeIndexAt_eq (index : FORS.Index) (lay : FORS.Layer) :
    FORS.Concrete.treeIndexAt index lay = treeOfIndex (toLayer lay) index := by
  apply Fin.ext
  fin_cases lay <;> rfl

theorem leafIndexAt_eq (index : FORS.Index) (lay : FORS.Layer) :
    toLeaf (FORS.Concrete.leafIndexAt index lay) = leafOfIndex (toLayer lay) index := by
  apply Fin.ext
  fin_cases lay <;> rfl

/-- **An address's bytes**: the model's fields, the tree below `2^64`, are the statement's address
of the type whose word is the model's tag. -/
theorem fieldBytes_tweakFields (addressType : AddressType) (layer tree keyPair height index : ℕ)
    (htree : tree < 2 ^ 64) :
    FORS.fieldBytes (FORS.tweakFields addressType.word layer tree keyPair height index) =
      (makeAddress layer tree addressType keyPair height index).toBytes := by
  simp only [FORS.fieldBytes, FORS.tweakFields, Address.toBytes, makeAddress,
    treeBytes_eq tree htree, List.append_assoc]
  rfl

/-- A model hash domain whose FORS node lies in its tree, as every algorithm's does. -/
def InRange : FORS.HashDomain → Prop
  | .chain .. => True
  | .leaf .. => True
  | .node .. => True
  | .encoding .. => True
  | .forsLeaf .. => True
  | .forsNode _ _ level node => node.val < 2 ^ (10 - (level.val + 1))
  | .forsRoots _ => True

/-- A model hash domain as the statement's: the layer reversed, a FORS level as its height. -/
def toDomain : FORS.HashDomain → HashDomain
  | .chain lay tree leaf chainIndex step => .chain (toLayer lay) tree (toLeaf leaf) chainIndex step
  | .leaf lay tree leaf => .leaf (toLayer lay) tree (toLeaf leaf)
  | .node lay tree level nodeIndex => .node (toLayer lay) tree level nodeIndex
  | .encoding lay tree leaf => .encoding (toLayer lay) tree (toLeaf leaf)
  | .forsLeaf index forsTree leaf => .forsLeaf index forsTree leaf
  | .forsNode index forsTree level node => .forsNode index forsTree (level.val + 1) node.val
  | .forsRoots index => .forsRoots index

theorem forsTree_lt (index : FORS.Index) : index.val / 2 ^ FORS.bottomHeight < 2 ^ 64 := by
  have := index.isLt; change _ < 2 ^ 26 at this
  exact lt_of_le_of_lt (Nat.div_le_self _ _) (by omega)

theorem treeOfIndex_zero (index : FORS.Index) :
    (treeOfIndex 0 index).val = index.val / 2 ^ FORS.bottomHeight := rfl

theorem leafOfIndex_zero (index : FORS.Index) :
    (leafOfIndex 0 index).val = index.val % 2 ^ FORS.bottomHeight := by
  show index.val / 2 ^ 0 % 2 ^ 8 = index.val % 2 ^ 8
  simp

/-- **The same address bytes**, for a domain in range. -/
theorem fieldBytes_hashDomainFields (domain : FORS.HashDomain) (h : InRange domain) :
    FORS.fieldBytes (FORS.hashDomainFields domain) =
      (hashDomainFields (toDomain domain)).toBytes := by
  cases domain with
  | chain lay tree leaf chainIndex step =>
    exact fieldBytes_tweakFields .wotsHash _ _ _ _ _ (lt_trans tree.isLt (by decide))
  | leaf lay tree leaf =>
    exact fieldBytes_tweakFields .wotsPublicKey _ _ _ _ _ (lt_trans tree.isLt (by decide))
  | node lay tree level nodeIndex =>
    exact fieldBytes_tweakFields .tree _ _ _ _ _ (lt_trans tree.isLt (by decide))
  | encoding lay tree leaf =>
    exact fieldBytes_tweakFields .wotsEncoding _ _ _ _ _ (lt_trans tree.isLt (by decide))
  | forsLeaf index forsTree leaf =>
    have hidx : FORS.forsTreeIndex forsTree 0 leaf.val =
        forsTreeIndex (show ForsTreeIndex from forsTree) 0 leaf.val := by
      unfold FORS.forsTreeIndex forsTreeIndex
      split
      · rfl
      · next hn => exact absurd (by simp) hn
    simp only [FORS.hashDomainFields, FORS.forsFields, hashDomainFields, hidx, treeOfIndex_zero,
      leafOfIndex_zero, toDomain]
    exact fieldBytes_tweakFields .forsTree _ _ _ _ _ (forsTree_lt index)
  | forsNode index forsTree level node =>
    have hidx : FORS.forsTreeIndex forsTree (level.val + 1) node.val =
        forsTreeIndex (show ForsTreeIndex from forsTree) (level.val + 1) node.val := by
      unfold FORS.forsTreeIndex forsTreeIndex
      split
      · rfl
      · next hn => exact absurd h hn
    simp only [FORS.hashDomainFields, FORS.forsFields, hashDomainFields, hidx, treeOfIndex_zero,
      leafOfIndex_zero, toDomain]
    exact fieldBytes_tweakFields .forsTree _ _ _ _ _ (forsTree_lt index)
  | forsRoots index =>
    simp only [FORS.hashDomainFields, FORS.forsFields, hashDomainFields, treeOfIndex_zero,
      leafOfIndex_zero, toDomain]
    exact fieldBytes_tweakFields .forsRoots _ _ _ _ _ (forsTree_lt index)

/-- **The same hash input**, for a domain in range. -/
theorem tweakableHashInput_eq (parameter : FORS.PublicParameter) (domain : FORS.HashDomain)
    (h : InRange domain) (payload : FORS.HashInput) :
    FORS.tweakableHashInput parameter domain payload =
      addressedHashInput parameter (hashDomainFields (toDomain domain)) payload := by
  simp only [FORS.tweakableHashInput, FORS.tweakBytes, fieldBytes_hashDomainFields domain h,
    addressedHashInput, hasherInput]
  rfl

/-! ## The hash -/

/-- The model's hash queries answered by a hash `hash` of the statement's, in any monad. -/
def hashImpl {m : Type → Type} (hash : HashInput → m HashOutput) : QueryImpl FORS.HashSpec m :=
  fun input ↦ hash input

/-- In the random-permutation model, the model's queries are answered by Keccak-256 over `π`. -/
theorem schemeHashOverPermutation_eq :
    schemeHashOverPermutation = hashImpl (keccakHash queryPermutation) := by
  funext input
  simp only [schemeHashOverPermutation, hashImpl, keccak256OverPermutation, keccakHash,
    Functor.map_map]
  refine congrArg (· <$> _) (funext fun digest ↦ ?_)
  simp only [digestBytesEquivBitVec_apply, LeanVM.Protocol.Digest.toBytes, Vector.toList]

variable {m : Type → Type} [Monad m] [LawfulMonad m] {hash : HashInput → m HashOutput}

local notation "σ" => hashImpl hash

/-- A query of the model's hash is the statement's hash. -/
theorem simulateQ_oracleHash (input : FORS.HashInput) :
    simulateQ σ (FORS.Concrete.oracleHash (m := OracleComp FORS.HashSpec) input) =
      hash input := by
  change simulateQ σ
    (LeanXmss.Verification.oracleHashWithHash (m := OracleComp SchemeHashSpec) input) = _
  exact simulateQ_HasQuery_query (spec := SchemeHashSpec) (impl := hashImpl hash) input


/-! ### Binds

The model's computations are in `OracleComp FORS.HashSpec`, the statement's hash spec up to
unfolding: the simulation lemmas of its binds, stated in that monad, so that `simp` sees them. -/

theorem sim_bind {α β : Type} (x : OracleComp FORS.HashSpec α)
    (f : α → OracleComp FORS.HashSpec β) :
    simulateQ σ (@Bind.bind (OracleComp FORS.HashSpec) _ α β x f) =
      simulateQ σ x >>= fun a ↦ simulateQ σ (f a) :=
  simulateQ_bind _ _ _

theorem sim_pure {α : Type} (a : α) :
    simulateQ σ (@Pure.pure (OracleComp FORS.HashSpec) _ α a) = pure a :=
  simulateQ_pure _ _

theorem sim_map {α β : Type} (f : α → β) (x : OracleComp FORS.HashSpec α) :
    simulateQ σ (@Functor.map (OracleComp FORS.HashSpec) _ α β f x) = f <$> simulateQ σ x :=
  simulateQ_map _ _ _

/-- Two binds agree when their computations and their continuations do. -/
theorem bind_eq_of {m : Type → Type} [Monad m] {α β : Type} {x y : m α} {f g : α → m β}
    (hx : x = y) (hfg : ∀ a, f a = g a) : x >>= f = y >>= g := by
  rw [hx, funext hfg]

/-- A hash query of a domain in range is the statement's tweakable hash. -/
theorem simulateQ_tweakableHash (parameter : FORS.PublicParameter) (domain : FORS.HashDomain)
    (h : InRange domain) (payload : FORS.HashInput) :
    simulateQ σ (FORS.Concrete.tweakableHash (m := OracleComp FORS.HashSpec) parameter domain
      payload) =
      Verification.tweakableHash hash parameter (toDomain domain) payload := by
  simp only [FORS.Concrete.tweakableHash, sim_bind, sim_pure, simulateQ_oracleHash,
    tweakableHashInput_eq parameter domain h, Verification.tweakableHash,
    Verification.addressedHash]
  rfl

theorem simulateQ_sequenceFin {α : Type} {n : ℕ} (c : Fin n → OracleComp FORS.HashSpec α) :
    simulateQ σ (FORS.Concrete.sequenceFin (m := OracleComp FORS.HashSpec) c) =
      sequenceFin fun i ↦ simulateQ σ (c i) := by
  induction n with
  | zero => simp only [FORS.Concrete.sequenceFin, sequenceFin, sim_pure]
  | succ n ih =>
    simp only [FORS.Concrete.sequenceFin, sequenceFin, sim_bind, sim_pure, ih]

/-! ## The maps of keys and signatures -/

/-- A statement public key as the model's: `PK.root`, and `PK.seed` as the parameter. -/
def toModelPublicKey (publicKey : PublicKey) : FORS.PublicKey :=
  ⟨publicKey.root, publicKey.publicSeed⟩

/-- A model public key as the statement's. -/
def ofModelPublicKey (publicKey : FORS.PublicKey) : PublicKey :=
  ⟨publicKey.parameter, publicKey.root⟩

/-- The public keys correspond. -/
def publicKeyEquiv : FORS.PublicKey ≃ PublicKey where
  toFun := ofModelPublicKey
  invFun := toModelPublicKey
  left_inv _ := rfl
  right_inv _ := rfl

/-- A FORS tree's opening, the model's from the statement's. -/
def toModelTreeOpening (opening : ForsTreeOpening) : FORS.TreeOpening :=
  ⟨opening.secret, opening.path⟩

/-- A FORS tree's opening, the statement's from the model's. -/
def ofModelTreeOpening (opening : FORS.TreeOpening) : ForsTreeOpening :=
  ⟨opening.secret, opening.path⟩

theorem layerHeight_ofLayer (layer : Layer) :
    FORS.layerHeight (ofLayer layer) = layerHeight layer := by
  rw [← layerHeight_toLayer, toLayer_ofLayer]

/-- A statement signature as the model's: the layers reversed, each path read through its length's
equality. -/
def toModelSignature (signature : Signature) : FORS.Signature where
  randomness := signature.randomizer
  fors forsTree := toModelTreeOpening (signature.forsOpening forsTree)
  layers lay :=
    ⟨(signature.layers (toLayer lay)).counter, (signature.layers (toLayer lay)).chainValues,
      fun level ↦ (signature.layers (toLayer lay)).authenticationPath
        (Fin.cast (layerHeight_toLayer lay).symm level)⟩

/-- A model signature as the statement's. -/
def ofModelSignature (signature : FORS.Signature) : Signature where
  randomizer := signature.randomness
  forsOpening forsTree := ofModelTreeOpening (signature.fors forsTree)
  layers layer :=
    ⟨(signature.layers (ofLayer layer)).counter, (signature.layers (ofLayer layer)).chainValues,
      fun level ↦ (signature.layers (ofLayer layer)).path
        (Fin.cast (layerHeight_ofLayer layer).symm level)⟩

/-- **The signatures correspond.** -/
def signatureEquiv : FORS.Signature ≃ Signature where
  toFun := ofModelSignature
  invFun := toModelSignature
  left_inv signature := by
    rcases signature with ⟨randomness, fors, layers⟩
    simp only [toModelSignature, ofModelSignature, toModelTreeOpening, ofModelTreeOpening]
    congr 1
    funext lay
    fin_cases lay <;> rfl
  right_inv signature := by
    rcases signature with ⟨randomizer, forsOpening, layers⟩
    simp only [toModelSignature, ofModelSignature, toModelTreeOpening, ofModelTreeOpening]
    congr 1
    funext layer
    fin_cases layer <;> rfl

/-! ## The digest's fields

The model packs the index and the FORS leaves into one bit vector (`FORS.truncateMessageDigest`),
the statement keeps the 34 bytes and reads the fields off them: both read the bytes of the calls
(`FORS.digestOutputBytes`) as FIPS 205's Algorithm 19 does. -/

section Digest

open FORS.Concrete (outputBit digestOutputBytes_length testBit_digestOutputByte
  testBit_digestFieldsValue
  testBit_digestIndexValue digestIndexValue_lt msbField_lt beInt_append)

theorem digestCalls_eq : FORS.digestCalls = 2 := rfl

/-- The statement's digest calls as the model's (the same type at `params`). -/
abbrev asModel (outputs : DigestCall → HashOutput) : FORS.DigestCall → FORS.HashOutput := outputs

theorem mdBytes_eq : FORS.mdBytes = 30 := rfl

theorem treeIndexBytes_eq : FORS.treeIndexBytes = 3 := rfl

theorem leafIndexBytes_eq : FORS.leafIndexBytes = 1 := rfl

theorem bottomHeight_eq : FORS.bottomHeight = 8 := rfl

theorem messageDigestBits_eq : FORS.messageDigestBits = 266 := rfl

/-- Bit `g` of the statement's value of the calls is bit `g` of the calls. -/
theorem testBit_digestValue (outputs : DigestCall → HashOutput) (g : ℕ) (hg : g < 512) :
    (digestValue outputs).testBit g = outputBit (asModel outputs) g := by
  have h0 := (outputs ⟨0, by decide⟩).isLt
  have hsum : digestValue outputs =
      2 ^ 256 * (outputs ⟨1, by decide⟩).toNat + (outputs ⟨0, by decide⟩).toNat := by
    show (∑ call : Fin 2, (outputs call).toNat * 2 ^ (256 * call.val)) = _
    rw [Fin.sum_univ_two]
    change (outputs ⟨0, by decide⟩).toNat * 2 ^ (256 * 0) +
      (outputs ⟨1, by decide⟩).toNat * 2 ^ (256 * 1) = _
    ring
  rw [hsum, Nat.testBit_two_pow_mul_add _ h0, outputBit]
  have hc : g / 256 < FORS.digestCalls := by rw [digestCalls_eq]; omega
  rw [dite_eq_left hc]
  by_cases hlt : g < 256
  · have h1 : g / 256 = 0 := by omega
    have h2 : g % 256 = g := by omega
    simp only [hlt, ↓reduceIte, BitVec.getLsbD, h1, h2]
    rfl
  · have h1 : g / 256 = 1 := by omega
    have h2 : g % 256 = g - 256 := by omega
    simp only [hlt, ↓reduceIte, BitVec.getLsbD, h1, h2]
    rfl

/-- Byte `p` of the statement's digest is byte `p` of the calls. -/
theorem messageDigestByte_eq (outputs : DigestCall → HashOutput) (p : ℕ) (hp : p < 34) :
    messageDigestByte (truncateMessageDigest outputs) p =
      ((FORS.digestOutputBytes (asModel outputs)).getD p 0).toNat := by
  apply Nat.eq_of_testBit_eq
  intro t
  by_cases ht : t < 8
  · rw [testBit_digestOutputByte (asModel outputs) p t ht,
      ← testBit_digestValue outputs _ (by omega)]
    simp only [messageDigestByte, truncateMessageDigest, BitVec.testBit_toNat,
      BitVec.getLsbD_extractLsb', BitVec.getLsbD_ofNat, ht, decide_true, Bool.true_and]
    have : 8 * p + t < 8 * digestByteCount := by unfold digestByteCount; omega
    simp only [this, decide_true, Bool.true_and]
  · have h8 : (2 : ℕ) ^ 8 ≤ 2 ^ t := Nat.pow_le_pow_right (by decide) (by omega)
    have hl : messageDigestByte (truncateMessageDigest outputs) p < 2 ^ t :=
      lt_of_lt_of_le (BitVec.isLt _) h8
    have hr : ((FORS.digestOutputBytes (asModel outputs)).getD p 0).toNat < 2 ^ t :=
      lt_of_lt_of_le (UInt8.toNat_lt _) h8
    rw [Nat.testBit_lt_two_pow hl, Nat.testBit_lt_two_pow hr]

theorem messageDigestBigEndian_succ (digest : MessageDigest) (start count : ℕ) :
    messageDigestBigEndian digest start (count + 1) =
      256 * messageDigestBigEndian digest start count +
        messageDigestByte digest (start + count) := by
  simp only [messageDigestBigEndian, List.range_succ, List.foldl_append, List.foldl_cons,
    List.foldl_nil]

/-- The statement's big-endian reading of the digest's bytes is the model's of the calls'. -/
theorem messageDigestBigEndian_eq (outputs : DigestCall → HashOutput) (start : ℕ) :
    ∀ count, start + count ≤ 34 →
      messageDigestBigEndian (truncateMessageDigest outputs) start count =
        FORS.beInt (((FORS.digestOutputBytes (asModel outputs)).drop start).take count)
  | 0, _ => by simp [messageDigestBigEndian, FORS.beInt]
  | count + 1, h => by
    have hlen := digestOutputBytes_length (asModel outputs)
    rw [digestCalls_eq] at hlen
    rw [messageDigestBigEndian_succ, messageDigestBigEndian_eq outputs start count (by omega),
      messageDigestByte_eq outputs _ (by omega), List.take_add_one, List.getElem?_drop,
      List.getElem?_eq_getElem (by omega), Option.toList_some, beInt_append,
      List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), Option.getD_some]
    rfl

theorem totalHeight_eq : FORS.totalHeight = 26 := rfl

/-- The statement's index is the model's value of the index bytes. -/
theorem digestIndex_val (outputs : DigestCall → HashOutput) :
    (digestIndex (truncateMessageDigest outputs)).val =
      FORS.digestIndexValue (FORS.digestOutputBytes (asModel outputs)) := by
  simp only [digestIndex, FORS.digestIndexValue, mdBytes_eq, treeIndexBytes_eq, leafIndexBytes_eq,
    bottomHeight_eq, totalHeight_eq, forsMessageByteCount, treeIndexByteCount, leafIndexByteCount,
    messageDigestBigEndian_eq outputs 30 3 (by omega),
    messageDigestBigEndian_eq outputs 33 1 (by omega)]

/-- The model's index is its value of the index bytes (at every shape). -/
theorem modelDigestIndex_val {P : FORS.Params} (outputs : FORS.DigestCall → FORS.HashOutput) :
    (FORS.Concrete.digestIndex (FORS.truncateMessageDigest outputs)).val =
      FORS.digestIndexValue (FORS.digestOutputBytes outputs) := by
  apply Nat.eq_of_testBit_eq
  intro q
  simp only [FORS.Concrete.digestIndex, BitVec.val_toFin, BitVec.testBit_toNat,
    BitVec.getLsbD_extractLsb', FORS.truncateMessageDigest, BitVec.getLsbD_ofNat,
    testBit_digestFieldsValue, Nat.zero_add]
  by_cases hq : q < FORS.totalHeight
  · have h2 : q < FORS.messageDigestBits := by unfold FORS.messageDigestBits; omega
    simp [hq, h2]
  · have hlt : FORS.digestIndexValue (FORS.digestOutputBytes outputs) < 2 ^ q :=
      lt_of_lt_of_le (digestIndexValue_lt _) (Nat.pow_le_pow_right (by decide) (by omega))
    simp [hq, Nat.testBit_lt_two_pow hlt]

/-- **The index**: the model's is the statement's. -/
theorem digestIndex_eq (outputs : DigestCall → HashOutput) :
    FORS.Concrete.digestIndex (FORS.truncateMessageDigest (asModel outputs)) =
      digestIndex (truncateMessageDigest outputs) :=
  Fin.ext ((modelDigestIndex_val (asModel outputs)).trans (digestIndex_val outputs).symm)

/-- The model's leaf of tree `κ` is the `a` bits of the leaf bytes from bit `a κ` (at every
shape). -/
theorem modelDigestLeaves_val {P : FORS.Params} (outputs : FORS.DigestCall → FORS.HashOutput)
    (κ : FORS.FTree) :
    (FORS.Concrete.digestLeaves (FORS.truncateMessageDigest outputs) κ).val =
      FORS.msbField (FORS.digestOutputBytes outputs) (FORS.forsHeight * κ.val) FORS.forsHeight := by
  have hoff := FORS.leafOffset_add_le κ
  have ha := FORS.forsHeight_pos
  apply Nat.eq_of_testBit_eq
  intro t
  simp only [FORS.Concrete.digestLeaves, BitVec.val_toFin, BitVec.testBit_toNat,
    BitVec.getLsbD_extractLsb', FORS.truncateMessageDigest, BitVec.getLsbD_ofNat,
    testBit_digestFieldsValue]
  by_cases ht : t < FORS.forsHeight
  · unfold FORS.Concrete.leafOffset at hoff ⊢
    have h1 : FORS.totalHeight + FORS.forsHeight * κ.val + t < FORS.messageDigestBits := by omega
    have h2 : ¬FORS.totalHeight + FORS.forsHeight * κ.val + t < FORS.totalHeight := by omega
    have h3 : (FORS.totalHeight + FORS.forsHeight * κ.val + t - FORS.totalHeight) /
        FORS.forsHeight = κ.val := by
      rw [show FORS.totalHeight + FORS.forsHeight * κ.val + t - FORS.totalHeight =
        t + FORS.forsHeight * κ.val by omega, Nat.add_mul_div_left _ _ ha, Nat.div_eq_of_lt ht,
        Nat.zero_add]
    have h4 : (FORS.totalHeight + FORS.forsHeight * κ.val + t - FORS.totalHeight) %
        FORS.forsHeight = t := by
      rw [show FORS.totalHeight + FORS.forsHeight * κ.val + t - FORS.totalHeight =
        t + FORS.forsHeight * κ.val by omega, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt ht]
    simp only [ht, h1, h2, h3, h4, κ.isLt, decide_true, Bool.true_and, ↓reduceIte, ↓reduceDIte]
  · have hlt := lt_of_lt_of_le (msbField_lt (FORS.digestOutputBytes outputs)
      (FORS.forsHeight * κ.val) FORS.forsHeight)
      (Nat.pow_le_pow_right (n := 2) (by decide) (show FORS.forsHeight ≤ t by omega))
    simp [ht, Nat.testBit_lt_two_pow hlt]

/-- Bit `p` of the statement's digest, read most significant bit first, is the calls'. -/
theorem messageDigestBit_eq (outputs : DigestCall → HashOutput) (p : ℕ) (hp : p < 272) :
    messageDigestBit (truncateMessageDigest outputs) p =
      FORS.msbBit (FORS.digestOutputBytes (asModel outputs)) p := by
  rw [messageDigestBit, messageDigestByte_eq outputs _ (by omega), FORS.msbBit]

/-- **The FORS leaves**: the model's are the statement's. -/
theorem digestLeaves_eq (outputs : DigestCall → HashOutput) :
    FORS.Concrete.digestLeaves (FORS.truncateMessageDigest (asModel outputs)) =
      digestForsLeaves (truncateMessageDigest outputs) := by
  funext κ
  apply Fin.ext
  rw [modelDigestLeaves_val]
  have hfold : (List.range forsTreeHeight).foldl (fun value j ↦ 2 * value +
        messageDigestBit (truncateMessageDigest outputs) (forsTreeHeight * κ.val + j)) 0 =
      FORS.msbField (FORS.digestOutputBytes (asModel outputs)) (FORS.forsHeight * κ.val)
        FORS.forsHeight := by
    unfold FORS.msbField
    refine List.foldl_ext _ _ _ fun value j hj ↦ ?_
    have hκ := κ.isLt
    have hj' := List.mem_range.mp hj
    change j < 10 at hj'
    change κ.val < 24 at hκ
    rw [messageDigestBit_eq outputs _ (by unfold forsTreeHeight; omega)]
    rfl
  have hlt := msbField_lt (FORS.digestOutputBytes (asModel outputs)) (FORS.forsHeight * κ.val)
    FORS.forsHeight
  simp only [digestForsLeaves, forsLeafOfNat, hfold]
  exact (Nat.mod_eq_of_lt hlt).symm

end Digest

/-! ## Verification -/

section Verification

open Verification

variable (parameter : FORS.PublicParameter)

theorem decodeDigest_eq (digest : Digest) :
    FORS.TargetSum.decodeDigest digest = TargetSum.decodeDigest digest := by
  have henc : FORS.TargetSum.digestEncoding digest = TargetSum.base2bDigits digest := rfl
  unfold FORS.TargetSum.decodeDigest TargetSum.decodeDigest
  rw [henc]
  rfl

theorem simulateQ_chainWalk (lay : FORS.Layer) (tree : FORS.TreeIndex) (leaf : FORS.LeafIndex)
    (chainIndex : FORS.ChainIndex) (start : ℕ) :
    ∀ (steps : ℕ) (value : FORS.Digest),
      simulateQ σ (FORS.Concrete.chainWalk (m := OracleComp FORS.HashSpec) parameter lay tree leaf
        chainIndex start steps value) =
        chainWalk hash parameter (toLayer lay) tree (toLeaf leaf) chainIndex start steps
          value
  | 0, value => by
    simp only [FORS.Concrete.chainWalk, chainWalk, walkChain]
    exact sim_pure _
  | steps + 1, value => by
    simp only [FORS.Concrete.chainWalk, sim_bind,
      simulateQ_chainWalk lay tree leaf chainIndex start steps]
    simp only [chainWalk, walkChain]
    refine bind_eq_of rfl fun previous ↦ ?_
    by_cases h : start + steps < 3
    · rw [dite_eq_left (show start + steps < FORS.chainLength - 1 from h),
        dite_eq_left (show start + steps < HashSig.chainLength - 1 from h)]
      simp only [simulateQ_tweakableHash _ (.chain _ _ _ _ _) trivial]
      rfl
    · rw [dite_eq_right (show ¬start + steps < FORS.chainLength - 1 from h),
        dite_eq_right (show ¬start + steps < HashSig.chainLength - 1 from h), sim_pure]
      rfl

theorem simulateQ_recoverChain (lay : FORS.Layer) (tree : FORS.TreeIndex) (leaf : FORS.LeafIndex)
    (chainIndex : FORS.ChainIndex) (digit : FORS.Digit) (value : FORS.Digest) :
    simulateQ σ (FORS.Concrete.recoverChain (m := OracleComp FORS.HashSpec) parameter lay tree leaf
      chainIndex digit value) =
      recoverChain hash parameter (toLayer lay) tree (toLeaf leaf) chainIndex digit
        value :=
  simulateQ_chainWalk parameter lay tree leaf chainIndex _ _ _

theorem simulateQ_leafHash (lay : FORS.Layer) (tree : FORS.TreeIndex) (leaf : FORS.LeafIndex)
    (endpoints : FORS.ChainIndex → FORS.Digest) :
    simulateQ σ (FORS.Concrete.leafHash (m := OracleComp FORS.HashSpec) parameter lay tree leaf
      endpoints) = leafHash hash parameter (toLayer lay) tree (toLeaf leaf) endpoints :=
  simulateQ_tweakableHash _ (.leaf lay tree leaf) trivial _

theorem simulateQ_encode (lay : FORS.Layer) (tree : FORS.TreeIndex) (leaf : FORS.LeafIndex)
    (message : FORS.Digest) (counter : FORS.Counter) :
    simulateQ σ (FORS.Concrete.encode (m := OracleComp FORS.HashSpec) parameter lay tree leaf
      (FORS.Concrete.rootPayload message) counter) =
      encode hash parameter (toLayer lay) tree (toLeaf leaf) message counter := by
  simp only [FORS.Concrete.encode, encode, sim_bind, sim_pure,
    simulateQ_tweakableHash _ (.encoding _ _ _) trivial]
  rfl

theorem simulateQ_otsLeaf (lay : FORS.Layer) (tree : FORS.TreeIndex) (leaf : FORS.LeafIndex)
    (message : FORS.Digest) (counter : FORS.Counter) (values : FORS.ChainIndex → FORS.Digest) :
    simulateQ σ (FORS.Concrete.otsLeaf (m := OracleComp FORS.HashSpec) parameter lay tree leaf
      (FORS.Concrete.rootPayload message) counter values) =
      otsLeaf hash parameter (toLayer lay) tree (toLeaf leaf) message counter
        values := by
  simp only [FORS.Concrete.otsLeaf, otsLeaf, sim_bind, simulateQ_encode]
  refine bind_eq_of rfl fun encoding ↦ ?_
  rcases encoding with _ | encoding
  · exact sim_pure _
  · simp only [sim_bind, sim_pure, simulateQ_sequenceFin, simulateQ_recoverChain,
      simulateQ_leafHash]
    rfl

theorem simulateQ_treeFold (lay : FORS.Layer) (tree : FORS.TreeIndex) (leaf : FORS.LeafIndex)
    (path : ℕ → FORS.Digest) :
    ∀ (levels : ℕ) (value : FORS.Digest),
      simulateQ σ (FORS.Concrete.treeFold (m := OracleComp FORS.HashSpec) parameter lay tree leaf
        path levels value) =
        treeFold hash parameter (toLayer lay) tree (toLeaf leaf) path levels value
  | 0, value => by
    simp only [FORS.Concrete.treeFold, treeFold, foldPath]
    exact sim_pure _
  | levels + 1, value => by
    simp only [FORS.Concrete.treeFold, sim_bind, simulateQ_treeFold lay tree leaf path levels]
    simp only [treeFold, foldPath]
    refine bind_eq_of rfl fun current ↦ ?_
    by_cases hbit : leaf.val.testBit levels = true
    · simp only [hbit, toLeaf, ↓reduceIte, simulateQ_tweakableHash _ (.node _ _ _ _) trivial]
      rfl
    · simp only [hbit, toLeaf, Bool.false_eq_true, ↓reduceIte,
        simulateQ_tweakableHash _ (.node _ _ _ _) trivial]
      rfl

theorem simulateQ_forsFold (index : FORS.Index) (forsTree : FORS.FTree) (leaf : FORS.FLeaf)
    (path : Fin FORS.forsHeight → FORS.Digest) :
    ∀ (levels : ℕ), levels ≤ 10 → ∀ (value : FORS.Digest),
      simulateQ σ (FORS.Concrete.forsFold (m := OracleComp FORS.HashSpec) parameter index forsTree
        leaf path levels value) =
        foldPath (fun level node ↦ tweakableHash hash parameter
            (.forsNode index forsTree (level + 1) node))
          leaf.val (fun level ↦ if h : level < forsTreeHeight then path ⟨level, h⟩ else 0)
          levels value
  | 0, _, value => by
    simp only [FORS.Concrete.forsFold, foldPath]
    exact sim_pure _
  | levels + 1, hlevels, value => by
    simp only [FORS.Concrete.forsFold, sim_bind,
      simulateQ_forsFold index forsTree leaf path levels (by omega)]
    simp only [foldPath]
    refine bind_eq_of rfl fun current ↦ ?_
    have hlevel : levels < FORS.forsHeight := show levels < 10 by omega
    have hlt : levels < forsTreeHeight := hlevel
    have hrange : InRange (.forsNode index forsTree ⟨levels, hlevel⟩
        ⟨leaf.val / 2 ^ (levels + 1), Nat.lt_of_le_of_lt (Nat.div_le_self _ _) leaf.isLt⟩) := by
      show leaf.val / 2 ^ (levels + 1) < 2 ^ (10 - (levels + 1))
      have hleaf : leaf.val < 2 ^ (10 - (levels + 1)) * 2 ^ (levels + 1) := by
        rw [← pow_add, show 10 - (levels + 1) + (levels + 1) = 10 by omega]
        exact leaf.isLt
      exact (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)).2 hleaf
    rw [dite_eq_left hlevel]
    simp only [hlt, ↓reduceDIte]
    by_cases hbit : leaf.val.testBit levels = true
    · simp only [hbit, ↓reduceIte, simulateQ_tweakableHash _ _ hrange]
      rfl
    · simp only [hbit, Bool.false_eq_true, ↓reduceIte, simulateQ_tweakableHash _ _ hrange]
      rfl

theorem simulateQ_forsTreeRecover (index : FORS.Index) (forsTree : FORS.FTree)
    (leaf : FORS.FLeaf) (opening : FORS.TreeOpening) :
    simulateQ σ (FORS.Concrete.treeRecover (m := OracleComp FORS.HashSpec) parameter index forsTree
      leaf opening) =
      forsTreeRecover hash parameter index forsTree leaf
        (ofModelTreeOpening opening) := by
  simp only [FORS.Concrete.treeRecover, forsTreeRecover, sim_bind, FORS.Concrete.forsLeafHash,
    simulateQ_tweakableHash _ (.forsLeaf _ _ _) trivial,
    simulateQ_forsFold _ _ _ _ _ FORS.forsHeight le_rfl]
  rfl

theorem simulateQ_forsRecover (index : FORS.Index) (leaves : FORS.FTree → FORS.FLeaf)
    (opening : FORS.FTree → FORS.TreeOpening) :
    (simulateQ σ (FORS.Concrete.forsRecover (m := OracleComp FORS.HashSpec) parameter index leaves
        opening) >>= fun roots ↦
      simulateQ σ (FORS.Concrete.forsPublicKey (m := OracleComp FORS.HashSpec) parameter index
        roots)) =
      forsRecover hash parameter index leaves
        (fun forsTree ↦ ofModelTreeOpening (opening forsTree)) := by
  simp only [FORS.Concrete.forsRecover, forsRecover, simulateQ_sequenceFin,
    simulateQ_forsTreeRecover, FORS.Concrete.forsPublicKey,
    simulateQ_tweakableHash _ (.forsRoots _) trivial]
  rfl

theorem simulateQ_messageDigestCall (root : FORS.Digest) (message : FORS.Message)
    (randomizer : FORS.Randomness) (call : FORS.DigestCall) :
    simulateQ σ (FORS.Concrete.messageDigestCall (m := OracleComp FORS.HashSpec) parameter root
      message randomizer call) =
      messageDigestCall hash randomizer parameter root message call := by
  simp only [FORS.Concrete.messageDigestCall, simulateQ_oracleHash, messageDigestCall]
  rfl

theorem signaturePath_eq (signature : Signature) (lay : FORS.Layer) :
    FORS.Concrete.signaturePath (toModelSignature signature) lay =
      layerPath signature (toLayer lay) := by
  funext level
  fin_cases lay <;> rfl

theorem simulateQ_verifyLayers (index : FORS.Index) (signature : Signature) :
    ∀ (layersLeft : ℕ) (message : FORS.Digest),
      simulateQ σ (FORS.Concrete.verifyLayers (m := OracleComp FORS.HashSpec) parameter index
        (toModelSignature signature) layersLeft (FORS.Concrete.rootPayload message)) =
        verifyLayers hash parameter index signature layersLeft message
  | 0, _ => by
    simp only [FORS.Concrete.verifyLayers, verifyLayers]
    exact sim_pure _
  | layersLeft + 1, message => by
    have ih := simulateQ_verifyLayers index signature layersLeft
    rw [FORS.Concrete.verifyLayers]
    simp only [verifyLayers]
    by_cases hlayer : layersLeft < 3
    · rw [dite_eq_left (show layersLeft < FORS.numLayers from hlayer),
        dite_eq_left (show layersLeft < layerCount from hlayer)]
      interval_cases layersLeft <;>
      · simp only [sim_bind, simulateQ_otsLeaf]
        refine bind_eq_of rfl fun found ↦ ?_
        rcases found with _ | value
        · exact sim_pure _
        · simp only [sim_bind, simulateQ_treeFold]
          refine bind_eq_of (by rw [signaturePath_eq]; rfl) fun root ↦ ?_
          simp only [↓reduceIte, Nat.succ_ne_zero, sim_pure, ih]
          rfl
    · rw [dite_eq_right (show ¬layersLeft < FORS.numLayers from hlayer),
        dite_eq_right (show ¬layersLeft < layerCount from hlayer), sim_pure]
      rfl

/-- **The verifier**: the model's, its queries answered by Keccak-256 over `π`, is the statement's,
through the maps. -/
theorem simulateQ_verify (publicKey : PublicKey) (message : FORS.Message) (signature : Signature) :
    simulateQ σ (FORS.Concrete.verify (m := OracleComp FORS.HashSpec) (toModelPublicKey publicKey)
      message (toModelSignature signature)) =
      verify hash publicKey message signature := by
  simp only [FORS.Concrete.verify, Verification.verify, FORS.Concrete.messageDigest,
    Verification.messageDigest, bind_assoc, pure_bind, sim_bind,
    simulateQ_sequenceFin, simulateQ_messageDigestCall]
  refine bind_eq_of rfl fun outputs ↦ ?_
  have hindex := digestIndex_eq outputs
  have hleaves := digestLeaves_eq outputs
  simp only [asModel] at hindex hleaves
  rw [hindex, hleaves]
  conv_lhs => rw [← bind_assoc]
  refine bind_eq_of (simulateQ_forsRecover _ _ _ _) fun forsKey ↦ ?_
  refine bind_eq_of (simulateQ_verifyLayers _ _ _ _ _) fun found ↦ ?_
  rcases found with _ | root
  · exact sim_pure _
  · exact sim_pure _

end Verification

end Sphincs.Model
