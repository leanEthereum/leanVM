module

public import Quantum.Qrom.Model
public import Statement.LeanSphincs

@[expose] public section

/-!
# leanSPHINCS over any hash

The statement's leanSPHINCS (`Statement/LeanSphincs.lean`) calls the permutation `π` only through
Keccak-256, `keccakHash π`. `LeanSphincsOver` copies every definition of the statement that
mentions `keccakHash π`, with `keccakHash π` replaced by a hash `hash : HashInput → m HashOutput`;
the shared combinators (`walkChain`, `foldPath`, `sequenceFin`, `merkleLevels`, `levelNode`, the
addresses and the payloads) are reused unchanged.

* `sphincsOver hash`: the scheme over `hash`, a `SchemeOver`.
* `sphincsOver_keccakHash`: **fidelity**, over Keccak-256 of the statement's `π` the copy is the
  statement's `RandomPermutationModel.sufCmaScheme`.
* `sphincs_hashInputs_le_maxLen`: every input the scheme hashes has at most `maxLen` bytes (the
  WOTS leaf, 1072 bytes, is the longest): two hashes agreeing on such inputs give the same scheme.
* `sphincsRom`: leanSPHINCS in the random-oracle model, `sphincsOver hashQ`.
-/

open OracleComp OracleSpec
open HashSig hiding PublicKey
open HashSig.OverPermutation (sequenceFin walkChain foldPath nodePayload keccakHash)
open Sphincs hiding HashDomain
open Sphincs.KeyGenerationAndSigning (ExpandedKey keyDerivationInput levelNode merkleLevels
  merkleLevelsFrom layerSignatures)
open Sphincs.Verification (layerPath)
open LeanVM.Semantics (KeccakState)

namespace Quantum.Qrom.Sphincs

namespace LeanSphincsOver

variable {m : Type → Type} [Monad m] (hash : HashInput → m HashOutput)

/-! ## Verification -/

/-- `Verification.addressedHash` over `hash`. -/
def addressedHash (publicSeed : PublicParameter) (address : Address) (payload : HashInput) :
    m Digest := do
  return truncateHash (← hash (addressedHashInput publicSeed address payload))

/-- `Verification.tweakableHash` over `hash`. -/
abbrev tweakableHash (publicSeed : PublicParameter) (domain : _root_.Sphincs.HashDomain)
    (payload : HashInput) : m Digest :=
  addressedHash hash publicSeed (hashDomainFields domain) payload

/-- `Verification.chainWalk` over `hash`. -/
def chainWalk (publicSeed : PublicParameter) (layer : Layer) (tree : TreeIndex)
    (leaf : TreeLeafIndex) (chainIndex : ChainIndex) : Nat → Nat → Digest → m Digest :=
  walkChain fun step value ↦
    tweakableHash hash publicSeed (.chain layer tree leaf chainIndex step)
      (littleEndianBytes 16 value)

/-- `Verification.recoverChain` over `hash`. -/
def recoverChain (publicSeed : PublicParameter) (layer : Layer) (tree : TreeIndex)
    (leaf : TreeLeafIndex) (chainIndex : ChainIndex) (digit : WinternitzDigit) (value : Digest) :
    m Digest :=
  chainWalk hash publicSeed layer tree leaf chainIndex digit.val (chainLength - 1 - digit.val) value

/-- `Verification.leafHash` over `hash`. -/
def leafHash (publicSeed : PublicParameter) (layer : Layer) (tree : TreeIndex)
    (leaf : TreeLeafIndex) (endpoints : ChainIndex → Digest) : m Digest :=
  tweakableHash hash publicSeed (.leaf layer tree leaf) (digestsPayload endpoints)

/-- `Verification.encode` over `hash`. -/
def encode (publicSeed : PublicParameter) (layer : Layer) (tree : TreeIndex)
    (leaf : TreeLeafIndex) (message : Digest) (counter : EncodingCounter) :
    m (Option Encoding) := do
  let digest ← tweakableHash hash publicSeed (.encoding layer tree leaf)
    (littleEndianBytes 16 message ++ bigEndianBytes 4 counter)
  return TargetSum.decodeDigest digest

/-- `Verification.otsLeaf` over `hash`. -/
def otsLeaf (publicSeed : PublicParameter) (layer : Layer) (tree : TreeIndex)
    (leaf : TreeLeafIndex) (message : Digest) (counter : EncodingCounter)
    (values : ChainIndex → Digest) : m (Option Digest) := do
  let some encoding ← encode hash publicSeed layer tree leaf message counter | return none
  let endpoints ← sequenceFin fun chainIndex =>
    recoverChain hash publicSeed layer tree leaf chainIndex (encoding chainIndex)
      (values chainIndex)
  let value ← leafHash hash publicSeed layer tree leaf endpoints
  return some value

/-- `Verification.treeFold` over `hash`. -/
def treeFold (publicSeed : PublicParameter) (layer : Layer) (tree : TreeIndex)
    (leaf : TreeLeafIndex) (path : Nat → Digest) : Nat → Digest → m Digest :=
  foldPath
    (fun level nodeIndex ↦ tweakableHash hash publicSeed (.node layer tree (level + 1) nodeIndex))
    leaf.val path

/-- `Verification.forsLeafHash` over `hash`. -/
def forsLeafHash (publicSeed : PublicParameter) (index : Index) (forsTree : ForsTreeIndex)
    (leaf : ForsLeafIndex) (secret : Digest) : m Digest :=
  tweakableHash hash publicSeed (.forsLeaf index forsTree leaf) (littleEndianBytes 16 secret)

/-- `Verification.forsTreeRecover` over `hash`. -/
def forsTreeRecover (publicSeed : PublicParameter) (index : Index) (forsTree : ForsTreeIndex)
    (leaf : ForsLeafIndex) (opening : ForsTreeOpening) : m Digest := do
  let value ← forsLeafHash hash publicSeed index forsTree leaf opening.secret
  foldPath
    (fun level node ↦ tweakableHash hash publicSeed (.forsNode index forsTree (level + 1) node))
    leaf.val (fun level ↦ if h : level < forsTreeHeight then opening.path ⟨level, h⟩ else 0)
    forsTreeHeight value

/-- `Verification.forsPublicKey` over `hash`. -/
def forsPublicKey (publicSeed : PublicParameter) (index : Index)
    (roots : ForsTreeIndex → Digest) : m Digest :=
  tweakableHash hash publicSeed (.forsRoots index) (digestsPayload roots)

/-- `Verification.forsRecover` over `hash`. -/
def forsRecover (publicSeed : PublicParameter) (index : Index)
    (leaves : ForsTreeIndex → ForsLeafIndex) (opening : ForsTreeIndex → ForsTreeOpening) :
    m Digest := do
  let roots ← sequenceFin fun forsTree =>
    forsTreeRecover hash publicSeed index forsTree (leaves forsTree) (opening forsTree)
  forsPublicKey hash publicSeed index roots

/-- `Verification.messageDigestCall` over `hash`. -/
def messageDigestCall (randomizer : Randomizer) (publicSeed : PublicParameter) (root : Digest)
    (message : Message) (call : DigestCall) : m HashOutput :=
  hash (littleEndianBytes 16 randomizer ++ littleEndianBytes 16 publicSeed ++
    littleEndianBytes 16 root ++ littleEndianBytes 32 message ++
    bigEndianBytes 4 (BitVec.ofNat 32 call.val))

/-- `Verification.messageDigest` over `hash`. -/
def messageDigest (publicKey : PublicKey) (randomizer : Randomizer) (message : Message) :
    m MessageDigest := do
  let outputs ← sequenceFin fun call =>
    messageDigestCall hash randomizer publicKey.publicSeed publicKey.root message call
  return truncateMessageDigest outputs

/-- `Verification.verifyLayers` over `hash`. -/
def verifyLayers (publicSeed : PublicParameter) (index : Index) (signature : Signature) :
    Nat → Digest → m (Option Digest)
  | 0, _ => pure none
  | layersLeft + 1, message => do
      if hlayer : layersLeft < layerCount then
        let layer : Layer := ⟨layerCount - 1 - layersLeft, by omega⟩
        let tree := treeOfIndex layer index
        let leaf := leafOfIndex layer index
        let some value ← otsLeaf hash publicSeed layer tree leaf message
            (signature.layers layer).counter (signature.layers layer).chainValues
          | return none
        let root ← treeFold hash publicSeed layer tree leaf (layerPath signature layer)
          (layerHeight layer) value
        if layersLeft = 0 then
          return some root
        else
          verifyLayers publicSeed index signature layersLeft root
      else
        pure none

/-- `Verification.verify` over `hash`. -/
def verify (publicKey : PublicKey) (message : Message) (signature : Signature) : m Bool := do
  let digest ← messageDigest hash publicKey signature.randomizer message
  let index := digestIndex digest
  let forsKey ← forsRecover hash publicKey.publicSeed index (digestForsLeaves digest)
    signature.forsOpening
  let some root ← verifyLayers hash publicKey.publicSeed index signature layerCount forsKey
    | return false
  return decide (root = publicKey.root)

/-! ## Key generation and signing -/

/-- `KeyGenerationAndSigning.expandKey` over `hash`. -/
def expandKey (secretSeed : SecretKey) : m ExpandedKey := do
  let secretPrfKey ← hash (keyDerivationInput secretSeed 1)
  let publicSeedOutput ← hash (keyDerivationInput secretSeed 0)
  return ⟨secretSeed, secretPrfKey, truncateHash publicSeedOutput⟩

/-- `KeyGenerationAndSigning.prf` over `hash`. -/
def prf (key : ExpandedKey) (domain : KeygenDomain) : m Digest :=
  addressedHash hash key.publicSeed (keygenDomainFields domain)
    (littleEndianBytes 32 key.secretSeed)

/-- `KeyGenerationAndSigning.prfMessage` over `hash`. -/
def prfMessage (secretPrfKey : HashOutput) (optionalRandomness : Digest) (message : Message) :
    m Randomizer := do
  return truncateHash (← hash (littleEndianBytes 32 secretPrfKey ++
    littleEndianBytes 16 optionalRandomness ++ framedMessage message))

/-- `KeyGenerationAndSigning.otsSecrets` over `hash`. -/
def otsSecrets (key : ExpandedKey) (layer : Layer) (tree : TreeIndex) (leaf : TreeLeafIndex) :
    m (ChainIndex → Digest) :=
  sequenceFin fun chainIndex ↦ prf hash key (.oneTimeChain layer tree leaf chainIndex)

/-- `KeyGenerationAndSigning.otsPublicLeaf` over `hash`. -/
def otsPublicLeaf (key : ExpandedKey) (layer : Layer) (tree : TreeIndex) (leaf : TreeLeafIndex) :
    m Digest := do
  let secrets ← otsSecrets hash key layer tree leaf
  let endpoints ← sequenceFin fun chainIndex =>
    chainWalk hash key.publicSeed layer tree leaf chainIndex 0 (chainLength - 1)
      (secrets chainIndex)
  leafHash hash key.publicSeed layer tree leaf endpoints

/-- `KeyGenerationAndSigning.otsSignFrom` over `hash`. -/
def otsSignFrom (key : ExpandedKey) (layer : Layer) (tree : TreeIndex) (leaf : TreeLeafIndex)
    (message : Digest) : Nat → Nat → m (Option (EncodingCounter × (ChainIndex → Digest)))
  | 0, _ => pure none
  | attempts + 1, counter => do
      match ← encode hash key.publicSeed layer tree leaf message
          (BitVec.ofNat counterBits counter) with
      | some encoding => do
          let secrets ← otsSecrets hash key layer tree leaf
          let values ← sequenceFin fun chainIndex =>
            chainWalk hash key.publicSeed layer tree leaf chainIndex 0 (encoding chainIndex).val
              (secrets chainIndex)
          return some (BitVec.ofNat counterBits counter, values)
      | none => otsSignFrom key layer tree leaf message attempts (counter + 1)

/-- `KeyGenerationAndSigning.otsSign` over `hash`. -/
def otsSign (key : ExpandedKey) (layer : Layer) (tree : TreeIndex) (leaf : TreeLeafIndex)
    (message : Digest) : m (Option (EncodingCounter × (ChainIndex → Digest))) :=
  otsSignFrom hash key layer tree leaf message encodingAttemptLimit 0

/-- `KeyGenerationAndSigning.treeLevels` over `hash`. -/
def treeLevels (key : ExpandedKey) (layer : Layer) (tree : TreeIndex) :
    m (List (List Digest)) := do
  let leaves ← (List.range (2 ^ layerHeight layer)).mapM fun leaf ↦
    otsPublicLeaf hash key layer tree (leafOfNat leaf)
  merkleLevels
    (fun height nodeIndex ↦ tweakableHash hash key.publicSeed (.node layer tree height nodeIndex))
    leaves (layerHeight layer)

/-- `KeyGenerationAndSigning.forsSecret` over `hash`. -/
def forsSecret (key : ExpandedKey) (index : Index) (forsTree : ForsTreeIndex)
    (leaf : ForsLeafIndex) : m Digest :=
  prf hash key (.forsSecret index forsTree leaf)

/-- `KeyGenerationAndSigning.forsTreeOpen` over `hash`. -/
def forsTreeOpen (key : ExpandedKey) (index : Index) (forsTree : ForsTreeIndex)
    (leaf : ForsLeafIndex) : m (Digest × ForsTreeOpening) := do
  let secrets ← (List.range (2 ^ forsTreeHeight)).mapM fun s ↦
    forsSecret hash key index forsTree (forsLeafOfNat s)
  let leafHashes ← (List.range (2 ^ forsTreeHeight)).mapM fun s ↦
    forsLeafHash hash key.publicSeed index forsTree (forsLeafOfNat s) (secrets.getD s 0)
  let levels ← merkleLevels
    (fun height node ↦ tweakableHash hash key.publicSeed (.forsNode index forsTree height node))
    leafHashes forsTreeHeight
  return (levelNode levels forsTreeHeight 0,
    ⟨secrets.getD leaf.val 0, fun z ↦ levelNode levels z.val ((leaf.val >>> z.val) ^^^ 1)⟩)

/-- `KeyGenerationAndSigning.forsOpen` over `hash`. -/
def forsOpen (key : ExpandedKey) (index : Index) (leaves : ForsTreeIndex → ForsLeafIndex) :
    m (Digest × (ForsTreeIndex → ForsTreeOpening)) := do
  let trees ← sequenceFin fun forsTree => forsTreeOpen hash key index forsTree (leaves forsTree)
  let forsKey ← forsPublicKey hash key.publicSeed index fun forsTree => (trees forsTree).1
  return (forsKey, fun forsTree => (trees forsTree).2)

/-- `KeyGenerationAndSigning.keygenInternal` over `hash`. -/
def keygenInternal (key : ExpandedKey) : m (PublicKey × List (List Digest)) := do
  let top ← treeLevels hash key topLayer 0
  return (⟨key.publicSeed, levelNode top (layerHeight topLayer) 0⟩, top)

/-- `KeyGenerationAndSigning.keygenFromSeed` over `hash`. -/
def keygenFromSeed (secretSeed : SecretKey) : m (PublicKey × SecretKey) := do
  let key ← expandKey hash secretSeed
  let (publicKey, _) ← keygenInternal hash key
  return (publicKey, secretSeed)

/-- `KeyGenerationAndSigning.signLayer` over `hash`. -/
def signLayer (key : ExpandedKey) (top : List (List Digest)) (index : Index) (layer : Layer)
    (message : Digest) : m (Option (LayerSignature layer × Digest)) := do
  let tree := treeOfIndex layer index
  let leaf := leafOfIndex layer index
  let some (counter, values) ← otsSign hash key layer tree leaf message | return none
  let levels ← if layer = topLayer then pure top else treeLevels hash key layer tree
  return some (⟨counter, values, fun z ↦ levelNode levels z.val ((leaf.val >>> z.val) ^^^ 1)⟩,
    levelNode levels (layerHeight layer) 0)

/-- `KeyGenerationAndSigning.signWithExpandedKey` over `hash`. -/
def signWithExpandedKey (key : ExpandedKey) (message : Message) : m (Option Signature) := do
  let (publicKey, top) ← keygenInternal hash key
  let randomizer ← prfMessage hash key.secretPrfKey key.publicSeed message
  let digest ← messageDigest hash publicKey randomizer message
  let index := digestIndex digest
  let (forsKey, forsOpening) ← forsOpen hash key index (digestForsLeaves digest)
  let some (bottom, bottomRoot) ← signLayer hash key top index 0 forsKey | return none
  let some (middle, middleRoot) ← signLayer hash key top index 1 bottomRoot | return none
  let some (topSignature, _) ← signLayer hash key top index 2 middleRoot | return none
  return some ⟨randomizer, forsOpening, layerSignatures bottom middle topSignature⟩

/-- `KeyGenerationAndSigning.sign` over `hash`. -/
def sign (secretKey : SecretKey) (message : Message) : m (Option Signature) := do
  let key ← expandKey hash secretKey
  signWithExpandedKey hash key message

/-! ## Fidelity: over `keccakHash π`, the statement's definitions -/

section fidelity

variable (π : KeccakState → m KeccakState)

theorem verifyLayers_keccakHash :
    verifyLayers (keccakHash π) = Verification.verifyLayers π := by
  funext publicSeed index signature layersLeft message
  induction layersLeft generalizing message with
  | zero => rfl
  | succ layersLeft ih =>
    simp only [verifyLayers, Verification.verifyLayers, ih]
    rfl

theorem verify_keccakHash : verify (keccakHash π) = Verification.verify π := by
  funext publicKey message signature
  unfold verify
  rw [verifyLayers_keccakHash]
  rfl

theorem keygenFromSeed_keccakHash :
    keygenFromSeed (keccakHash π) = KeyGenerationAndSigning.keygenFromSeed π :=
  rfl

theorem otsSignFrom_keccakHash :
    otsSignFrom (keccakHash π) = KeyGenerationAndSigning.otsSignFrom π := by
  funext key layer tree leaf message attempts counter
  induction attempts generalizing counter with
  | zero => rfl
  | succ attempts ih =>
    simp only [otsSignFrom, KeyGenerationAndSigning.otsSignFrom, ih]
    rfl

theorem sign_keccakHash : sign (keccakHash π) = KeyGenerationAndSigning.sign π := by
  funext secretKey message
  unfold sign signWithExpandedKey signLayer otsSign
  rw [otsSignFrom_keccakHash]
  rfl

end fidelity

/-! ## Every hashed input has at most `maxLen` bytes -/

section congr

variable {hash} {hash' : HashInput → m HashOutput}

private theorem length_digestsPayload {n : Nat} (digests : Fin n → Digest) :
    (digestsPayload digests).length = 16 * n := by
  have h : ∀ l : List (BitVec (8 * 16)),
      (l.flatMap (littleEndianBytes 16)).length = 16 * l.length := by
    intro l
    induction l with
    | nil => rfl
    | cons a l ih =>
      rw [List.flatMap_cons, List.length_append, ih, List.length_cons, littleEndianBytes,
        List.length_ofFn]
      ring
  exact (h (List.ofFn digests)).trans (congrArg (16 * ·) (List.length_ofFn (f := digests)))

private theorem length_nodePayload (left right : Digest) :
    (nodePayload left right).length = 32 := by
  simp only [nodePayload, List.length_append, littleEndianBytes, List.length_ofFn]

private theorem length_addressedHashInput (publicSeed : PublicParameter) (address : Address)
    (payload : HashInput) :
    (addressedHashInput publicSeed address payload).length = 48 + payload.length := by
  simp only [addressedHashInput, hasherInput, Address.toBytes, List.length_append,
    littleEndianBytes, bigEndianBytes, List.length_ofFn]

/-- Two hashes agreeing on the inputs of at most `maxLen` bytes. -/
abbrev AgreeOnDomain (hash hash' : HashInput → m HashOutput) : Prop :=
  ∀ l : HashInput, l.length ≤ maxLen → hash l = hash' l

theorem addressedHash_congr (hH : AgreeOnDomain hash hash') (publicSeed : PublicParameter)
    (address : Address) {payload : HashInput} (hp : payload.length ≤ 1040) :
    addressedHash hash publicSeed address payload =
      addressedHash hash' publicSeed address payload := by
  unfold addressedHash
  rw [hH _ (by rw [length_addressedHashInput, maxLen]; omega)]

theorem foldPath_tweakable_congr (hH : AgreeOnDomain hash hash') (publicSeed : PublicParameter)
    (domain : Nat → Nat → _root_.Sphincs.HashDomain) :
    foldPath (fun level index ↦ tweakableHash hash publicSeed (domain level index)) =
      foldPath (fun level index ↦ tweakableHash hash' publicSeed (domain level index)) := by
  funext leafIndex sibling levels value
  induction levels generalizing value with
  | zero => rfl
  | succ levels ih =>
    simp only [foldPath, ih]
    congr 1
    funext current
    split_ifs <;> exact addressedHash_congr hH _ _ (by rw [length_nodePayload]; omega)

theorem merkleLevels_tweakable_congr (hH : AgreeOnDomain hash hash')
    (publicSeed : PublicParameter) (domain : Nat → Nat → _root_.Sphincs.HashDomain) :
    merkleLevels (fun level index ↦ tweakableHash hash publicSeed (domain level index)) =
      merkleLevels (fun level index ↦ tweakableHash hash' publicSeed (domain level index)) := by
  funext leaves levels
  unfold merkleLevels
  generalize 0 = height
  induction levels generalizing height leaves with
  | zero => rfl
  | succ levels ih =>
    simp only [merkleLevelsFrom, ih]
    congr 1
    congr 1
    funext j
    exact addressedHash_congr hH _ _ (by rw [length_nodePayload]; omega)

theorem chainWalk_congr (hH : AgreeOnDomain hash hash') : chainWalk hash = chainWalk hash' := by
  funext publicSeed layer tree leaf chainIndex
  unfold chainWalk
  congr 1
  funext step value
  exact addressedHash_congr hH _ _ (by simp [littleEndianBytes])

theorem leafHash_congr (hH : AgreeOnDomain hash hash') : leafHash hash = leafHash hash' := by
  funext publicSeed layer tree leaf endpoints
  exact addressedHash_congr hH _ _ (by rw [length_digestsPayload]; decide)

theorem encode_congr (hH : AgreeOnDomain hash hash') : encode hash = encode hash' := by
  funext publicSeed layer tree leaf message counter
  unfold encode
  rw [tweakableHash, addressedHash_congr hH _ _ (by simp [littleEndianBytes, bigEndianBytes])]

theorem otsLeaf_congr (hH : AgreeOnDomain hash hash') : otsLeaf hash = otsLeaf hash' := by
  funext publicSeed layer tree leaf message counter values
  simp only [otsLeaf, recoverChain, encode_congr hH, chainWalk_congr hH, leafHash_congr hH]

theorem treeFold_congr (hH : AgreeOnDomain hash hash') : treeFold hash = treeFold hash' := by
  funext publicSeed layer tree leaf path
  exact congrFun (congrFun (foldPath_tweakable_congr hH publicSeed _) _) _

theorem forsLeafHash_congr (hH : AgreeOnDomain hash hash') :
    forsLeafHash hash = forsLeafHash hash' := by
  funext publicSeed index forsTree leaf secret
  exact addressedHash_congr hH _ _ (by simp [littleEndianBytes])

theorem forsPublicKey_congr (hH : AgreeOnDomain hash hash') :
    forsPublicKey hash = forsPublicKey hash' := by
  funext publicSeed index roots
  exact addressedHash_congr hH _ _ (by rw [length_digestsPayload]; decide)

theorem forsRecover_congr (hH : AgreeOnDomain hash hash') :
    forsRecover hash = forsRecover hash' := by
  funext publicSeed index leaves opening
  simp only [forsRecover, forsTreeRecover, forsLeafHash_congr hH,
    foldPath_tweakable_congr hH publicSeed, forsPublicKey_congr hH]

theorem messageDigest_congr (hH : AgreeOnDomain hash hash') :
    messageDigest hash = messageDigest hash' := by
  funext publicKey randomizer message
  simp only [messageDigest, messageDigestCall]
  congr 2
  funext call
  exact hH _ (by simp [littleEndianBytes, bigEndianBytes, maxLen])

theorem verifyLayers_congr (hH : AgreeOnDomain hash hash') :
    verifyLayers hash = verifyLayers hash' := by
  funext publicSeed index signature layersLeft message
  induction layersLeft generalizing message with
  | zero => rfl
  | succ layersLeft ih => simp only [verifyLayers, otsLeaf_congr hH, treeFold_congr hH, ih]

theorem verify_congr (hH : AgreeOnDomain hash hash') : verify hash = verify hash' := by
  funext publicKey message signature
  simp only [verify, messageDigest_congr hH, forsRecover_congr hH, verifyLayers_congr hH]

theorem expandKey_congr (hH : AgreeOnDomain hash hash') : expandKey hash = expandKey hash' := by
  funext secretSeed
  have hl : ∀ d, (keyDerivationInput secretSeed d).length ≤ maxLen := fun d ↦ by
    simp [keyDerivationInput, seedTag, littleEndianBytes, maxLen]
  simp only [expandKey, hH _ (hl 0), hH _ (hl 1)]

theorem prf_congr (hH : AgreeOnDomain hash hash') : prf hash = prf hash' := by
  funext key domain
  exact addressedHash_congr hH _ _ (by simp [littleEndianBytes])

theorem prfMessage_congr (hH : AgreeOnDomain hash hash') :
    prfMessage hash = prfMessage hash' := by
  funext secretPrfKey optionalRandomness message
  unfold prfMessage
  rw [hH _ (by simp [framedMessage, contextString, seedTag, littleEndianBytes, maxLen])]

theorem otsPublicLeaf_congr (hH : AgreeOnDomain hash hash') :
    otsPublicLeaf hash = otsPublicLeaf hash' := by
  funext key layer tree leaf
  simp only [otsPublicLeaf, otsSecrets, prf_congr hH, chainWalk_congr hH, leafHash_congr hH]

theorem otsSign_congr (hH : AgreeOnDomain hash hash') : otsSign hash = otsSign hash' := by
  funext key layer tree leaf message
  unfold otsSign
  generalize encodingAttemptLimit = attempts
  generalize 0 = counter
  induction attempts generalizing counter with
  | zero => rfl
  | succ attempts ih =>
    simp only [otsSignFrom, otsSecrets, encode_congr hH, prf_congr hH, chainWalk_congr hH, ih]

theorem treeLevels_congr (hH : AgreeOnDomain hash hash') :
    treeLevels hash = treeLevels hash' := by
  funext key layer tree
  simp only [treeLevels, otsPublicLeaf_congr hH, merkleLevels_tweakable_congr hH key.publicSeed]

theorem keygenFromSeed_congr (hH : AgreeOnDomain hash hash') :
    keygenFromSeed hash = keygenFromSeed hash' := by
  funext secretSeed
  simp only [keygenFromSeed, keygenInternal, expandKey_congr hH, treeLevels_congr hH]

theorem forsOpen_congr (hH : AgreeOnDomain hash hash') : forsOpen hash = forsOpen hash' := by
  funext key index leaves
  simp only [forsOpen, forsTreeOpen, forsSecret, prf_congr hH, forsLeafHash_congr hH,
    merkleLevels_tweakable_congr hH key.publicSeed, forsPublicKey_congr hH]

theorem signLayer_congr (hH : AgreeOnDomain hash hash') : signLayer hash = signLayer hash' := by
  funext key top index layer message
  simp only [signLayer, otsSign_congr hH, treeLevels_congr hH]

theorem sign_congr (hH : AgreeOnDomain hash hash') : sign hash = sign hash' := by
  funext secretKey message
  simp only [sign, signWithExpandedKey, keygenInternal, expandKey_congr hH, treeLevels_congr hH,
    prfMessage_congr hH, messageDigest_congr hH, forsOpen_congr hH, signLayer_congr hH]

end congr

end LeanSphincsOver

/-! ## The scheme -/

open LeanSphincsOver

/-- **leanSPHINCS over the hash `hash`**: the statement's seed sampler and winning condition, key
generation, signer and verifier over `hash`. -/
noncomputable def sphincsOver {ι : Type} {O : OracleSpec.{0, 0} ι}
    (hash : HashInput → OracleComp O HashOutput) :
    SchemeOver O MasterSeed PublicKey SecretKey Message (Option Signature) Forgery where
  sampleSeed := sampleMasterSeed
  generateKeys := keygenFromSeed hash
  sign sk message := LeanSphincsOver.sign hash sk message
  verify pk forgery := LeanSphincsOver.verify hash pk forgery.message forgery.signature
  winningCondition := RandomPermutationModel.sufCmaScheme.winningCondition

/-- **Fidelity**: over Keccak-256 of the statement's `π`, the copy is the statement's scheme. -/
theorem sphincsOver_keccakHash :
    (sphincsOver (keccakHash Common.queryPermutation)).toScheme =
      RandomPermutationModel.sufCmaScheme := by
  simp only [SchemeOver.toScheme, sphincsOver, keygenFromSeed_keccakHash, sign_keccakHash,
    verify_keccakHash]
  rfl

/-- **Every input leanSPHINCS hashes has at most `maxLen` bytes**: key generation, the signer
and the verifier only call `hash` on such inputs, so two hashes agreeing on them give the same
scheme. -/
theorem sphincs_hashInputs_le_maxLen {ι : Type} {O : OracleSpec.{0, 0} ι}
    {hash hash' : HashInput → OracleComp O HashOutput}
    (hH : ∀ l : HashInput, l.length ≤ maxLen → hash l = hash' l) :
    sphincsOver hash = sphincsOver hash' := by
  simp only [sphincsOver, keygenFromSeed_congr hH, sign_congr hH, verify_congr hH]

/-- **leanSPHINCS in the random-oracle model**: every Keccak-256 call is one call of `H`. -/
noncomputable def sphincsRom :
    SchemeOver RomOracles MasterSeed PublicKey SecretKey Message (Option Signature) Forgery :=
  sphincsOver hashQ

end Quantum.Qrom.Sphincs

end
