module

public import Quantum.Qrom.Model
public import Statement.LeanXmss

@[expose] public section

/-!
# leanXMSS over any hash

The statement's leanXMSS (`Statement/LeanXmss.lean`) hashes with Keccak-256 over a permutation `π`
(`keccakHash π`), through `th`, `thPair` and `schemeSeedOf` only. `Over` copies each definition
that mentions `keccakHash π`, verbatim with `keccakHash π` replaced by a hash
`hash : HashInput → m HashOutput`; the shared `HashSig` combinators (`walkChain`, `foldPath`,
`buildTree`, `sequenceFin`) and every hash-free definition are the statement's.

* `xmssOver hash`: the scheme over any oracles `O`, given the hash as an `O`-computation.
* `xmssOver_keccakHash` (**fidelity**): over Keccak-256 with the statement's `π`, it is the
  statement's `LeanXmss.RandomPermutationModel.sufCmaScheme`.
* `xmss_hashInputs_le_maxLen`: every input the scheme hashes has at most `maxLen` bytes, per call
  site (`length_thInput_chain` and its siblings): two hashes that agree on such inputs give the
  same scheme.
* `xmssRom := xmssOver hashQ`: leanXMSS in the random-oracle model.
-/

open OracleComp OracleSpec
open HashSig HashSig.OverPermutation LeanXmss

namespace Quantum.Qrom.Xmss

namespace Over

variable {m : Type → Type} [Monad m] (hash : HashInput → m HashOutput)

/-! ## The tweakable hash -/

/-- `Th(P, A, M) = Truncate_16(H(P || A || M))`. -/
def th (parameter : PublicParameter) (fields : TweakFields) (payload : HashInput) : m Digest := do
  return truncateHash (← hash (thInput parameter fields payload))

/-- `H(P || A || M)`, untruncated. -/
def thPair (parameter : PublicParameter) (fields : TweakFields) (payload : HashInput) :
    m HashOutput :=
  hash (thInput parameter fields payload)

/-- `S = H("leanXMSS" || S_0)`, all 32 bytes. -/
def schemeSeedOf (masterSeed : MasterSeed) : m MasterSeed :=
  hash (seedTag ++ littleEndianBytes 32 masterSeed)

/-! ## Verification -/

/-- The tweakable hash at a hash domain's address. -/
abbrev tweakableHash (parameter : PublicParameter) (domain : LeanXmss.HashDomain)
    (payload : HashInput) : m Digest :=
  th hash parameter (hashDomainFields domain) payload

/-- Chain `i` of a one-time key. -/
def chainWalk (parameter : PublicParameter) (layer : Layer) (key : KeyIndex)
    (chainIndex : ChainIndex) : Nat → Nat → Digest → m Digest :=
  walkChain fun step value ↦
    tweakableHash hash parameter (.chain layer key step)
      (Verification.chainPayload chainIndex value)

/-- The verifier's half of a chain. -/
def recoverChain (parameter : PublicParameter) (layer : Layer) (key : KeyIndex)
    (chainIndex : ChainIndex) (digit : WinternitzDigit) (value : Digest) : m Digest :=
  chainWalk hash parameter layer key chainIndex digit.val (chainLength - 1 - digit.val) value

/-- The one-time leaf. -/
def leafHash (parameter : PublicParameter) (layer : Layer) (key : KeyIndex)
    (endpoints : ChainIndex → Digest) : m Digest :=
  tweakableHash hash parameter (.leaf layer key) (digestsPayload endpoints)

/-- `D = Th(P, A_msg(l, e), M || rho)`. -/
def messageDigest (parameter : PublicParameter) (layer : Layer) (key : KeyIndex)
    (message : HashInput) (randomizer : Randomizer) : m Digest :=
  tweakableHash hash parameter (.message layer key) (message ++ littleEndianBytes 16 randomizer)

/-- The leaf a claimed one-time signature recovers, or nothing. -/
def otsLeaf (parameter : PublicParameter) (layer : Layer) (key : KeyIndex) (message : HashInput)
    (randomizer : Randomizer) (values : ChainIndex → Digest) : m (Option Digest) := do
  let digest ← messageDigest hash parameter layer key message randomizer
  let some encoding := Codeword.decode digest | return none
  let endpoints ← sequenceFin fun chainIndex =>
    recoverChain hash parameter layer key chainIndex (encoding chainIndex) (values chainIndex)
  let value ← leafHash hash parameter layer key endpoints
  return some value

/-- Fold a key's leaf and path into its tree's root. -/
def treeFold (parameter : PublicParameter) (layer : Layer) (key : KeyIndex)
    (path : Fin layerHeight → Digest) : Nat → Digest → m Digest :=
  foldPath (fun level nodeIndex ↦ tweakableHash hash parameter (.node layer (level + 1) nodeIndex))
    key.val fun level ↦ if h : level < layerHeight then path ⟨level, h⟩ else 0

/-- The root a layer's signature by key `e` reaches from `message`, or nothing. -/
def layerRoot (parameter : PublicParameter) (layer : Layer) (key : KeyIndex) (message : HashInput)
    (layerSignature : LayerSignature) : m (Option Digest) := do
  let some leaf ← otsLeaf hash parameter layer key message layerSignature.randomizer
      layerSignature.chainValues | return none
  let root ← treeFold hash parameter layer key layerSignature.authenticationPath layerHeight leaf
  return some root

/-- `Ver(pk, m, sigma)`. -/
def verify (publicKey : PublicKey) (message : Message) (signature : Signature) : m Bool := do
  let leafIndex := signature.leafIndex
  let some bottomRoot ← layerRoot hash publicKey.parameter bottomLayer
      (keyIndexOnLayer leafIndex bottomLayer) (littleEndianBytes 32 message)
      (signature.layers bottomLayer) | return false
  let some root ← layerRoot hash publicKey.parameter topLayer (keyIndexOnLayer leafIndex topLayer)
      (littleEndianBytes 16 bottomRoot) (signature.layers topLayer) | return false
  return decide (root = publicKey.root)

/-! ## Key generation and signing -/

/-- The starts of the `v` chains of a one-time key, from 29 seed derivations. -/
def otsSecrets (parameter : PublicParameter) (layer : Layer) (key : KeyIndex) (seed : MasterSeed) :
    m (ChainIndex → Digest) := do
  let outputs ← sequenceFin fun chainPairIndex : ChainPairIndex =>
    thPair hash parameter (keygenDomainFields (.oneTimeChainPair layer key chainPairIndex))
      (littleEndianBytes 32 seed)
  return fun chainIndex => hashHalfForChain chainIndex.val (outputs (chainPair chainIndex))

/-- The chain ends of a one-time key. -/
def oneTimePublicKey (parameter : PublicParameter) (layer : Layer) (key : KeyIndex)
    (seed : MasterSeed) : m (ChainIndex → Digest) := do
  let secrets ← otsSecrets hash parameter layer key seed
  sequenceFin fun chainIndex =>
    chainWalk hash parameter layer key chainIndex 0 (chainLength - 1) (secrets chainIndex)

/-- The randomizer trials `R0 + c, R0 + c + 1, ...`, stopping at the first codeword. -/
def otsSignFrom (parameter : PublicParameter) (layer : Layer) (key : KeyIndex) (seed : MasterSeed)
    (message : HashInput) (randomizerBase : Randomizer) :
    Nat → Nat → m (Option (Randomizer × (ChainIndex → Digest)))
  | 0, _ => pure none
  | attempts + 1, trial => do
      let randomizer := randomizerBase + BitVec.ofNat digestBits trial
      let digest ← messageDigest hash parameter layer key message randomizer
      match Codeword.decode digest with
      | some encoding => do
          let secrets ← otsSecrets hash parameter layer key seed
          let values ← sequenceFin fun chainIndex =>
            chainWalk hash parameter layer key chainIndex 0 (encoding chainIndex).val
              (secrets chainIndex)
          return some (randomizer, values)
      | none => otsSignFrom parameter layer key seed message randomizerBase attempts (trial + 1)

/-- Derive `R0`, take the least admissible trial, then open the chains. -/
def otsSign (parameter : PublicParameter) (layer : Layer) (key : KeyIndex) (seed : MasterSeed)
    (message : HashInput) : m (Option (Randomizer × (ChainIndex → Digest))) := do
  let randomizerBase ← th hash parameter (tweakFields 7 0 (layerHi layer 0) key)
    (littleEndianBytes 32 seed ++ message)
  otsSignFrom hash parameter layer key seed message randomizerBase randomizerAttemptLimit 0

/-- Node `nodeIndex` at tree level `level` of layer `l`. -/
def treeNode (parameter : PublicParameter) (layer : Layer) (seed : MasterSeed) : Nat → Nat
    → m Digest :=
  buildTree (fun nodeIndex ↦ do
      let key : KeyIndex := ⟨nodeIndex % lifetime, Nat.mod_lt _ (by decide)⟩
      leafHash hash parameter layer key (← oneTimePublicKey hash parameter layer key seed))
    fun level nodeIndex ↦ tweakableHash hash parameter (.node layer (level + 1) nodeIndex)

/-- The authentication path of key `e`. -/
def treePath (parameter : PublicParameter) (layer : Layer) (seed : MasterSeed) (key : KeyIndex) :
    m (Fin layerHeight → Digest) :=
  sequenceFin fun level =>
    treeNode hash parameter layer seed level.val (Nat.xor (key.val / 2 ^ level.val) 1)

/-- The public parameter of the scheme seed `S`. -/
def publicParameterOf (seed : MasterSeed) : m PublicParameter :=
  th hash 0 (keygenDomainFields .parameter) (littleEndianBytes 32 seed)

/-- `Gen`: hash `S_0` into `S`, derive the public parameter and build the top tree. -/
def keygenFromSeed (masterSeed : MasterSeed) : m (PublicKey × SecretKey) := do
  let seed ← schemeSeedOf hash masterSeed
  let parameter ← publicParameterOf hash seed
  let root ← treeNode hash parameter topLayer seed layerHeight 0
  return (⟨root, parameter⟩, ⟨masterSeed, parameter⟩)

/-- One layer's signature by key `e` of `message`. -/
def signLayer (seed : MasterSeed) (parameter : PublicParameter) (layer : Layer) (key : KeyIndex)
    (message : HashInput) : m (Option LayerSignature) := do
  let some (randomizer, values) ← otsSign hash parameter layer key seed message | return none
  let path ← treePath hash parameter layer seed key
  return some ⟨randomizer, values, path⟩

/-- `Sign` at leaf index `idx` with the scheme seed `S` and the public parameter. -/
def signWithSchemeSeed (seed : MasterSeed) (parameter : PublicParameter) (leafIndex : LeafIndex)
    (message : Message) : m (Option Signature) := do
  let bottomKey := keyIndexOnLayer leafIndex bottomLayer
  let topKey := keyIndexOnLayer leafIndex topLayer
  let some bottom ← signLayer hash seed parameter bottomLayer bottomKey
      (littleEndianBytes 32 message) | return none
  let bottomRoot ← treeNode hash parameter bottomLayer seed layerHeight topKey.val
  let some top ← signLayer hash seed parameter topLayer topKey (littleEndianBytes 16 bottomRoot)
    | return none
  return some ⟨leafIndex, fun layer => if layer = bottomLayer then bottom else top⟩

/-- `Sign` at leaf index `idx`: derive `S` from the key's seed, then sign both layers. -/
def sign (secretKey : SecretKey) (leafIndex : LeafIndex) (message : Message) :
    m (Option Signature) := do
  let seed ← schemeSeedOf hash secretKey.keySeed
  signWithSchemeSeed hash seed secretKey.parameter leafIndex message

end Over

/-! ## The scheme -/

/-- **leanXMSS over the hash `hash`**, an `O`-computation: the statement's `sufCmaScheme` with
`keccakHash π` replaced by `hash`; the winning condition, hash-free, is the statement's. -/
noncomputable def xmssOver {ι : Type} {O : OracleSpec.{0, 0} ι}
    (hash : HashInput → OracleComp O HashOutput) :
    SchemeOver O MasterSeed PublicKey SecretKey SigningRequest (Option Signature) Forgery where
  sampleSeed := sampleMasterSeed
  generateKeys := Over.keygenFromSeed hash
  sign sk request := Over.sign hash sk request.leafIndex request.message
  verify pk forgery := Over.verify hash pk forgery.message forgery.signature
  winningCondition := LeanXmss.RandomPermutationModel.sufCmaScheme.winningCondition

/-! ## Fidelity -/

section Fidelity

open LeanVM.Semantics (KeccakState)

variable {m : Type → Type} [Monad m] (π : KeccakState → m KeccakState)

theorem th_keccakHash (parameter : PublicParameter) (fields : TweakFields)
    (payload : HashInput) :
    Over.th (keccakHash π) parameter fields payload = th π parameter fields payload :=
  rfl

theorem chainWalk_keccakHash (parameter : PublicParameter) (layer : Layer) (key : KeyIndex)
    (chainIndex : ChainIndex) :
    Over.chainWalk (keccakHash π) parameter layer key chainIndex =
      Verification.chainWalk π parameter layer key chainIndex :=
  rfl

theorem otsLeaf_keccakHash (parameter : PublicParameter) (layer : Layer) (key : KeyIndex)
    (message : HashInput) (randomizer : Randomizer) (values : ChainIndex → Digest) :
    Over.otsLeaf (keccakHash π) parameter layer key message randomizer values =
      Verification.otsLeaf π parameter layer key message randomizer values :=
  rfl

theorem treeFold_keccakHash (parameter : PublicParameter) (layer : Layer) (key : KeyIndex)
    (path : Fin layerHeight → Digest) :
    Over.treeFold (keccakHash π) parameter layer key path =
      Verification.treeFold π parameter layer key path :=
  rfl

theorem verify_keccakHash (publicKey : PublicKey) (message : Message) (signature : Signature) :
    Over.verify (keccakHash π) publicKey message signature =
      Verification.verify π publicKey message signature :=
  rfl

theorem otsSecrets_keccakHash (parameter : PublicParameter) (layer : Layer) (key : KeyIndex)
    (seed : MasterSeed) :
    Over.otsSecrets (keccakHash π) parameter layer key seed =
      KeyGenerationAndSigning.otsSecrets π parameter layer key seed :=
  rfl

theorem messageDigest_keccakHash (parameter : PublicParameter) (layer : Layer) (key : KeyIndex)
    (message : HashInput) (randomizer : Randomizer) :
    Over.messageDigest (keccakHash π) parameter layer key message randomizer =
      Verification.messageDigest π parameter layer key message randomizer :=
  rfl

theorem otsSignFrom_keccakHash (parameter : PublicParameter) (layer : Layer) (key : KeyIndex)
    (seed : MasterSeed) (message : HashInput) (randomizerBase : Randomizer) :
    ∀ attempts trial : Nat,
    Over.otsSignFrom (keccakHash π) parameter layer key seed message randomizerBase attempts
        trial =
      KeyGenerationAndSigning.otsSignFrom π parameter layer key seed message randomizerBase
        attempts trial
  | 0, _ => rfl
  | attempts + 1, trial => by
    simp only [Over.otsSignFrom, KeyGenerationAndSigning.otsSignFrom, messageDigest_keccakHash,
      otsSecrets_keccakHash, chainWalk_keccakHash,
      otsSignFrom_keccakHash parameter layer key seed message randomizerBase attempts (trial + 1)]
    rfl

theorem otsSign_keccakHash (parameter : PublicParameter) (layer : Layer) (key : KeyIndex)
    (seed : MasterSeed) (message : HashInput) :
    Over.otsSign (keccakHash π) parameter layer key seed message =
      KeyGenerationAndSigning.otsSign π parameter layer key seed message := by
  simp only [Over.otsSign, KeyGenerationAndSigning.otsSign, th_keccakHash, otsSignFrom_keccakHash]

theorem treeNode_keccakHash (parameter : PublicParameter) (layer : Layer) (seed : MasterSeed) :
    Over.treeNode (keccakHash π) parameter layer seed =
      KeyGenerationAndSigning.treeNode π parameter layer seed :=
  rfl

theorem keygenFromSeed_keccakHash (masterSeed : MasterSeed) :
    Over.keygenFromSeed (keccakHash π) masterSeed =
      KeyGenerationAndSigning.keygenFromSeed π masterSeed := by
  simp only [Over.keygenFromSeed, KeyGenerationAndSigning.keygenFromSeed, Over.schemeSeedOf,
    schemeSeedOf, Over.publicParameterOf, KeyGenerationAndSigning.publicParameterOf,
    th_keccakHash, treeNode_keccakHash]

theorem signLayer_keccakHash (seed : MasterSeed) (parameter : PublicParameter) (layer : Layer)
    (key : KeyIndex) (message : HashInput) :
    Over.signLayer (keccakHash π) seed parameter layer key message =
      KeyGenerationAndSigning.signLayer π seed parameter layer key message := by
  simp only [Over.signLayer, KeyGenerationAndSigning.signLayer, otsSign_keccakHash,
    Over.treePath, KeyGenerationAndSigning.treePath, treeNode_keccakHash]
  rfl

theorem sign_keccakHash (secretKey : SecretKey) (leafIndex : LeafIndex) (message : Message) :
    Over.sign (keccakHash π) secretKey leafIndex message =
      KeyGenerationAndSigning.sign π secretKey leafIndex message := by
  simp only [Over.sign, KeyGenerationAndSigning.sign, Over.schemeSeedOf, schemeSeedOf,
    Over.signWithSchemeSeed, KeyGenerationAndSigning.signWithSchemeSeed, signLayer_keccakHash,
    treeNode_keccakHash]
  rfl

end Fidelity

/-- **Fidelity**: over Keccak-256 with the statement's permutation oracle, the copy is the
statement's scheme. -/
theorem xmssOver_keccakHash :
    (xmssOver (keccakHash Common.queryPermutation)).toScheme =
      LeanXmss.RandomPermutationModel.sufCmaScheme := by
  have hk : Over.keygenFromSeed (keccakHash Common.queryPermutation) =
      KeyGenerationAndSigning.keygenFromSeed Common.queryPermutation :=
    funext (keygenFromSeed_keccakHash _)
  simp only [xmssOver, SchemeOver.toScheme, hk, sign_keccakHash, verify_keccakHash]
  rfl

/-- **leanXMSS in the random-oracle model**: every hash one query of `H`. -/
noncomputable def xmssRom :
    SchemeOver RomOracles MasterSeed PublicKey SecretKey SigningRequest (Option Signature)
      Forgery :=
  xmssOver hashQ

/-! ## The hashed inputs are short -/

section Lengths

theorem length_flatMap_const {α : Type} {f : α → List UInt8} {k : ℕ}
    (hf : ∀ a, (f a).length = k) (l : List α) : (l.flatMap f).length = k * l.length := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.flatMap_cons, List.length_append, ih, hf, List.length_cons]
    ring

theorem length_thInput_eq (parameter : PublicParameter) (fields : TweakFields)
    (payload : HashInput) : (thInput parameter fields payload).length = 32 + payload.length := by
  simp only [thInput, hasherInput, addressBytes, littleEndianBytes, List.length_append,
    List.length_ofFn]

/-- A tweakable-hash input with a payload of at most `maxLen - 32` bytes is short. -/
theorem length_thInput_le {parameter : PublicParameter} {fields : TweakFields}
    {payload : HashInput} (h : payload.length ≤ maxLen - 32) :
    (thInput parameter fields payload).length ≤ maxLen := by
  rw [length_thInput_eq]
  simp only [maxLen] at h ⊢
  omega

/-- A chain step's input: 64 bytes. -/
theorem length_thInput_chain (parameter : PublicParameter) (fields : TweakFields)
    (chainIndex : ChainIndex) (value : Digest) :
    (thInput parameter fields (Verification.chainPayload chainIndex value)).length ≤ maxLen :=
  length_thInput_le (by norm_num [Verification.chainPayload, littleEndianBytes, maxLen])

theorem length_digestsPayload {n : ℕ} (digests : Fin n → Digest) :
    (digestsPayload digests).length = 16 * n :=
  (length_flatMap_const (f := littleEndianBytes 16) (k := 16) (fun _ ↦ List.length_ofFn)
    (List.ofFn digests)).trans (congrArg (16 * ·) List.length_ofFn)

/-- A leaf's input: 960 bytes. -/
theorem length_thInput_leaf (parameter : PublicParameter) (fields : TweakFields)
    (endpoints : ChainIndex → Digest) :
    (thInput parameter fields (digestsPayload endpoints)).length ≤ maxLen :=
  length_thInput_le (by rw [length_digestsPayload]; norm_num [chainCount, maxLen])

/-- A tree node's input: 64 bytes. -/
theorem length_thInput_node (parameter : PublicParameter) (fields : TweakFields)
    (left right : Digest) :
    (thInput parameter fields (nodePayload left right)).length ≤ maxLen :=
  length_thInput_le (by norm_num [nodePayload, littleEndianBytes, maxLen])

/-- A message digest's input, for a message of at most `maxLen - 64` bytes. -/
theorem length_thInput_message (parameter : PublicParameter) (fields : TweakFields)
    {message : HashInput} (hm : message.length ≤ maxLen - 64) (randomizer : Randomizer) :
    (thInput parameter fields (message ++ littleEndianBytes 16 randomizer)).length ≤ maxLen :=
  length_thInput_le (by
    simp only [maxLen, List.length_append, littleEndianBytes, List.length_ofFn] at hm ⊢
    omega)

/-- A seed derivation's input (chain starts, the public parameter): 64 bytes. -/
theorem length_thInput_seed (parameter : PublicParameter) (fields : TweakFields)
    (seed : MasterSeed) : (thInput parameter fields (littleEndianBytes 32 seed)).length ≤ maxLen :=
  length_thInput_le (by norm_num [littleEndianBytes, maxLen])

/-- A randomizer base's input, for a message of at most `maxLen - 64` bytes. -/
theorem length_thInput_randomizer (parameter : PublicParameter) (fields : TweakFields)
    (seed : MasterSeed) {message : HashInput} (hm : message.length ≤ maxLen - 64) :
    (thInput parameter fields (littleEndianBytes 32 seed ++ message)).length ≤ maxLen :=
  length_thInput_le (by
    simp only [maxLen, List.length_append, littleEndianBytes, List.length_ofFn] at hm ⊢
    omega)

/-- The scheme seed's input: 40 bytes. -/
theorem length_seedInput (masterSeed : MasterSeed) :
    (seedTag ++ littleEndianBytes 32 masterSeed).length ≤ maxLen := by
  norm_num [seedTag, littleEndianBytes, maxLen]

/-- A digest's bytes are a short message. -/
theorem length_digestBytes_le (d : Digest) : (littleEndianBytes 16 d).length ≤ maxLen - 64 := by
  norm_num [littleEndianBytes, maxLen]

/-- A message's bytes are a short message. -/
theorem length_messageBytes_le (message : Message) :
    (littleEndianBytes 32 message).length ≤ maxLen - 64 := by
  norm_num [littleEndianBytes, maxLen]

end Lengths

/-! ## Hashes agreeing on short inputs give the same scheme -/

namespace Over

variable {m : Type → Type} [Monad m]

theorem foldPath_congr {node node' : Nat → Nat → HashInput → m Digest}
    (hn : ∀ level nodeIndex left right, node level nodeIndex (nodePayload left right) =
      node' level nodeIndex (nodePayload left right))
    (leafIndex : Nat) (siblingAtLevel : Nat → Digest) : ∀ (levels : Nat) (value : Digest),
    foldPath node leafIndex siblingAtLevel levels value =
      foldPath node' leafIndex siblingAtLevel levels value
  | 0, _ => rfl
  | levels + 1, value => by
    simp only [foldPath, foldPath_congr hn leafIndex siblingAtLevel levels value]
    congr 1
    funext current
    split <;> exact hn _ _ _ _

theorem buildTree_congr {leaf leaf' : Nat → m Digest}
    {node node' : Nat → Nat → HashInput → m Digest} (hl : ∀ index, leaf index = leaf' index)
    (hn : ∀ level nodeIndex left right, node level nodeIndex (nodePayload left right) =
      node' level nodeIndex (nodePayload left right)) :
    ∀ level index : Nat, buildTree leaf node level index = buildTree leaf' node' level index
  | 0, index => hl index
  | level + 1, index => by
    simp only [buildTree, buildTree_congr hl hn level, hn]

variable {hash hash' : HashInput → m HashOutput}
  (h : ∀ l : HashInput, l.length ≤ maxLen → hash l = hash' l)

include h

theorem th_congr (parameter : PublicParameter) (fields : TweakFields) {payload : HashInput}
    (hl : (thInput parameter fields payload).length ≤ maxLen) :
    th hash parameter fields payload = th hash' parameter fields payload := by
  rw [th, th, h _ hl]

theorem chainWalk_congr (parameter : PublicParameter) (layer : Layer) (key : KeyIndex)
    (chainIndex : ChainIndex) (start steps : Nat) (value : Digest) :
    chainWalk hash parameter layer key chainIndex start steps value =
      chainWalk hash' parameter layer key chainIndex start steps value := by
  have hs : (fun (step : ChainStep) value ↦ tweakableHash hash parameter (.chain layer key step)
        (Verification.chainPayload chainIndex value)) =
      fun step value ↦ tweakableHash hash' parameter (.chain layer key step)
        (Verification.chainPayload chainIndex value) :=
    funext fun _ ↦ funext fun _ ↦ th_congr h _ _ (length_thInput_chain _ _ _ _)
  rw [chainWalk, chainWalk, hs]

theorem recoverChain_congr (parameter : PublicParameter) (layer : Layer) (key : KeyIndex)
    (chainIndex : ChainIndex) (digit : WinternitzDigit) (value : Digest) :
    recoverChain hash parameter layer key chainIndex digit value =
      recoverChain hash' parameter layer key chainIndex digit value := by
  rw [recoverChain, recoverChain, chainWalk_congr h]

theorem leafHash_congr (parameter : PublicParameter) (layer : Layer) (key : KeyIndex)
    (endpoints : ChainIndex → Digest) :
    leafHash hash parameter layer key endpoints = leafHash hash' parameter layer key endpoints :=
  th_congr h _ _ (length_thInput_leaf _ _ _)

theorem messageDigest_congr (parameter : PublicParameter) (layer : Layer) (key : KeyIndex)
    {message : HashInput} (hm : message.length ≤ maxLen - 64) (randomizer : Randomizer) :
    messageDigest hash parameter layer key message randomizer =
      messageDigest hash' parameter layer key message randomizer :=
  th_congr h _ _ (length_thInput_message _ _ hm _)

theorem otsLeaf_congr (parameter : PublicParameter) (layer : Layer) (key : KeyIndex)
    {message : HashInput} (hm : message.length ≤ maxLen - 64) (randomizer : Randomizer)
    (values : ChainIndex → Digest) :
    otsLeaf hash parameter layer key message randomizer values =
      otsLeaf hash' parameter layer key message randomizer values := by
  simp only [otsLeaf, messageDigest_congr h _ _ _ hm, recoverChain_congr h, leafHash_congr h]

theorem treeFold_congr (parameter : PublicParameter) (layer : Layer) (key : KeyIndex)
    (path : Fin layerHeight → Digest) (levels : Nat) (value : Digest) :
    treeFold hash parameter layer key path levels value =
      treeFold hash' parameter layer key path levels value := by
  unfold treeFold
  exact foldPath_congr (fun _ _ _ _ ↦ th_congr h _ _ (length_thInput_node _ _ _ _)) _ _ _ _

theorem layerRoot_congr (parameter : PublicParameter) (layer : Layer) (key : KeyIndex)
    {message : HashInput} (hm : message.length ≤ maxLen - 64)
    (layerSignature : LayerSignature) :
    layerRoot hash parameter layer key message layerSignature =
      layerRoot hash' parameter layer key message layerSignature := by
  simp only [layerRoot, otsLeaf_congr h _ _ _ hm, treeFold_congr h]

theorem verify_congr (publicKey : PublicKey) (message : Message) (signature : Signature) :
    verify hash publicKey message signature = verify hash' publicKey message signature := by
  simp (disch := first | exact length_digestBytes_le _ | exact length_messageBytes_le _) only
    [verify, layerRoot_congr h]

theorem otsSecrets_congr (parameter : PublicParameter) (layer : Layer) (key : KeyIndex)
    (seed : MasterSeed) :
    otsSecrets hash parameter layer key seed = otsSecrets hash' parameter layer key seed := by
  have hs : ∀ t : ChainPairIndex,
      thPair hash parameter (keygenDomainFields (.oneTimeChainPair layer key t))
        (littleEndianBytes 32 seed) =
      thPair hash' parameter (keygenDomainFields (.oneTimeChainPair layer key t))
        (littleEndianBytes 32 seed) :=
    fun _ ↦ h _ (length_thInput_seed _ _ _)
  simp only [otsSecrets, hs]

theorem oneTimePublicKey_congr (parameter : PublicParameter) (layer : Layer) (key : KeyIndex)
    (seed : MasterSeed) :
    oneTimePublicKey hash parameter layer key seed =
      oneTimePublicKey hash' parameter layer key seed := by
  simp only [oneTimePublicKey, otsSecrets_congr h, chainWalk_congr h]

theorem otsSignFrom_congr (parameter : PublicParameter) (layer : Layer) (key : KeyIndex)
    (seed : MasterSeed) {message : HashInput} (hm : message.length ≤ maxLen - 64)
    (randomizerBase : Randomizer) : ∀ attempts trial : Nat,
    otsSignFrom hash parameter layer key seed message randomizerBase attempts trial =
      otsSignFrom hash' parameter layer key seed message randomizerBase attempts trial
  | 0, _ => rfl
  | attempts + 1, trial => by
    simp only [otsSignFrom, messageDigest_congr h _ _ _ hm, otsSecrets_congr h,
      chainWalk_congr h, otsSignFrom_congr parameter layer key seed hm randomizerBase attempts
        (trial + 1)]

theorem otsSign_congr (parameter : PublicParameter) (layer : Layer) (key : KeyIndex)
    (seed : MasterSeed) {message : HashInput} (hm : message.length ≤ maxLen - 64) :
    otsSign hash parameter layer key seed message =
      otsSign hash' parameter layer key seed message := by
  simp only [otsSign, th_congr h parameter (tweakFields 7 0 (layerHi layer 0) key)
    (length_thInput_randomizer parameter _ seed hm), otsSignFrom_congr h _ _ _ _ hm]

theorem treeNode_congr (parameter : PublicParameter) (layer : Layer) (seed : MasterSeed)
    (level nodeIndex : Nat) :
    treeNode hash parameter layer seed level nodeIndex =
      treeNode hash' parameter layer seed level nodeIndex := by
  unfold treeNode
  exact buildTree_congr (fun _ ↦ by simp only [leafHash_congr h, oneTimePublicKey_congr h])
    (fun _ _ _ _ ↦ th_congr h _ _ (length_thInput_node _ _ _ _)) _ _

theorem treePath_congr (parameter : PublicParameter) (layer : Layer) (seed : MasterSeed)
    (key : KeyIndex) :
    treePath hash parameter layer seed key = treePath hash' parameter layer seed key := by
  simp only [treePath, treeNode_congr h]

theorem keygenFromSeed_congr (masterSeed : MasterSeed) :
    keygenFromSeed hash masterSeed = keygenFromSeed hash' masterSeed := by
  have hp : ∀ seed : MasterSeed, publicParameterOf hash seed = publicParameterOf hash' seed :=
    fun _ ↦ th_congr h _ _ (length_thInput_seed _ _ _)
  simp only [keygenFromSeed, schemeSeedOf, h _ (length_seedInput masterSeed), hp,
    treeNode_congr h]

theorem signLayer_congr (seed : MasterSeed) (parameter : PublicParameter) (layer : Layer)
    (key : KeyIndex) {message : HashInput} (hm : message.length ≤ maxLen - 64) :
    signLayer hash seed parameter layer key message =
      signLayer hash' seed parameter layer key message := by
  simp only [signLayer, otsSign_congr h _ _ _ _ hm, treePath_congr h]

theorem sign_congr (secretKey : SecretKey) (leafIndex : LeafIndex) (message : Message) :
    sign hash secretKey leafIndex message = sign hash' secretKey leafIndex message := by
  simp (disch := first | exact length_digestBytes_le _ | exact length_messageBytes_le _) only
    [sign, schemeSeedOf,
    h _ (length_seedInput secretKey.keySeed), signWithSchemeSeed, signLayer_congr h,
    treeNode_congr h]

end Over

/-- **Every input leanXMSS hashes has at most `maxLen` bytes** (key generation, signing, and the
verification of any forgery; per call site `length_thInput_chain`, `length_thInput_leaf`,
`length_thInput_node`, `length_thInput_message`, `length_thInput_seed`,
`length_thInput_randomizer`, `length_seedInput`): two hashes that agree on such inputs give the
same scheme. -/
theorem xmss_hashInputs_le_maxLen {ι : Type} {O : OracleSpec.{0, 0} ι}
    {hash hash' : HashInput → OracleComp O HashOutput}
    (h : ∀ l : HashInput, l.length ≤ maxLen → hash l = hash' l) :
    xmssOver hash = xmssOver hash' := by
  have hk : Over.keygenFromSeed hash = Over.keygenFromSeed hash' :=
    funext (Over.keygenFromSeed_congr h)
  simp only [xmssOver, hk, Over.sign_congr h, Over.verify_congr h]

end Quantum.Qrom.Xmss

end
